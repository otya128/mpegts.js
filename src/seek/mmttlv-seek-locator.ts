/*
 * Copyright (C) 2024 otya. All Rights Reserved.
 *
 * @author otya <otya281@gmail.com>
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

import { MMTTLVReader } from 'arib-mmt-tlv-ts';
import { MMT_ASSET_TYPE_HEV1, MMT_ASSET_TYPE_MP4A } from 'arib-mmt-tlv-ts/dist/mmt-si.js';
import { MPUExtendedTimestamp, MPUExtendedTimestampDescriptor, MPUTimestamp, MPUTimestampDescriptor } from 'arib-mmt-tlv-ts/dist/mmt-si-descriptor.js';
import IOController from '../io/io-controller.js';
import { SeekLocator } from './seek-locator';
import Log from '../utils/logger.js';
import mpegts from '../../d.ts/mpegts.js';

type SeekInformation = {
    first_timestamp: number;
    last_timestamp: number;
    estimated_bitrate: number;
    content_length: number;
};

type ProbeFirstTimestampResult = {
    video_timestamp?: number,
    audio_timestamp?: number,
    contentLength?: number
};

class MMTTLVSeekLocator implements SeekLocator {

    private readonly TAG: string = 'MMTTLVSeekLocator';

    private config_: mpegts.Config;

    private seek_info: Promise<SeekInformation | undefined>;

    private mediaDataSource_: mpegts.MediaDataSource;
    private duration_probe_size = 4 * 1024 * 1024;
    private duration_probe_size_limit = 32 * 1024 * 1024;
    private max_seek_error_seconds = 10;
    private rap_cache = new Map<number, ProbeFirstTimestampResult>();

    public constructor(mediaDataSource: mpegts.MediaDataSource, config: mpegts.Config, durationCallback: (d: number) => void) {
        this.mediaDataSource_ = mediaDataSource;
        this.config_ = config;
        this.seek_info = this.probeSeekInfo(durationCallback);
    }

    async probeSeekInfo(durationCallback: (d: number) => void): Promise<SeekInformation | undefined> {
        const { video_timestamp, audio_timestamp, contentLength } = await this.probeFirstTimestamp(0, this.duration_probe_size_limit);
        if (video_timestamp == null || audio_timestamp == null || contentLength == null) {
            Log.e(this.TAG, 'probeSeekInfo: probeFirstTimestamp failed');
            return undefined;
        }
        Log.v(this.TAG, `probeSeekInfo: video_timestamp=${video_timestamp} audio_timestamp=${audio_timestamp}`);
        const first_timestamp = Math.min(video_timestamp, audio_timestamp);
        let last_timestamp: number | undefined;
        let probe_size: number = this.duration_probe_size;
        while (last_timestamp == null) {
            const start = Math.max(contentLength - probe_size, 0);
            last_timestamp = await this.probeLastTimestamp(start);
            probe_size *= 2;
            if (probe_size > this.duration_probe_size_limit || start === Math.max(contentLength - probe_size, 0)) {
                Log.e(this.TAG, 'probeSeekInfo: probeLastTimestamp failed');
                return undefined;
            }
        }
        durationCallback(last_timestamp - first_timestamp);
        return {
            first_timestamp,
            last_timestamp,
            estimated_bitrate: (contentLength * 8) / (last_timestamp - first_timestamp),
            content_length: contentLength,
        };
    }

    probeFirstTimestamp(start: number, probeSize: number, abortSignal?: AbortSignal): Promise<ProbeFirstTimestampResult> {
        const ioctl = new IOController(this.mediaDataSource_, this.config_);
        const reader = new MMTTLVReader();
        let mpt_packet_id: number | undefined;
        reader.addEventListener('plt', (e) => {
            mpt_packet_id = e.table.packages[0].locationInfo.packetId;
        });
        let video_packet_id: number | undefined;
        let video_rap_mpu_sequence: number | undefined;
        let video_timestamp_desc: MPUTimestampDescriptor | undefined;
        let audio_packet_id: number | undefined;
        let audio_rap_mpu_sequence: number | undefined;
        let audio_timestamp_desc: MPUTimestampDescriptor | undefined;
        const video_timestamps: Map<number, MPUTimestamp> = new Map();
        const audio_timestamps: Map<number, MPUTimestamp> = new Map();
        reader.addEventListener('mpt', (e) => {
            if (e.packetId !== mpt_packet_id) {
                return;
            }
            for (const asset of e.table.assets) {
                const packet_id = asset.locations[0]?.packetId;
                if (video_packet_id == null) {
                    if (asset.assetType === MMT_ASSET_TYPE_HEV1) {
                        video_packet_id = packet_id;
                    }
                }
                if (audio_packet_id == null) {
                    if (asset.assetType === MMT_ASSET_TYPE_MP4A) {
                        audio_packet_id = packet_id;
                    }
                }
                if (packet_id === video_packet_id) {
                    for (const desc of asset.assetDescriptors) {
                        if (desc.tag === 'mpuTimestamp') {
                            video_timestamp_desc = desc;
                            for (const ts of desc.timestamps) {
                                video_timestamps.set(ts.mpuSequenceNumber, ts);
                            }
                        }
                    }
                }
                if (packet_id === audio_packet_id) {
                    for (const desc of asset.assetDescriptors) {
                        if (desc.tag === 'mpuTimestamp') {
                            audio_timestamp_desc = desc;
                            for (const ts of desc.timestamps) {
                                audio_timestamps.set(ts.mpuSequenceNumber, ts);
                            }
                        }
                    }
                }
            }
        });
        reader.addEventListener('mpu', (e) => {
            if (e.mmtHeader.packetId === video_packet_id) {
                if (!e.mmtHeader.rapFlag) {
                    return;
                }
                if (video_rap_mpu_sequence != null) {
                    return;
                }
                video_rap_mpu_sequence = e.mpu.mpuSequenceNumber;
            }
            if (e.mmtHeader.packetId === audio_packet_id) {
                if (!e.mmtHeader.rapFlag) {
                    return;
                }
                if (audio_rap_mpu_sequence != null) {
                    return;
                }
                audio_rap_mpu_sequence = e.mpu.mpuSequenceNumber;
            }
        });
        return new Promise((resolve, reject) => {
            let bytes = 0;
            const abort = () => {
                ioctl.destroy();
                reject("aborted");
            };
            abortSignal?.addEventListener("abort", abort);
            ioctl.onDataArrival = (chunk: ArrayBuffer, _byte_start: number) => {
                reader.push(new Uint8Array(chunk));
                bytes += chunk.byteLength;
                if (video_rap_mpu_sequence != null && audio_rap_mpu_sequence != null) {
                    let min_video_mpu_seq = Infinity;
                    video_timestamps.forEach((_, k) => {
                        min_video_mpu_seq = Math.min(min_video_mpu_seq, k);
                    });
                    const video_ts = video_timestamps.get(Math.max(min_video_mpu_seq, video_rap_mpu_sequence));
                    let min_audio_mpu_seq = Infinity;
                    audio_timestamps.forEach((_, k) => {
                        min_audio_mpu_seq = Math.min(min_audio_mpu_seq, k);
                    });
                    const audio_ts = audio_timestamps.get(Math.max(min_audio_mpu_seq, audio_rap_mpu_sequence));
                    if (video_ts != null && audio_ts != null) {
                        ioctl.destroy();
                        abortSignal?.removeEventListener("abort", abort);
                        resolve({
                            video_timestamp: video_ts.mpuPresentationTime.seconds + video_ts.mpuPresentationTime.fractional * Math.pow(2, -32),
                            audio_timestamp: audio_ts.mpuPresentationTime.seconds + audio_ts.mpuPresentationTime.fractional * Math.pow(2, -32),
                            contentLength: ioctl.totalLength
                        });
                        return;
                    }
                }
                if (bytes >= probeSize) {
                    ioctl.destroy();
                    abortSignal?.removeEventListener("abort", abort);
                    resolve({ contentLength: ioctl.totalLength });
                }
            };
            ioctl.onComplete = () => {
                ioctl.destroy();
                abortSignal?.removeEventListener("abort", abort);
                resolve({ contentLength: ioctl.totalLength });
            };
            ioctl.onError = (type, data) => {
                ioctl.destroy();
                abortSignal?.removeEventListener("abort", abort);
                reject(`error ${type} ${data.msg}`);
            };
            ioctl.open(start);
        });
    }

    // TODO: probe last decodable timestamp instead of first decodable timestamp
    async probeLastTimestamp(start: number, probeSize?: number) {
        const ioctl = new IOController(this.mediaDataSource_, this.config_, 0);
        const reader = new MMTTLVReader();
        let mpt_packet_id: number | undefined;
        reader.addEventListener('plt', (e) => {
            mpt_packet_id = e.table.packages[0].locationInfo.packetId;
        });
        let video_packet_id: number | undefined;
        let rap_mpu_sequence: number | undefined;
        let video_timestamp_desc: MPUTimestampDescriptor | undefined;
        const video_timestamps: Map<number, MPUTimestamp> = new Map();
        let video_extended_timestamp_desc: MPUExtendedTimestampDescriptor | undefined;
        const video_extended_timestamps: Map<number, MPUExtendedTimestamp> = new Map();
        reader.addEventListener('mpt', (e) => {
            if (e.packetId !== mpt_packet_id) {
                return;
            }
            for (const asset of e.table.assets) {
                const packet_id = asset.locations[0]?.packetId;
                if (video_packet_id == null) {
                    if (asset.assetType === MMT_ASSET_TYPE_HEV1) {
                        video_packet_id = packet_id;
                    }
                }
                if (packet_id === video_packet_id) {
                    for (const desc of asset.assetDescriptors) {
                        if (desc.tag === 'mpuTimestamp') {
                            video_timestamp_desc = desc;
                            for (const ts of desc.timestamps) {
                                video_timestamps.set(ts.mpuSequenceNumber, ts);
                            }
                        } else if (desc.tag === 'mpuExtendedTimestamp') {
                            video_extended_timestamp_desc = desc;
                            for (const ts of desc.timestamps) {
                                video_extended_timestamps.set(ts.mpuSequenceNumber, ts);
                            }
                        }
                    }
                }
            }
        });
        reader.addEventListener('mpu', (e) => {
            if (e.mmtHeader.packetId !== video_packet_id) {
                return;
            }
            if (!e.mmtHeader.rapFlag) {
                return;
            }
            rap_mpu_sequence = e.mpu.mpuSequenceNumber;
        });
        return new Promise<number | undefined>((resolve, _reject) => {
            let bytes = 0;
            let last_pts: number | undefined;
            ioctl.onDataArrival = (chunk: ArrayBuffer, _byte_start: number) => {
                reader.push(new Uint8Array(chunk));
                bytes += chunk.byteLength;
                if (rap_mpu_sequence != null) {
                    const ts = video_timestamps.get(rap_mpu_sequence);
                    if (ts != null) {
                        last_pts = ts.mpuPresentationTime.seconds + ts.mpuPresentationTime.fractional * Math.pow(2, -32);
                        if (video_extended_timestamp_desc != null) {
                            const { defaultPTSOffset, timescale } = video_extended_timestamp_desc;
                            if (defaultPTSOffset != null && timescale != null) {
                                last_pts += defaultPTSOffset / timescale;
                            }
                        }
                    }
                }
                if (probeSize != null && bytes >= probeSize) {
                    ioctl.destroy();
                    resolve(last_pts);
                }
            };
            ioctl.onComplete = () => {
                ioctl.destroy();
                resolve(last_pts);
            };
            ioctl.onError = (type: number, data: mpegts.LoaderErrorMessage) => {
                ioctl.destroy();
                resolve(undefined);
            };
            ioctl.open(start);
        });
    }

    async estimateCBR(ts: number, info: SeekInformation, abortSignal?: AbortSignal): Promise<number | undefined> {
        const { first_timestamp, estimated_bitrate } = info;
        let estimated_position = Math.floor((estimated_bitrate * Math.max(0, (ts - 1))) / 8);
        if (abortSignal.aborted) {
            return undefined;
        }
        const cached = this.rap_cache.get(estimated_position);
        const probed = cached ?? await this.probeFirstTimestamp(estimated_position, 32 * 1024 * 1024, abortSignal);
        if (probed == null) {
            return undefined;
        }
        this.rap_cache.set(estimated_position, probed);
        const { video_timestamp, audio_timestamp } = probed;
        if (video_timestamp == null || audio_timestamp == null) {
            return undefined;
        }
        const actual_ts = Math.min(video_timestamp, audio_timestamp);
        const delta = ts - (actual_ts - first_timestamp);
        Log.v(this.TAG, `probe RAP CBR${cached ? " (cached)" : ""} offset=${estimated_position} ts=${actual_ts - info.first_timestamp} delta=${delta}`);
        if (delta >= 0 && delta < this.max_seek_error_seconds) {
            if (delta < 0.5) {
                return Math.max(0, estimated_position - Math.floor(info.estimated_bitrate / 8 / 2));
            }
            return estimated_position;
        }
        return undefined;
    }
    async estimateVBR(ts: number, info: SeekInformation, abortSignal?: AbortSignal): Promise<number | undefined> {
        let lbound = 0;
        let ubound = info.content_length - 1;
        let mid = lbound + Math.floor((ubound - lbound) / 2);

        while (lbound <= ubound) {
            if (abortSignal.aborted) {
                return undefined;
            }
            const cached = this.rap_cache.get(mid);
            const probed = cached ?? await this.probeFirstTimestamp(mid, 32 * 1024 * 1024, abortSignal);
            this.rap_cache.set(mid, probed);
            const { video_timestamp, audio_timestamp } = probed;
            if (video_timestamp == null || audio_timestamp == null) {
                return undefined;
            }
            const actual_ts = Math.max(video_timestamp, audio_timestamp);
            const delta = ts - (actual_ts - info.first_timestamp);
            Log.v(this.TAG, `probe RAP VBR${cached ? " (cached)" : ""} offset=${mid} ts=${actual_ts - info.first_timestamp} delta=${delta}`);
            if (delta >= 0 && delta < this.max_seek_error_seconds) {
                if (delta < 0.5) {
                    return Math.max(0, mid - Math.floor(info.estimated_bitrate / 8 / 2));
                }
                return mid;
            } else if (delta > 0) {
                lbound = mid + 1;
            } else {
                ubound = mid - 1;
            }
            const next = lbound + Math.floor((ubound - lbound) / 2);
            if (Math.abs(next - mid) <= 32 * 1024) {
                return Math.min(next, mid);
            }
            mid = next;
        }
        return undefined;
    }

    public async locateSeekPosition(milliseconds: number, abortSignal?: AbortSignal): Promise<number> {
        const ts = milliseconds / 1000;
        const info = await this.seek_info;
        if (info == null) {
            throw "locateSeekPosition failed.";
        }
        if (ts < this.max_seek_error_seconds) {
            return 0;
        }
        const cbr_estimated = await this.estimateCBR(ts, info, abortSignal);
        if (cbr_estimated != null) {
            return cbr_estimated;
        }
        Log.v(this.TAG, "CBR estimation failed, falling back to VBR estimation.");
        const vbr_estimated = await this.estimateVBR(ts, info, abortSignal);
        if (vbr_estimated != null) {
            throw "locateSeekPosition failed.";
        }
        return vbr_estimated;
    }
}

export default MMTTLVSeekLocator;
