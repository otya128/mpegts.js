/*
 * Copyright (C) 2021 magicxqq. All Rights Reserved.
 * Copyright (C) 2024 otya. All Rights Reserved.
 *
 * @author magicxqq <xqq@xqq.im>
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

import Log from '../utils/logger';
import MediaInfo from '../core/media-info';
import {IllegalStateException} from '../utils/exception';
import BaseDemuxer, { AudioTrack } from './base-demuxer';
import { AACFrame, AudioSpecificConfig, LOASAACFrame, readAudioMuxElement } from './aac';
import { MPEG4AudioObjectTypes, MPEG4SamplingFrequencyIndex } from './mpeg4-audio';
import { H265NaluHVC1, H265NaluType, HEVCDecoderConfigurationRecord } from './h265';
import H265Parser from './h265-parser';
import { MMTTLVReader } from 'arib-mmt-tlv-ts/dist/index.js';
import { MMTP_FRAGMENTATION_INDICATOR_COMPLETE, MMTP_FRAGMENTATION_INDICATOR_HEAD, MMTP_FRAGMENTATION_INDICATOR_MIDDLE, MMTP_FRAGMENTATION_INDICATOR_TAIL } from 'arib-mmt-tlv-ts/dist/mmtp.js';
import { MMTSIEvent, MediaProcessingUnitEvent, NTPEvent } from 'arib-mmt-tlv-ts/dist/event.js';
import { concatBuffers } from 'arib-mmt-tlv-ts/dist/utils.js';
import { MMTPackageTable, MMT_ASSET_TYPE_HEV1, MMT_ASSET_TYPE_MP4A, PackageListTable } from 'arib-mmt-tlv-ts/dist/mmt-si.js';
import { MH_AUDIO_COMPONENT_STREAM_CONTENT_MPEG4_AAC, MH_AUDIO_COMPONENT_TYPE_22POINT2, MH_AUDIO_COMPONENT_TYPE_5POINT1, MH_AUDIO_COMPONENT_TYPE_7POINT1, MH_AUDIO_COMPONENT_TYPE_COMMENTARY_FOR_VISUALLY_IMPAIRED, MH_AUDIO_COMPONENT_TYPE_FOR_HEARING_IMPAIRED, MH_AUDIO_COMPONENT_TYPE_MASK_HANDICAPPED, MH_AUDIO_COMPONENT_TYPE_MASK_SOUND_MODE, MH_AUDIO_COMPONENT_TYPE_STEREO, MPUExtendedTimestamp, MPUExtendedTimestampDescriptor, MPUTimestamp, MPUTimestampDescriptor, SAMPLING_RATE_48000, STREAM_TYPE_LATM_LOAS } from 'arib-mmt-tlv-ts/dist/mmt-si-descriptor.js';
import { MMTHeader } from 'arib-mmt-tlv-ts/dist/mmt-header.js';
import { MediaProcessingUnit } from 'arib-mmt-tlv-ts/dist/mpu.js';
import { ntp64TimestampToSeconds } from 'arib-mmt-tlv-ts/dist/ntp.js';

type AACAudioMetadata = {
    codec: 'aac',
    audio_object_type: MPEG4AudioObjectTypes;
    sampling_freq_index: MPEG4SamplingFrequencyIndex;
    sampling_frequency: number;
    channel_config: number;
};

type AudioData = {
    codec: 'aac';
    data: AACFrame;
};

class MMTTLVDemuxer extends BaseDemuxer {

    private readonly TAG: string = 'MMTTLVDemuxer';

    private config_: any;

    private media_info_ = new MediaInfo();

    private duration_ = 0;

    private video_metadata_: {
        vps: H265NaluHVC1 | undefined,
        sps: H265NaluHVC1 | undefined,
        pps: H265NaluHVC1 | undefined,
        details: any
    } = {
        vps: undefined,
        sps: undefined,
        pps: undefined,
        details: undefined
    };

    private audio_metadata_: AACAudioMetadata = {
        codec: undefined,
        audio_object_type: undefined,
        sampling_freq_index: undefined,
        sampling_frequency: undefined,
        channel_config: undefined
    };

    private has_video_ = false;
    private has_audio_ = false;
    private video_init_segment_dispatched_ = false;
    private audio_init_segment_dispatched_ = false;
    private video_metadata_changed_ = false;
    private loas_previous_frame: LOASAACFrame | null = null;

    private video_track_ = {type: 'video', id: 1, sequenceNumber: 0, samples: [], length: 0};
    private audio_track_ = {type: 'audio', id: 2, sequenceNumber: 0, samples: [], length: 0};

    private reader_ = new MMTTLVReader();

    private mpt_packet_id_?: number;

    private video_packet_id_?: number;
    private video_timestamp_desc_?: MPUTimestampDescriptor;
    private video_timestamps_: Map<number, MPUTimestamp> = new Map();
    private video_extended_timestamp_desc_?: MPUExtendedTimestampDescriptor;
    private video_extended_timestamps_: Map<number, MPUExtendedTimestamp> = new Map();

    private audio_packet_id_?: number;
    // { PID: MPUTimestampDescriptor }
    private audio_timestamp_desc_: Map<number, MPUTimestampDescriptor> = new Map();
    // { PID: { mpu_sequence_number: MPUTimestamp } }
    private audio_timestamps_: Map<number, Map<number, MPUTimestamp>> = new Map();
    // { PID: MPUExtendedTimestampDescriptor }
    private audio_extended_timestamp_desc_: Map<number, MPUExtendedTimestampDescriptor> = new Map();
    // { PID: { mpu_sequence_number: MPUExtendedTimestamp } }
    private audio_extended_timestamps_: Map<number, Map<number, MPUExtendedTimestamp>> = new Map();

    private video_mfu_queue_: Uint8Array[] = [];
    private video_access_unit_index_ = 0;
    private video_mpu_sequence_number_ = 0;
    private video_units_: {type: H265NaluType, data: Uint8Array}[] = [];

    private audio_mfu_queue_: Uint8Array[] = [];
    private audio_access_unit_index_ = 0;
    private audio_mpu_sequence_number_ = 0;
    private selected_audio_component_tag_ = 0;

    private system_clock_?: number;
    private system_clock_offset_?: number;
    private find_video_rap_ = true;
    private find_audio_rap_ = true;
    private eventVersion = -1;
    private mpt_version_ = -1;
    public constructor(config: any) {
        super();

        this.reader_.addEventListener('plt', (e) => this.onPLT(e));
        this.reader_.addEventListener('mpt', (e) => this.onMPT(e));
        this.reader_.addEventListener('mpu', (e) => this.onMPU(e));
        this.reader_.addEventListener('ntp', (e) => this.onNTP(e));
        // for debug
        this.reader_.addEventListener('eit', (e) => {
            if (e.table.tableId === 'EIT[p/f]') {
                if (e.table.sectionNumber === 0 && e.table.currentNextIndicator) {
                    if (e.table.versionNumber === this.eventVersion) {
                        return;
                    }
                    this.eventVersion = e.table.versionNumber;
                    const event = e.table.events[0];
                    for (const desc of event.descriptors) {
                        if (desc.tag === 'mhShortEvent') {
                            Log.v(this.TAG, `event: ${new TextDecoder().decode(desc.eventName)} ${new TextDecoder().decode(desc.text)}`);
                        }
                    }
                }
            }
        })
        this.config_ = config;
    }

    public destroy() {
        this.media_info_ = null;

        this.video_metadata_ = null;
        this.audio_metadata_ = null;

        this.video_track_ = null;
        this.audio_track_ = null;

        super.destroy();
    }

    public bindDataSource(loader) {
        loader.onDataArrival = this.parseChunks.bind(this);
        return this;
    }

    public resetMediaInfo() {
        this.media_info_ = new MediaInfo();
    }

    public parseChunks(chunk: ArrayBuffer, byte_start: number): number {
        if (!this.onError
                || !this.onMediaInfo
                || !this.onTrackMetadata
                || !this.onDataAvailable) {
            throw new IllegalStateException('onError & onMediaInfo & onTrackMetadata & onDataAvailable callback must be specified');
        }

        const now = performance.now() + performance.timeOrigin;
        const prev_stc = this.system_clock_;
        const prev_stc_offset = this.system_clock_offset_;
        this.reader_.push(new Uint8Array(chunk));

        // dispatch parsed frames to the remuxer (consumer)
        this.dispatchAudioVideoMediaSegment();
        if (this.onSystemClock != null && this.system_clock_ != null && prev_stc !== this.system_clock_) {
            let stc_offset = 0;
            if (prev_stc != null && prev_stc_offset != null && this.system_clock_offset_ != null) {
                const stc_delta = this.system_clock_ - prev_stc;
                const offset_delta = this.system_clock_offset_ - prev_stc_offset;
                if (stc_delta > 0 && offset_delta > 0) {
                    const rate = offset_delta / stc_delta;
                    stc_offset = (this.reader_.bytes - this.system_clock_offset_) / rate;
                }
            }
            this.onSystemClock(this.system_clock_ + stc_offset, now);
        }

        return chunk.byteLength;  // consumed bytes
    }

    private onPLT({ table }: MMTSIEvent<PackageListTable>) {
        const pkg = table.packages[0];
        if (pkg == null) {
            return;
        }
        this.mpt_packet_id_ = pkg.locationInfo.packetId;
    }

    private resetVideo() {
        this.find_video_rap_ = true;
        this.video_mfu_queue_ = [];
        this.video_units_ = [];
    }

    private resetAudio() {
        this.find_audio_rap_ = true;
        this.audio_mfu_queue_ = [];
    }

    private onMPT({ packetId: mpt_packet_id, table }: MMTSIEvent<MMTPackageTable>) {
        if (this.mpt_packet_id_ !== mpt_packet_id) {
            return;
        }
        const mpt_changed = this.mpt_version_ !== table.version;
        this.mpt_version_ = table.version;
        let audio_detected = false, video_detected = false;
        let audio_track_index = 0;
        let main_audio_packet_id = -1;
        let selected_audio_packet_id = -1;
        const selectable_audios = new Set<number>();
        for (const asset of table.assets) {
            const packet_id = asset.locations[0]?.packetId;
            if (asset.assetType === MMT_ASSET_TYPE_MP4A) {
                let selectable = true;
                for (const desc of asset.assetDescriptors) {
                    if (desc.tag === 'mhAudioComponent') {
                        if (desc.streamContent !== MH_AUDIO_COMPONENT_STREAM_CONTENT_MPEG4_AAC) {
                            selectable = false;
                        } else if (desc.streamType !== STREAM_TYPE_LATM_LOAS) {
                            selectable = false;
                        }
                        if (desc.mainComponentFlag) {
                            main_audio_packet_id = packet_id;
                        }
                        if (this.selected_audio_component_tag_ === desc.componentTag) {
                            selected_audio_packet_id = packet_id;
                        }
                    }
                }
                if (selectable) {
                    selectable_audios.add(packet_id);
                }
            }
        }
        if (selected_audio_packet_id === -1) {
            selected_audio_packet_id = main_audio_packet_id;
        }
        if (mpt_changed) {
            const audio_track_list: AudioTrack[] = [];
            for (const asset of table.assets) {
                const packet_id = asset.locations[0]?.packetId;
                if (selectable_audios.has(packet_id)) {
                    const audio_track: AudioTrack = {
                        id: String(audio_track_list.length),
                    };
                    for (const desc of asset.assetDescriptors) {
                        if (desc.tag === 'mhAudioComponent') {
                            audio_track.label = new TextDecoder().decode(desc.text);
                            if (desc.samplingRate === SAMPLING_RATE_48000) {
                                audio_track.samplingRate = 48000;
                            }
                            audio_track.main = desc.mainComponentFlag;
                            switch (desc.componentType & MH_AUDIO_COMPONENT_TYPE_MASK_SOUND_MODE) {
                                case MH_AUDIO_COMPONENT_TYPE_STEREO:
                                    audio_track.channelLayoutName = 'stereo';
                                    break;
                                case MH_AUDIO_COMPONENT_TYPE_5POINT1:
                                    audio_track.channelLayoutName = '5.1';
                                    break;
                                case MH_AUDIO_COMPONENT_TYPE_7POINT1:
                                    audio_track.channelLayoutName = '7.1';
                                    break;
                                case MH_AUDIO_COMPONENT_TYPE_22POINT2:
                                    audio_track.channelLayoutName = '22.2';
                                    break;
                            }
                            switch (desc.componentType & MH_AUDIO_COMPONENT_TYPE_MASK_HANDICAPPED) {
                                case MH_AUDIO_COMPONENT_TYPE_COMMENTARY_FOR_VISUALLY_IMPAIRED:
                                    audio_track.audioDescription = 'visually';
                                    break;
                                case MH_AUDIO_COMPONENT_TYPE_FOR_HEARING_IMPAIRED:
                                    audio_track.audioDescription = 'hearing';
                                break;
                            }
                            audio_track.language = String.fromCharCode((desc.iso639LanguageCode >> 16) & 0xff, (desc.iso639LanguageCode >> 8) & 0xff, desc.iso639LanguageCode & 0xff);
                            audio_track.groupId = desc.simulcastGroupTag.toString(16);
                            audio_track.id = desc.componentTag.toString(16);
                        }
                    }
                    audio_track_list.push(audio_track);
                }
            }
            this.onAudioTracksMetadata?.(audio_track_list);
        }
        for (const asset of table.assets) {
            const packet_id = asset.locations[0]?.packetId;
            if (!video_detected && asset.assetType === MMT_ASSET_TYPE_HEV1) {
                if (this.video_packet_id_ != null && this.video_packet_id_ !== packet_id) {
                    Log.v(this.TAG, `video packet id changed 0x${this.video_packet_id_.toString(16)} => 0x${packet_id.toString(16)}`);
                    this.resetVideo();
                }
                this.video_packet_id_ = packet_id;
                this.has_video_ = true;
                video_detected = true;
            }
            if (!audio_detected && selectable_audios.has(packet_id) && packet_id === selected_audio_packet_id) {
                if (this.audio_packet_id_ != null && this.audio_packet_id_ !== packet_id) {
                    Log.v(this.TAG, `audio packet id changed 0x${this.audio_packet_id_.toString(16)} => 0x${packet_id.toString(16)}`);
                    this.resetAudio();
                }
                this.audio_packet_id_ = packet_id;
                this.has_audio_ = true;
                audio_detected = true;
            }
            if (selectable_audios.has(packet_id)) {
                audio_track_index += 1;
                for (const desc of asset.assetDescriptors) {
                    if (desc.tag === 'mpuTimestamp') {
                        this.audio_timestamp_desc_.set(packet_id, desc);
                        const map = this.audio_timestamps_.get(packet_id) ?? new Map();
                        this.audio_timestamps_.set(packet_id, map);
                        for (const ts of desc.timestamps) {
                            map.set(ts.mpuSequenceNumber, ts);
                        }
                    } else if (desc.tag === 'mpuExtendedTimestamp') {
                        this.audio_extended_timestamp_desc_.set(packet_id, desc);
                        const map = this.audio_extended_timestamps_.get(packet_id) ?? new Map();
                        this.audio_extended_timestamps_.set(packet_id, map);
                        for (const ts of desc.timestamps) {
                            map.set(ts.mpuSequenceNumber, ts);
                        }
                    }
                }
            }
            if (video_detected && packet_id === this.video_packet_id_) {
                for (const desc of asset.assetDescriptors) {
                    if (desc.tag === 'mpuTimestamp') {
                        this.video_timestamp_desc_ = desc;
                        for (const ts of desc.timestamps) {
                            this.video_timestamps_.set(ts.mpuSequenceNumber, ts);
                        }
                    } else if (desc.tag === 'mpuExtendedTimestamp') {
                        this.video_extended_timestamp_desc_ = desc;
                        for (const ts of desc.timestamps) {
                            this.video_extended_timestamps_.set(ts.mpuSequenceNumber, ts);
                        }
                    }
                }
            }
        }
    }

    public insertDiscontinuity() {
        this.resetVideo();
        this.resetAudio();
        this.video_track_ = {type: 'video', id: 1, sequenceNumber: 0, samples: [], length: 0};
        this.audio_track_ = {type: 'audio', id: 2, sequenceNumber: 0, samples: [], length: 0};
        this.video_init_segment_dispatched_ = false;
        this.audio_init_segment_dispatched_ = false;
        this.reader_.reset();
        this.system_clock_ = undefined;
        this.system_clock_offset_ = null;
        this.mpt_version_ = -1;
    }

    private addVideoSample(mpu_sequence_number: number, access_unit_index: number) {
        const { video_timestamp_desc_: timestamp, video_extended_timestamp_desc_: extended_timestamp } = this;
        if (timestamp == null || extended_timestamp == null) {
            return;
        }
        const base_timestamp = this.video_timestamps_.get(mpu_sequence_number);
        const ext_timestamp = this.video_extended_timestamps_.get(mpu_sequence_number);
        if (base_timestamp == null || ext_timestamp == null) {
            return;
        }
        const { timescale, defaultPTSOffset } = extended_timestamp;
        if (timescale == null || defaultPTSOffset == null) {
            return;
        }
        const time_offset = Math.floor((base_timestamp.mpuPresentationTime.seconds + base_timestamp.mpuPresentationTime.fractional * Math.pow(2, -32)) * timescale);
        const dts = time_offset + access_unit_index * defaultPTSOffset;
        const pts = dts + (ext_timestamp.accessUnits[access_unit_index]?.dtsPTSOffset ?? 0);
        const dts_ms = Math.floor(dts * 1000 / timescale);
        const pts_ms = Math.floor(pts * 1000 / timescale);
        let hvc_sample = {
            units: this.video_units_,
            length: this.video_units_.reduce((c, p) => c + p.data.length, 0),
            isKeyframe: this.video_units_.some(x => x.type === H265NaluType.kSliceIDR_W_RADL || x.type === H265NaluType.kSliceIDR_N_LP || x.type === H265NaluType.kSliceCRA_NUT),
            dts: dts_ms,
            pts: pts_ms,
            cts: pts_ms - dts_ms,
        };
        this.video_units_ = [];
        this.video_track_.samples.push(hvc_sample);
        this.video_track_.length += hvc_sample.length;
    }

    private onMPU({ mmtHeader, mpu }: MediaProcessingUnitEvent) {
        if (mmtHeader.packetId === this.audio_packet_id_) {
            this.processAudioMPU(mmtHeader, mpu);
        }
        if (mmtHeader.packetId === this.video_packet_id_) {
            this.processVideoMPU(mmtHeader, mpu);
        }
    }

    private onNTP({ ntp, offset }: NTPEvent) {
        this.system_clock_ = ntp64TimestampToSeconds(ntp.transmitTimestamp);
        this.system_clock_offset_ = offset;
    }

    audio_metadata_changed?: number;

    private processAudioMPU(mmtHeader: MMTHeader, mpu: MediaProcessingUnit) {
        if (mpu.fragmentType !== 'mfu' || !mpu.timedFlag) {
            return;
        }
        if (this.audio_mpu_sequence_number_ !== mpu.mpuSequenceNumber) {
            this.audio_mfu_queue_ = [];
        }
        if (this.find_audio_rap_ && !mmtHeader.rapFlag) {
            return;
        }
        if (mmtHeader.rapFlag || this.audio_mpu_sequence_number_ !== mpu.mpuSequenceNumber) {
            this.audio_mpu_sequence_number_ = mpu.mpuSequenceNumber;
            this.audio_access_unit_index_ = 0;
        }
        this.find_audio_rap_ = false;
        if (mpu.fragmentationIndicator === MMTP_FRAGMENTATION_INDICATOR_MIDDLE && this.audio_mfu_queue_.length === 0) {
            return;
        }
        if (mpu.fragmentationIndicator === MMTP_FRAGMENTATION_INDICATOR_HEAD || mpu.fragmentationIndicator === MMTP_FRAGMENTATION_INDICATOR_COMPLETE) {
            this.audio_mfu_queue_ = [];
        }
        for (const m of mpu.mfuList) {
            this.audio_mfu_queue_.push(m.mfuData);
        }
        if (mpu.fragmentationIndicator !== MMTP_FRAGMENTATION_INDICATOR_COMPLETE && mpu.fragmentationIndicator !== MMTP_FRAGMENTATION_INDICATOR_TAIL) {
            return;
        }
        const frames = mpu.fragmentationIndicator === MMTP_FRAGMENTATION_INDICATOR_COMPLETE ? this.audio_mfu_queue_ : [concatBuffers(this.audio_mfu_queue_)];
        this.audio_mfu_queue_ = [];
        for (const frame of frames) {
            const access_unit = this.audio_access_unit_index_;
            const mpu_sequence_number = mpu.mpuSequenceNumber;
            const timestamp = this.audio_timestamp_desc_.get(mmtHeader.packetId);
            const extended_timestamp = this.audio_extended_timestamp_desc_.get(mmtHeader.packetId);
            if (timestamp == null || extended_timestamp == null) {
                return;
            }
            const base_timestamp = this.audio_timestamps_.get(mmtHeader.packetId)?.get(mpu_sequence_number);
            const ext_timestamp = this.audio_extended_timestamps_.get(mmtHeader.packetId)?.get(mpu_sequence_number);
            if (base_timestamp == null || ext_timestamp == null) {
                return;
            }
            const { timescale, defaultPTSOffset } = extended_timestamp;
            if (timescale == null || defaultPTSOffset == null) {
                return;
            }
            const time_offset = Math.floor((base_timestamp.mpuPresentationTime.seconds + base_timestamp.mpuPresentationTime.fractional * Math.pow(2, -32)) * timescale);
            const dts = time_offset + access_unit * defaultPTSOffset;
            const pts = dts + (ext_timestamp.accessUnits[access_unit]?.dtsPTSOffset ?? 0);
            const dts_ms = Math.floor(dts * 1000 / timescale);
            const pts_ms = Math.floor(pts * 1000 / timescale);
            const aac_frame = readAudioMuxElement(frame, this.loas_previous_frame);
            if (aac_frame == null) {
                this.audio_access_unit_index_ += 1;
                continue;
            }
            this.loas_previous_frame = aac_frame;
            const audio_sample = {
                codec: 'aac',
                data: aac_frame
            } as const;

            if (this.audio_init_segment_dispatched_ === false || this.detectAudioMetadataChange(audio_sample)) {
                this.audio_metadata_ = {
                    codec: 'aac',
                    audio_object_type: aac_frame.audio_object_type,
                    sampling_freq_index: aac_frame.sampling_freq_index,
                    sampling_frequency: aac_frame.sampling_frequency,
                    channel_config: aac_frame.channel_config
                };
                // flush stashed frames before notify new AudioSpecificConfig
                this.dispatchAudioMediaSegment(true);
                // notify new AAC AudioSpecificConfig
                this.dispatchAudioInitSegment(audio_sample);
            }

           const unit = aac_frame.data;
            const aac_sample = {
                unit,
                length: unit.byteLength,
                pts: pts_ms,
                dts: dts_ms
            };
            this.audio_track_.samples.push(aac_sample);
            this.audio_track_.length += unit.byteLength;
            this.audio_access_unit_index_ += 1;
        }
    }

    private processVideoMPU(mmtHeader: MMTHeader, mpu: MediaProcessingUnit) {
        if (mpu.fragmentType !== 'mfu' || !mpu.timedFlag) {
            return;
        }
        if (this.video_mpu_sequence_number_ !== mpu.mpuSequenceNumber) {
            this.video_mfu_queue_ = [];
        }
        if (this.find_video_rap_ && !mmtHeader.rapFlag) {
            return;
        }
        if (mmtHeader.rapFlag || this.video_mpu_sequence_number_ !== mpu.mpuSequenceNumber) {
            if (!this.find_video_rap_) {
                this.addVideoSample(this.video_mpu_sequence_number_, this.video_access_unit_index_);
            }
            this.video_access_unit_index_ = 0;
            this.video_mpu_sequence_number_ = mpu.mpuSequenceNumber;
        }
        this.find_video_rap_ = false;
        if (mpu.fragmentationIndicator === MMTP_FRAGMENTATION_INDICATOR_MIDDLE && this.video_mfu_queue_.length === 0) {
            return;
        }
        if (mpu.fragmentationIndicator === MMTP_FRAGMENTATION_INDICATOR_HEAD || mpu.fragmentationIndicator === MMTP_FRAGMENTATION_INDICATOR_COMPLETE) {
            this.video_mfu_queue_ = [];
        }
        for (const m of mpu.mfuList) {
            this.video_mfu_queue_.push(m.mfuData);
        }
        if (mpu.fragmentationIndicator !== MMTP_FRAGMENTATION_INDICATOR_COMPLETE && mpu.fragmentationIndicator !== MMTP_FRAGMENTATION_INDICATOR_TAIL) {
            return;
        }
        const nals = mpu.fragmentationIndicator === MMTP_FRAGMENTATION_INDICATOR_COMPLETE ? this.video_mfu_queue_ : [concatBuffers(this.video_mfu_queue_)];
        this.video_mfu_queue_ = [];
        let vps_nalu: H265NaluHVC1 | undefined;
        let vps_details: any;
        for (const nalData of nals) {
            const len = (nalData[0] << 24) | (nalData[1] << 16) | (nalData[2] << 8) | nalData[3];
            let nalu_hvc1 = new H265NaluHVC1(nalData.subarray(0, len + 4));
            const data = nalData.subarray(4);
            switch (nalu_hvc1.type) {
                case H265NaluType.kSliceVPS: {
                    let details = H265Parser.parseVPS(nalu_hvc1.data);
                    this.video_metadata_.vps = nalu_hvc1;
                    this.video_metadata_.details = {
                        ... this.video_metadata_.details,
                        ... details
                    };
                    vps_nalu = nalu_hvc1;
                    vps_details = details;
                    break;
                }
                case H265NaluType.kSliceSPS: {
                    let details = H265Parser.parseSPS(data);
                    if (!this.video_init_segment_dispatched_) {
                        this.video_metadata_.sps = nalu_hvc1;
                        this.video_metadata_.details = {
                            ... this.video_metadata_.details,
                            ... details
                        };
                    } else if (this.detectVideoMetadataChange(nalu_hvc1, details) === true) {
                        Log.v(this.TAG, `H265: Critical h265 metadata has been changed, attempt to re-generate InitSegment`);
                        this.video_metadata_changed_ = true;
                        this.video_metadata_ = { vps: vps_nalu, sps: nalu_hvc1, pps: undefined, details: { ...vps_details, ...details }};
                    }
                    break;
                }
                case H265NaluType.kSlicePPS: {
                    if (!this.video_init_segment_dispatched_ || this.video_metadata_changed_) {
                        let details = H265Parser.parsePPS(data);
                        this.video_metadata_.pps = nalu_hvc1;
                        this.video_metadata_.details = {
                            ... this.video_metadata_.details,
                            ... details
                        };
                        if (this.video_metadata_.vps && this.video_metadata_.sps && this.video_metadata_.pps) {
                            if (this.video_metadata_changed_) {
                                // flush stashed frames before changing codec metadata
                                this.dispatchVideoMediaSegment(true);
                            }
                            // notify new codec metadata (maybe changed)
                            this.dispatchVideoInitSegment();
                        }
                    }
                    break;
                }
            }
            if (!this.video_init_segment_dispatched_) {
                continue;
            }
            // parameter set
            if (nalu_hvc1.type === H265NaluType.kSliceVPS || nalu_hvc1.type === H265NaluType.kSliceSPS || nalu_hvc1.type === H265NaluType.kSlicePPS) {
                continue;
            }
            if (nalu_hvc1.type === H265NaluType.kSliceAUD && this.video_units_.length > 0) {
                this.addVideoSample(this.video_mpu_sequence_number_, this.video_access_unit_index_);
                this.video_access_unit_index_ += 1;
            }
            this.video_units_.push(nalu_hvc1);
        }
    }

    private detectVideoMetadataChange(new_sps: H265NaluHVC1, new_details: any): boolean {
        if (new_details.codec_mimetype !== this.video_metadata_.details.codec_mimetype) {
            Log.v(this.TAG, `Video: Codec mimeType changed from ` +
                            `${this.video_metadata_.details.codec_mimetype} to ${new_details.codec_mimetype}`);
            return true;
        }

        if (new_details.codec_size.width !== this.video_metadata_.details.codec_size.width
            || new_details.codec_size.height !== this.video_metadata_.details.codec_size.height) {
            let old_size = this.video_metadata_.details.codec_size;
            let new_size = new_details.codec_size;
            Log.v(this.TAG, `Video: Coded Resolution changed from ` +
                            `${old_size.width}x${old_size.height} to ${new_size.width}x${new_size.height}`);
            return true;
        }

        if (new_details.present_size.width !== this.video_metadata_.details.present_size.width) {
            Log.v(this.TAG, `Video: Present resolution width changed from ` +
                            `${this.video_metadata_.details.present_size.width} to ${new_details.present_size.width}`);
            return true;
        }

        if (new_details.colour_primaries !== this.video_metadata_.details.colour_primaries) {
            Log.v(this.TAG, `Video: Colour primaries changed from ` +
                            `${this.video_metadata_.details.colour_primaries} to ${new_details.colour_primaries}`);
            return true;
        }

        if (new_details.transfer_characteristics !== this.video_metadata_.details.transfer_characteristics) {
            Log.v(this.TAG, `Video: Transfer characteristics changed from ` +
                            `${this.video_metadata_.details.transfer_characteristics} to ${new_details.transfer_characteristics}`);
            return true;
        }

        if (new_details.matrix_coeffs !== this.video_metadata_.details.matrix_coeffs) {
            Log.v(this.TAG, `Video: Matrix coeffs changed from ` +
                            `${this.video_metadata_.details.matrix_coeffs} to ${new_details.matrix_coeffs}`);
            return true;
        }

        return false;
    }

    private isInitSegmentDispatched(): boolean {
        if (this.has_video_ && this.has_audio_) {  // both video & audio
            return this.video_init_segment_dispatched_ && this.audio_init_segment_dispatched_;
        }
        if (this.has_video_ && !this.has_audio_) {  // video only
            return this.video_init_segment_dispatched_;
        }
        if (!this.has_video_ && this.has_audio_) {  // audio only
            return this.audio_init_segment_dispatched_;
        }
        return false;
    }

    private dispatchVideoInitSegment() {
        let details = this.video_metadata_.details;
        let meta: any = {};

        meta.type = 'video';
        meta.id = this.video_track_.id;
        meta.timescale = 1000;
        meta.duration = this.duration_;

        meta.codecWidth = details.codec_size.width;
        meta.codecHeight = details.codec_size.height;
        meta.presentWidth = details.present_size.width;
        meta.presentHeight = details.present_size.height;

        meta.profile = details.profile_string;
        meta.level = details.level_string;
        meta.bitDepth = details.bit_depth;
        meta.chromaFormat = details.chroma_format;
        meta.sarRatio = details.sar_ratio;
        meta.frameRate = details.frame_rate;

        let fps_den = meta.frameRate.fps_den;
        let fps_num = meta.frameRate.fps_num;
        meta.refSampleDuration = 1000 * (fps_den / fps_num);

        meta.codec = details.codec_mimetype;

        if (this.video_metadata_.vps) {
            let vps_without_header = this.video_metadata_.vps.data.subarray(4);
            let sps_without_header = this.video_metadata_.sps.data.subarray(4);
            let pps_without_header = this.video_metadata_.pps.data.subarray(4);
            let hvcc = new HEVCDecoderConfigurationRecord(vps_without_header, sps_without_header, pps_without_header, details);
            meta.hvcc = hvcc.getData();

            if (this.video_init_segment_dispatched_ == false) {
                Log.v(this.TAG, `Generated first HEVCDecoderConfigurationRecord for mimeType: ${meta.codec}`);
            }
        }
        this.onTrackMetadata('video', meta);
        this.video_init_segment_dispatched_ = true;
        this.video_metadata_changed_ = false;

        // notify new MediaInfo
        let mi = this.media_info_;
        mi.hasVideo = true;
        mi.width = meta.codecWidth;
        mi.height = meta.codecHeight;
        mi.fps = meta.frameRate.fps;
        mi.profile = meta.profile;
        mi.level = meta.level;
        mi.refFrames = details.ref_frames;
        mi.chromaFormat = details.chroma_format_string;
        mi.sarNum = meta.sarRatio.width;
        mi.sarDen = meta.sarRatio.height;
        mi.videoCodec = meta.codec;

        if (mi.hasAudio && mi.audioCodec) {
            mi.mimeType = `video/mp2t; codecs="${mi.videoCodec},${mi.audioCodec}"`;
        } else {
            mi.mimeType = `video/mp2t; codecs="${mi.videoCodec}"`;
        }

        if (mi.isComplete()) {
            this.onMediaInfo(mi);
        }
    }

    private dispatchVideoMediaSegment(force = false) {
        if (this.isInitSegmentDispatched()) {
            if (force || this.video_track_.length) {
                this.onDataAvailable(null, this.video_track_, force);
            }
        }
    }

    private dispatchAudioMediaSegment(force = false) {
        if (this.isInitSegmentDispatched()) {
            if (force || this.audio_track_.length) {
                this.onDataAvailable(this.audio_track_, null, force);
            }
        }
    }

    private dispatchAudioVideoMediaSegment() {
        if (this.isInitSegmentDispatched()) {
            if (this.audio_track_.length || this.video_track_.length) {
                this.onDataAvailable(this.audio_track_, this.video_track_);
            }
        }
    }

    private detectAudioMetadataChange(sample: AudioData): boolean {
        if (sample.codec !== this.audio_metadata_.codec) {
            Log.v(this.TAG, `Audio: Audio Codecs changed from ` +
                                `${this.audio_metadata_.codec} to ${sample.codec}`);
            return true;
        }

        if (sample.codec === 'aac' && this.audio_metadata_.codec === 'aac') {
            const frame = sample.data;
            if (frame.audio_object_type !== this.audio_metadata_.audio_object_type) {
                Log.v(this.TAG, `AAC: AudioObjectType changed from ` +
                                `${this.audio_metadata_.audio_object_type} to ${frame.audio_object_type}`);
                return true;
            }

            if (frame.sampling_freq_index !== this.audio_metadata_.sampling_freq_index) {
                Log.v(this.TAG, `AAC: SamplingFrequencyIndex changed from ` +
                                `${this.audio_metadata_.sampling_freq_index} to ${frame.sampling_freq_index}`);
                return true;
            }

            if (frame.channel_config !== this.audio_metadata_.channel_config) {
                Log.v(this.TAG, `AAC: Channel configuration changed from ` +
                                `${this.audio_metadata_.channel_config} to ${frame.channel_config}`);
                return true;
            }
        }

        return false;
    }

    private dispatchAudioInitSegment(sample: AudioData) {
        let meta: any = {};
        meta.type = 'audio';
        meta.id = this.audio_track_.id;
        meta.timescale = 1000;
        meta.duration = this.duration_;

        if (this.audio_metadata_.codec === 'aac') {
            let aac_frame = sample.codec === 'aac' ? sample.data : null;
            let audio_specific_config = new AudioSpecificConfig(aac_frame);

            meta.audioSampleRate = audio_specific_config.sampling_rate;
            meta.channelCount = audio_specific_config.channel_count;
            meta.codec = audio_specific_config.codec_mimetype;
            meta.originalCodec = audio_specific_config.original_codec_mimetype;
            meta.config = audio_specific_config.config;
            meta.refSampleDuration = 1024 / meta.audioSampleRate * meta.timescale;
        }

        if (this.audio_init_segment_dispatched_ == false) {
            Log.v(this.TAG, `Generated first AudioSpecificConfig for mimeType: ${meta.codec}`);
        }

        this.onTrackMetadata('audio', meta);
        this.audio_init_segment_dispatched_ = true;

        // notify new MediaInfo
        let mi = this.media_info_;
        mi.hasAudio = true;
        mi.audioCodec = meta.originalCodec;
        mi.audioSampleRate = meta.audioSampleRate;
        mi.audioChannelCount = meta.channelCount;

        if (mi.hasVideo && mi.videoCodec) {
            mi.mimeType = `video/mp2t; codecs="${mi.videoCodec},${mi.audioCodec}"`;
        } else {
            mi.mimeType = `video/mp2t; codecs="${mi.audioCodec}"`;
        }

        if (mi.isComplete()) {
            this.onMediaInfo(mi);
        }
    }

    switchAudioTrack(id: string): void {
        this.selected_audio_component_tag_ = parseInt(id, 16);
    }
}

export default MMTTLVDemuxer;
