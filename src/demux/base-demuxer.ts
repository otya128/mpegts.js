import MediaInfo from '../core/media-info';
import { PESPrivateData, PESPrivateDataDescriptor } from './pes-private-data';
import { SMPTE2038Data } from './smpte2038';
import { SCTE35Data } from './scte35';
import { KLVData } from './klv';

type OnErrorCallback = (type: string, info: string) => void;
type OnMediaInfoCallback = (mediaInfo: MediaInfo) => void;
type OnMetaDataArrivedCallback = (metadata: any) => void;
type OnTrackMetadataCallback = (type: string, metadata: any) => void;
type OnDataAvailableCallback = (audioTrack: any, videoTrack: any, force?: boolean) => void;
type OnTimedID3MetadataCallback = (timed_id3_data: PESPrivateData) => void;
type OnSynchronousKLVMetadataCallback = (synchronous_klv_data: KLVData) => void;
type OnAsynchronousKLVMetadataCallback = (asynchronous_klv_data: PESPrivateData) => void;
type OnSMPTE2038MetadataCallback = (smpte2038_data: SMPTE2038Data) => void;
type OnSCTE35MetadataCallback = (scte35_data: SCTE35Data) => void;
type OnPESPrivateDataCallback = (private_data: PESPrivateData) => void;
type OnPESPrivateDataDescriptorCallback = (private_data_descriptor: PESPrivateDataDescriptor) => void;
type OnSystemClockCallback = (system_clock: number, performance_timestamp: number) => void;
export type ChannelLayoutName = 'mono' | 'dualmono' | 'stereo' | '4' | '5' | '5.1' | '7.1' | '22.2';
export type AudioTrack = {
    id: string;
    main?: boolean;
    channelLayoutName?: ChannelLayoutName;
    groupId?: string;
    samplingRate?: number;
    label?: string;
    language?: string;
    secondLanguage?: string;
    audioDescription?: 'visually' | 'hearing';
};
type OnAudioTracksMetadataCallback = (tracks: AudioTrack[]) => void;

export default abstract class BaseDemuxer {

    public onError: OnErrorCallback;
    public onMediaInfo: OnMediaInfoCallback;
    public onMetaDataArrived: OnMetaDataArrivedCallback;
    public onTrackMetadata: OnTrackMetadataCallback;
    public onDataAvailable: OnDataAvailableCallback;
    public onTimedID3Metadata: OnTimedID3MetadataCallback;
    public onSynchronousKLVMetadata: OnSynchronousKLVMetadataCallback
    public onAsynchronousKLVMetadata: OnAsynchronousKLVMetadataCallback;
    public onSMPTE2038Metadata: OnSMPTE2038MetadataCallback;
    public onSCTE35Metadata: OnSCTE35MetadataCallback;
    public onPESPrivateData: OnPESPrivateDataCallback;
    public onPESPrivateDataDescriptor: OnPESPrivateDataDescriptorCallback;
    public onSystemClock?: OnSystemClockCallback;
    public onAudioTracksMetadata?: OnAudioTracksMetadataCallback;

    public constructor() {}

    public destroy(): void {
        this.onError = null;
        this.onMediaInfo = null;
        this.onMetaDataArrived = null;
        this.onTrackMetadata = null;
        this.onDataAvailable = null;
        this.onTimedID3Metadata = null;
        this.onSynchronousKLVMetadata = null;
        this.onAsynchronousKLVMetadata = null;
        this.onSMPTE2038Metadata = null;
        this.onSCTE35Metadata = null;
        this.onPESPrivateData = null;
        this.onPESPrivateDataDescriptor = null;
        this.onSystemClock = null;
        this.onAudioTracksMetadata = null;
    }

    abstract parseChunks(chunk: ArrayBuffer, byteStart: number): number;

    public insertDiscontinuity(): void {}
    public switchAudioTrack(id: string): void {}
}
