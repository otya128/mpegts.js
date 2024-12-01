export interface SeekLocator {
    locateSeekPosition(milliseconds: number, signal?: AbortSignal): Promise<number>;
}
