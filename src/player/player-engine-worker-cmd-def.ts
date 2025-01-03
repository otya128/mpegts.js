/*
 * Copyright (C) 2023 zheng qian. All Rights Reserved.
 *
 * @author zheng qian <xqq@xqq.im>
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

export type WorkerCommandOp =
    | 'logging_config'
    | 'init'
    | 'destroy'
    | 'initialize_mse'
    | 'shutdown_mse'
    | 'load'
    | 'unload'
    | 'unbuffered_seek'
    | 'timeupdate'
    | 'readystatechange'
    | 'pause_transmuxer'
    | 'resume_transmuxer'
    | 'switch_audio_track'
    | 'reset_audio';

export type WorkerCommandPacket = {
    cmd: WorkerCommandOp,
};

export type WorkerCommandPacketInit = WorkerCommandPacket & {
    cmd: 'init',
    media_data_source: any,
    config: any,
};

export type WorkerCommandPacketLoggingConfig = WorkerCommandPacket & {
    cmd: 'logging_config',
    logging_config: any,
};

export type WorkerCommandPacketUnbufferedSeek = WorkerCommandPacket & {
    cmd: 'unbuffered_seek',
    milliseconds: number,
};

export type WorkerCommandPacketTimeUpdate = WorkerCommandPacket & {
    cmd: 'timeupdate',
    current_time: number,
};

export type WorkerCommandPacketReadyStateChange = WorkerCommandPacket & {
    cmd: 'readystatechange',
    ready_state: number,
};

export type WorkerCommandPacketSwitchAudioTrack = WorkerCommandPacket & {
    cmd: 'switch_audio_track',
    id: string,
};

export type WorkerCommandPacketResetAudio = WorkerCommandPacket & {
    cmd: 'reset_audio',
    milliseconds: number,
};
