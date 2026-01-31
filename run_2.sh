#!/bin/bash

START=73
END=199
# 同時に実行するプロセス数（CPUコア数に合わせて調整。例：16コアなら 8〜12 程度）
MAX_JOBS=2

seq $START $END | xargs -I{} -P $MAX_JOBS sh -c "
    echo 'Starting chunk {}...';
    .lake/build/bin/graph-enum-claim5 \
        anchored_init_padded_7.g6 \
        single \
        anchored_4433_17 \
        anchored_4433_21 \
        {} || { echo 'Error: Chunk {} failed'; exit 1; }
"

echo "All tasks finished."