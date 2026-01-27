#!/bin/bash

# 開始と終了のインデックスを設定
START=73
END=199

# 出力先ディレクトリが存在しない場合は作成しておく

for ((i=START; i<=END; i++))
do
    echo "------------------------------------------"
    echo "Processing chunk $i of $END..."
    echo "------------------------------------------"

    # 実行コマンド (末尾の引数に $i を渡す)
    .lake/build/bin/graph-enum-claim5 \
        anchored_init_padded_7.g6 \
        single \
        anchored_4433_17 \
        anchored_4433_21 \
        $i

    # 前のコマンドが失敗（終了コードが 0 以外）したら停止する
    if [ $? -ne 0 ]; then
        echo "Error: Chunk $i failed. Exiting."
        exit 1
  fi
done

echo "Done! All chunks from $START to $END have been processed."
echo "All tasks finished."