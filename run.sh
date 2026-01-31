#!/bin/bash

# 開始と終了のインデックスを設定
START=0
END=199

# 出力先ディレクトリが存在しない場合は作成しておく
mkdir -p ./outputs/claim5/anchored/44330/

for ((i=START; i<=END; i++))
do
    echo "------------------------------------------"
    echo "Processing chunk $i of $END..."
    echo "------------------------------------------"

    # 実行コマンド (末尾の引数に $i を渡す)
    .lake/build/bin/graph-enum-claim5 \
        anchored_init_padded_4.g6 \
        single \
        ./outputs/claim5/intermediate/44330/18_part \
        ./outputs/claim5/anchored/44330/18_part \
        $i

    # 前のコマンドが失敗（終了コードが 0 以外）したら停止する
    if [ $? -ne 0 ]; then
        echo "Error: Chunk $i failed. Exiting."
        exit 1
  fi
done

echo "Done! All chunks from $START to $END have been processed."
# echo "All tasks finished. Shutting down in 60 seconds..."
# sleep 60
# sudo poweroff  # インスタンスを停止する（課金を止める）