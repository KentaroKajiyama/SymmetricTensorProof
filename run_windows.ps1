# 開始と終了のインデックスを設定
$START = 0
$END = 199

# 出力先ディレクトリが存在しない場合は作成しておく
$OutputPath = "./outputs/claim5/anchored/44330/"
if (-not (Test-Path $OutputPath)) {
    New-Item -ItemType Directory -Path $OutputPath -Force
}

for ($i = $START; $i -le $END; $i++) {
    Write-Host "------------------------------------------"
    Write-Host "Processing chunk $i of $END..."
    Write-Host "------------------------------------------"

    # 実行コマンドの呼び出し
    # PowerShellではカレントディレクトリの実行ファイルに .\ を付ける必要があります
    & .lake/build/bin/graph-enum-claim5 `
        anchored_init_padded_4.g6 `
        single `
        ./outputs/claim5/intermediate/44330/18_part `
        ./outputs/claim5/anchored/44330/18_part `
        $i

    # 前のコマンドが失敗（終了コードが 0 以外）したら停止する
    # $LASTEXITCODE は直前の外部プロセスの終了コードを保持します
    if ($LASTEXITCODE -ne 0) {
        Write-Error "Error: Chunk $i failed. Exiting."
        exit 1
    }
}

Write-Host "Done! All chunks from $START to $END have been processed."

# インスタンスを停止する場合（必要に応じてコメントアウトを外してください）
# Write-Host "All tasks finished. Shutting down in 60 seconds..."
# Start-Sleep -Seconds 60
# Stop-Computer -Force