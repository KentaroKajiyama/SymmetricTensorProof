/* native/glue.cpp */
#include <lean/lean.h>
#include <vector>
#include <set>
#include <string>
#include <fstream>
#include <algorithm>
#include <iostream>

// 並列実行用のヘッダー
#include <thread>
#include <mutex>
#include <future>

#define MAXN 64

// ==========================================================
// 1. C言語ライブラリ (Nauty) のインクルード
//    ここだけ extern "C" で囲みます。
// ==========================================================
extern "C" {
    #include "nauty.h"
    #include "naututil.h" 
    #include "gtools.h"

    // 【修正】 dispatch_graph の手動宣言を削除しました。
    // nauty.h に既に定義が含まれているため、重複定義エラーになります。
}

// 【修正】 windows.h のインクルードを削除しました。
// nauty.h の 'boolean' (int) と windows.h の 'boolean' (unsigned char) が
// 衝突するためです。ファイルI/Oには標準C++ (<fstream>) を使うので不要です。

// ==========================================================
// 2. C++ ヘルパー関数と型定義
//    ここは extern "C" の「外」です。
// ==========================================================

using GraphKey = std::vector<graph>;

/* 【修正版】パーティション設定関数
    - Anchors: 個別に固定する -> ptn = 0 (Singleton Cell)
    - Others:  まとめて1つのグループ -> ptn = 1 (Large Cell)
*/
// ==========================================================
// ヘルパー関数: パーティション設定 (std::vector 版)
// スレッドセーフにするため、Leanオブジェクトではなく int vector を受け取ります
// ==========================================================
void setup_partition(
    int n, 
    const std::vector<int>& fixed_nodes, // LeanオブジェクトではなくC++標準型
    int* lab,                            // Nauty APIに合わせてポインタで受け取る
    int* ptn
) {
    size_t num_anchors = fixed_nodes.size();
    std::vector<bool> is_anchor(n, false);
    
    // 1. アンカーを lab の先頭に配置
    for (size_t i = 0; i < num_anchors; i++) {
        int v = fixed_nodes[i];
        
        lab[i] = v;
        // アンカーは「それぞれ別の色（固定）」なので区切る (0)
        ptn[i] = 0; 
        is_anchor[v] = true;
    }

    // 2. 残りの頂点 (Cloud) を配置
    int idx = num_anchors;
    for (int v = 0; v < n; v++) {
        if (!is_anchor[v]) {
            lab[idx] = v;
            // 残りの頂点は「同じ色（互換可能）」なのでつなげる (1)
            ptn[idx] = 1; 
            idx++;
        }
    }
    
    // 最後の頂点は必ず区切り (0)
    if (n > 0) {
        ptn[n - 1] = 0;
    }
}

// ==========================================================
// 3. Lean FFI エクスポート関数
//    Lean から見えるように extern "C" をつけます。
// ==========================================================

extern "C" {

// FFI 1: Graph6 ファイルの読み込み
lean_obj_res cpp_load_graphs(lean_obj_arg n_obj, lean_obj_arg path_obj, lean_obj_arg world) {
    size_t n = lean_unbox(n_obj);
    size_t n_sq = n * n;
    int m = SETWORDSNEEDED(n);
    const char* path = lean_string_cstr(path_obj);

    std::ifstream infile(path);
    if (!infile.is_open()) {
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("Could not open file")));
    }

    std::vector<std::string> lines;
    std::string line;
    while (std::getline(infile, line)) {
        // Windowsの改行コード(CR)対策
        if (!line.empty() && line.back() == '\r') {
            line.pop_back();
        }
        if (line.length() > 0) lines.push_back(line);
    }
    infile.close();

    lean_object* result_arr = lean_alloc_array(lines.size(), lines.size());
    std::vector<graph> g_buf(m * n);

    for (size_t i = 0; i < lines.size(); ++i) {
        lean_object* ba_obj = lean_alloc_sarray(1, n_sq, n_sq);
        uint8_t* ptr = lean_sarray_cptr(ba_obj);
        
        std::string mutable_line = lines[i];
        
        // stringtograph 呼び出し
        stringtograph(&mutable_line[0], g_buf.data(), m);

        std::fill(ptr, ptr + n_sq, 0);

        for (int u = 0; u < n; u++) {
            for (int v = u + 1; v < n; v++) {
                if (ISELEMENT(GRAPHROW(g_buf.data(), u, m), v)) { 
                        ptr[u * n + v] = 1;
                        ptr[v * n + u] = 1;
                }
            }
        }

        lean_array_set_core(result_arr, i, ba_obj);
    }

    return lean_io_result_mk_ok(result_arr);
}

// FFI 2: 同型除去
lean_obj_res cpp_reduce_iso(lean_obj_arg n_obj, lean_obj_arg S_arr, lean_obj_arg anchors_arr) {
    int n = (int)lean_unbox(n_obj);
    int m = SETWORDSNEEDED(n);
    size_t s_size = lean_array_size(S_arr);

    // 0. アンカー情報の取得 (ここで Lean配列 → C++ vector に変換)
    size_t num_anchors = lean_array_size(anchors_arr);
    std::vector<int> fixed_nodes;
    fixed_nodes.reserve(num_anchors);
    for (size_t i = 0; i < num_anchors; i++) {
        fixed_nodes.push_back((int)lean_unbox(lean_array_uget(anchors_arr, i)));
    }

    // 1. 全グラフのデータを一つの大きなベクターにまとめてコピー (アロケーション回数を1回にする)
    // 各グラフ m*n 個の graph 型データを持つ
    std::vector<graph> all_graphs_data(s_size * m * n, 0);
    std::vector<lean_object*> original_objs(s_size);

    for (size_t i = 0; i < s_size; i++) {
        lean_object* adj_mat_obj = lean_array_uget(S_arr, i);
        original_objs[i] = adj_mat_obj;
        
        uint8_t* bytes = lean_sarray_cptr(adj_mat_obj);
        graph* g_ptr = &all_graphs_data[i * m * n];

        for (int r = 0; r < n; r++) {
            graph* row_ptr = GRAPHROW(g_ptr, r, m);
            for (int c = 0; c < n; c++) {
                if (r != c && bytes[r * n + c] == 1) {
                    ADDELEMENT(row_ptr, c); 
                }
            }
        }
    }

    // 2. 並列処理
    unsigned int num_threads = std::thread::hardware_concurrency();
    if (num_threads == 0) num_threads = 4;

    std::vector<std::pair<GraphKey, lean_object*>> all_candidates;
    std::mutex merge_mutex;
    std::atomic<size_t> progress_count(0); // 進捗確認用
    // 追加のミューテックス（Nauty呼び出し専用）
    std::mutex nauty_mutex;

    auto worker = [&](size_t start_idx, size_t end_idx) {
        // スレッドごとに1回だけワークスペースを確保（ループ内での再確保を防ぐ）
        std::vector<int> lab(n), ptn(n), orbits(n);
        std::vector<graph> canonical_g(m * n);
        std::vector<graph> g_work_buffer(m * n); // コピー用のバッファ
        
        // ローカル結果保持
        std::vector<std::pair<GraphKey, lean_object*>> local_candidates;
        std::set<GraphKey> local_seen;

        for (size_t i = start_idx; i < end_idx; i++) {
            // Nautyは入力を破壊することがあるため、ワークバッファにコピー
            std::copy(all_graphs_data.begin() + (i * m * n), 
                      all_graphs_data.begin() + ((i + 1) * m * n), 
                      g_work_buffer.begin());

            // 毎ループ options を初期化 (スレッドセーフを確実に)
            DEFAULTOPTIONS_GRAPH(worker_options);
            statsblk stats;
            worker_options.getcanon = TRUE;
            worker_options.defaultptn = FALSE;
            worker_options.digraph = FALSE;

            setup_partition(n, fixed_nodes, lab.data(), ptn.data());

            densenauty(g_work_buffer.data(), lab.data(), ptn.data(), orbits.data(), 
                    &worker_options, &stats, m, n, canonical_g.data());

            GraphKey key(canonical_g.begin(), canonical_g.end());

            if (local_seen.find(key) == local_seen.end()) {
                local_seen.insert(key);
                local_candidates.push_back({std::move(key), original_objs[i]});
            }
            
            // // 100件ごとに進捗をカウント
            // if (++progress_count % 100 == 0) {
            //     // 必要ならここでログ出力
            // }
            
        }
        // ★★★ 【追加】このスレッド用のNautyメモリを解放 ★★★
        nauty_freedyn();
        // マージ処理
        std::lock_guard<std::mutex> lock(merge_mutex);
        all_candidates.insert(all_candidates.end(), 
                              std::make_move_iterator(local_candidates.begin()), 
                              std::make_move_iterator(local_candidates.end()));
    };

    // 3. スレッド起動
    std::vector<std::thread> threads;
    size_t chunk_size = (s_size + num_threads - 1) / num_threads;

    for (unsigned int t = 0; t < num_threads; t++) {
        size_t start = t * chunk_size;
        size_t end = std::min(start + chunk_size, s_size);
        if (start < end) {
            threads.emplace_back(worker, start, end);
        }
    }

    for (auto& t : threads) {
        if (t.joinable()) t.join();
    }

    // 4. 最終マージ
    std::set<GraphKey> final_seen;
    std::vector<lean_object*> unique_objs;

    for (const auto& pair : all_candidates) {
        if (final_seen.find(pair.first) == final_seen.end()) {
            final_seen.insert(pair.first);
            unique_objs.push_back(pair.second);
        }
    }

    // 5. 結果の作成
    lean_obj_res result = lean_alloc_array(unique_objs.size(), unique_objs.size());
    for (size_t i = 0; i < unique_objs.size(); i++) {
        lean_inc(unique_objs[i]);
        lean_array_set_core(result, i, unique_objs[i]);
    }

    return result;
}

// FFI 3: Graph6 書き出し
lean_obj_res cpp_dump_graph6(lean_obj_arg n_obj, lean_obj_arg path_obj, b_lean_obj_arg S_arr, lean_obj_arg world) {
    int n = (int)lean_unbox(n_obj);
    int m = SETWORDSNEEDED(n);
    const char* path = lean_string_cstr(path_obj);
    size_t s_size = lean_array_size(S_arr);

    FILE* outfile = fopen(path, "w");
    if (!outfile) {
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("Could not open file")));
    }

    std::vector<graph> g(m * n);

    for (size_t i = 0; i < s_size; i++) {
        lean_object* adj_mat_obj = lean_array_get_core(S_arr, i);
        uint8_t* raw_bytes = lean_sarray_cptr(adj_mat_obj);

        EMPTYGRAPH(g.data(), m, n);
        for (int u = 0; u < n; u++) {
            for (int v = u + 1; v < n; v++) {
                if (raw_bytes[u * n + v]) {
                    ADDONEEDGE(g.data(), u, v, m);
                }
            }
        }

        char* g6_str = ntog6(g.data(), m, n);
        fprintf(outfile, "%s\n", g6_str);
    }

    fclose(outfile);
    return lean_io_result_mk_ok(lean_box(0));
}

} // End extern "C"