/* native/glue.cpp */
#include <lean/lean.h>
#include <vector>
#include <set>
#include <string>
#include <fstream>
#include <algorithm>

#define MAXN 64
#include "nauty.h"
#include "gtools.h" 

extern "C" {

using GraphKey = std::vector<graph>;

// ==========================================================
// Helper 2: Nauty 用パーティション設定
// ==========================================================

void setup_partition(
    int n, 
    b_lean_obj_arg anchors_arr, 
    std::vector<int>& lab, 
    std::vector<int>& ptn
) {
    size_t num_anchors = lean_array_size(anchors_arr);
    std::vector<bool> is_anchor(n, false);
    
    // 1. アンカーを lab の先頭に配置し、個別にセルを分ける (ptn=1)
    for (size_t i = 0; i < num_anchors; i++) {
        lean_object* val_obj = lean_array_get_core(anchors_arr, i);
        int v = (int)lean_unbox(val_obj);
        
        lab[i] = v;
        ptn[i] = 1; 
        is_anchor[v] = true;
    }

    // 2. 残りの頂点を配置し、同じセルにまとめる (ptn=0)
    int idx = num_anchors;
    for (int v = 0; v < n; v++) {
        if (!is_anchor[v]) {
            lab[idx] = v;
            ptn[idx] = 0; // 0 は「次の頂点と同じセル」を意味する
            idx++;
        }
    }
    
    // nauty 仕様: 最後の要素の ptn は必ず 0
    // (ただし、その手前が 1 ならば独立したセル、0 ならば前のセルと同じ)
    ptn[n - 1] = 0;
}

// ==========================================================
// FFI 1: Graph6 ファイルの読み込み (Nauty stringtograph 利用)
// ==========================================================
lean_obj_res cpp_load_graphs(lean_obj_arg n_obj, lean_obj_arg path_obj, lean_obj_arg world) {
    size_t n = lean_unbox(n_obj);
    size_t n_sq = n * n;
    int m = SETWORDSNEEDED(n); // Nauty用
    const char* path = lean_string_cstr(path_obj);

    std::ifstream infile(path);
    if (!infile.is_open()) {
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("Could not open file")));
    }

    std::vector<std::string> lines;
    std::string line;
    while (std::getline(infile, line)) {
        if (line.length() > 0) lines.push_back(line);
    }
    infile.close();

    lean_object* result_arr = lean_alloc_array(lines.size(), lines.size());

    // ★修正点1: Nauty用のグラフバッファをここで確保 (1回確保して使い回してもOKですが、安全のため毎回リセット前提で)
    // Nauty の graph 型は unsigned long などのエイリアスです。
    // サイズは m * n ワード必要です。
    std::vector<graph> g_buf(m * n);

    for (size_t i = 0; i < lines.size(); ++i) {
        lean_object* ba_obj = lean_alloc_sarray(1, n_sq, n_sq);
        uint8_t* ptr = lean_sarray_cptr(ba_obj);
        
        // --- Nauty の関数でパース ---
        // stringtograph は char* を受け取り、内部で malloc した graph* を返す
        // (行末の改行などは関数内で無視してくれるが、const char* ではなく char* を要求するのでコピーする)
        std::string mutable_line = lines[i];
        
        // ★修正点2: stringtograph の正しい呼び出し方
        // stringtograph(char *s, graph *g, int m)
        // g_buf.data() で生ポインタを渡します。
        stringtograph(&mutable_line[0], g_buf.data(), m);

        // Lean用の ByteArray に変換
        // 一旦 0 で埋める
        std::fill(ptr, ptr + n_sq, 0);

        for (int u = 0; u < n; u++) {
            for (int v = u + 1; v < n; v++) {
                // g_buf.data() に対してマクロを使う
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


// ==========================================================
// FFI 2: 同型除去 (Nauty Dense Mode)
// Lean: reduce_iso {n} (S : @& Array (AdjMat n)) (anchors : @& Array (Fin n)) : Array (AdjMat n)
// ==========================================================
lean_obj_res cpp_reduce_iso(lean_obj_arg n_obj, b_lean_obj_arg S_arr, b_lean_obj_arg anchors_arr) {
    int n = (int)lean_unbox(n_obj);
    int m = SETWORDSNEEDED(n); 
    
    // Nauty 初期化チェック
    nauty_check(WORDSIZE, m, n, NAUTYVERSIONID);

    // 作業領域
    std::vector<graph> g(m * n);
    std::vector<graph> canong(m * n);
    std::vector<int> lab(n), ptn(n), orbits(n);
    
    // オプション
    static DEFAULTOPTIONS_GRAPH(options);
    static statsblk stats;
    options.getcanon = TRUE;
    options.defaultptn = FALSE; // 自前のパーティションを使用
    options.digraph = FALSE;

    // パーティション構築 (アンカー情報は共通)
    setup_partition(n, anchors_arr, lab, ptn);

    // 重複除去用
    std::set<GraphKey> unique_set;
    std::vector<lean_object*> unique_lean_objs;

    size_t s_size = lean_array_size(S_arr);

    for (size_t i = 0; i < s_size; i++) {
        lean_object* adj_mat_obj = lean_array_get_core(S_arr, i);
        uint8_t* raw_bytes = lean_sarray_cptr(adj_mat_obj);

        // 1. Lean -> Nauty 変換
        EMPTYGRAPH(g.data(), m, n);
        for (int u = 0; u < n; u++) {
            for (int v = u + 1; v < n; v++) {
                if (raw_bytes[u * n + v]) {
                    ADDONEEDGE(g.data(), u, v, m);
                }
            }
        }

        // 2. Nauty 実行 (lab/ptn は破壊されるのでコピーを渡す)
        std::vector<int> lab_curr = lab;
        std::vector<int> ptn_curr = ptn;
        
        densenauty(g.data(), lab_curr.data(), ptn_curr.data(), orbits.data(), 
                    &options, &stats, m, n, canong.data());

        // 3. 重複チェック
        GraphKey key(canong.begin(), canong.end());
        if (unique_set.find(key) == unique_set.end()) {
            unique_set.insert(key);
            
            // 採用 (参照カウント増)
            lean_inc(adj_mat_obj);
            unique_lean_objs.push_back(adj_mat_obj);
        }
    }

    // 結果配列作成
    lean_obj_res result = lean_alloc_array(unique_lean_objs.size(), unique_lean_objs.size());
    for (size_t i = 0; i < unique_lean_objs.size(); i++) {
        lean_array_set_core(result, i, unique_lean_objs[i]);
    }

    return result; // 純粋関数なので直接返す (IOラップなし)
}


// ==========================================================
// FFI 3: Graph6 ファイルへの書き出し (Nauty ntog6 利用)
// ==========================================================
lean_obj_res cpp_dump_graph6(lean_obj_arg n_obj, lean_obj_arg path_obj, b_lean_obj_arg S_arr, lean_obj_arg world) {
    int n = (int)lean_unbox(n_obj);
    int m = SETWORDSNEEDED(n);
    const char* path = lean_string_cstr(path_obj);
    size_t s_size = lean_array_size(S_arr);

    FILE* outfile = fopen(path, "w");
    if (!outfile) {
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("Could not open file")));
    }

    // Nauty形式の一時バッファ
    std::vector<graph> g(m * n);

    for (size_t i = 0; i < s_size; i++) {
        lean_object* adj_mat_obj = lean_array_get_core(S_arr, i);
        uint8_t* raw_bytes = lean_sarray_cptr(adj_mat_obj);

        // Lean -> Nauty 変換
        EMPTYGRAPH(g.data(), m, n);
        for (int u = 0; u < n; u++) {
            for (int v = u + 1; v < n; v++) {
                if (raw_bytes[u * n + v]) {
                    ADDONEEDGE(g.data(), u, v, m);
                }
            }
        }

        // --- Nauty の関数で文字列化 ---
        // ntog6(graph *g, int m, int n) -> char*
        // Nauty の静的バッファへのポインタが返ってくる
        char* g6_str = ntog6(g.data(), m, n);
        
        fprintf(outfile, "%s\n", g6_str);
    }

    fclose(outfile);
    return lean_io_result_mk_ok(lean_box(0));
}

} // extern "C"