/* native/glue.cpp */
#include <lean/lean.h>
#include <vector>
#include <set>
#include <string>
#include <fstream>
#include <algorithm>
#include <iostream>

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
void setup_partition(
    int n, 
    b_lean_obj_arg anchors_arr, 
    std::vector<int>& lab, 
    std::vector<int>& ptn
) {
    size_t num_anchors = lean_array_size(anchors_arr);
    std::vector<bool> is_anchor(n, false);
    
    // 1. アンカーを lab の先頭に配置
    for (size_t i = 0; i < num_anchors; i++) {
        lean_object* val_obj = lean_array_get_core(anchors_arr, i);
        int v = (int)lean_unbox(val_obj);
        
        lab[i] = v;
        // 【修正】アンカーは「それぞれ別の色」で固定したいので、
        //  区切りを表す 0 をセットします。
        ptn[i] = 0; 
        is_anchor[v] = true;
    }

    // 2. 残りの頂点 (Cloud) を配置
    int idx = num_anchors;
    for (int v = 0; v < n; v++) {
        if (!is_anchor[v]) {
            lab[idx] = v;
            // 【修正】残りの頂点は「同じ色（互換可能）」にしたいので、
            //  つながりを表す 1 をセットします。
            ptn[idx] = 1; 
            idx++;
        }
    }
    
    // 【修正】最後の頂点は必ず区切り (0) にする
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
lean_obj_res cpp_reduce_iso(lean_obj_arg n_obj, b_lean_obj_arg S_arr, b_lean_obj_arg anchors_arr) {
    int n = (int)lean_unbox(n_obj);
    int m = SETWORDSNEEDED(n); 
    
    // Nauty 初期化チェック
    // nauty_check(WORDSIZE, m, n, NAUTYVERSIONID); 

    std::vector<graph> g(m * n);
    std::vector<graph> canong(m * n);
    std::vector<int> lab(n), ptn(n), orbits(n);
    
    static DEFAULTOPTIONS_GRAPH(options);
    static statsblk stats;
    options.getcanon = TRUE;
    options.defaultptn = FALSE;
    options.digraph = FALSE;

    setup_partition(n, anchors_arr, lab, ptn);

    std::set<GraphKey> unique_set;
    std::vector<lean_object*> unique_lean_objs;

    size_t s_size = lean_array_size(S_arr);

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

        std::vector<int> lab_curr = lab;
        std::vector<int> ptn_curr = ptn;
        
        densenauty(g.data(), lab_curr.data(), ptn_curr.data(), orbits.data(), 
                    &options, &stats, m, n, canong.data());

        GraphKey key(canong.begin(), canong.end());
        if (unique_set.find(key) == unique_set.end()) {
            unique_set.insert(key);
            lean_inc(adj_mat_obj);
            unique_lean_objs.push_back(adj_mat_obj);
        }
    }

    lean_obj_res result = lean_alloc_array(unique_lean_objs.size(), unique_lean_objs.size());
    for (size_t i = 0; i < unique_lean_objs.size(); i++) {
        lean_array_set_core(result, i, unique_lean_objs[i]);
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