/*
 * nauty_wrapper.c
 * Nautyの全ソースをまとめてコンパイルするためのラッパー。
 * これにより、lakefile.lean で扱うファイルが1つで済みます。
 */

// Nautyの設定マクロが必要な場合はここで定義
// #define MAXN 64 

#include "nauty.c"
#include "nautil.c"
#include "naugraph.c"
#include "schreier.c"
#include "naurng.c"
#include "nautinv.c"
#include "gtools.c"