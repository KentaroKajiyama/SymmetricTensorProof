import Lake
open Lake DSL

package SymmetricTensorProof where
  -- TOMLの [leanOptions] に相当する設定
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩
  ]
  -- C++ コンパイル用の追加フラグ（超重要）
  moreLeancArgs := #[
    "-O3",                     -- 最適化
    "-D_WIN32",                -- Windows環境であることを明示
    "-DWIN32",                 -- 念のため両方定義
    "-DAVOID_SYS_WAIT_H",      -- sys/wait.h を回避
    "-DHAVE_WAIT_H=0",         -- wait.h を持っていないと宣言
    "-I./native"               -- ヘッダファイルの場所
  ]

-- [[require]] name = "mathlib" に相当
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- [[lean_lib]] name = "SymmetricTensorProof" に相当
@[default_target]
lean_lib «SymmetricTensorProof» where
  -- ライブラリ設定

-- TODO: リファクタリング後に改めてコンパイルする
-- [[lean_exe]] name = "verify_proof" に相当
-- lean_exe «verify_proof» where
--   root := `SymmetricTensorProof.Verification.Main
--   exeName := "verify_proof"

-- [[lean_exe]] name = "symm-tensor-proof" に相当
lean_exe «symm-tensor-proof» where
  root := `SymmetricTensorProof.GraphEnum.Main
  exeName := "graph-enum-claim5"

lean_exe «graph-enum-test» where
  root := `SymmetricTensorProof.GraphEnum.Test
  exeName := "graph-enum-test"

---------------------------------------------------------------------
-- ここから下が C++ (Nauty) 連携用の設定です（TOMLでは書けない部分）
---------------------------------------------------------------------

-- 1. glue.cpp のコンパイル設定
target glue.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "native" / "glue.o"
  -- 入力ソースコード (.cpp)
  let srcFile := pkg.dir / "native" / "glue.cpp"
  let srcJob ← inputFile srcFile false
  -- ヘッダファイルの場所を指定
  let weakArgs := #["-I", (pkg.dir / "native").toString]
  -- buildO (ファイル名) (出力先) (ソース) (コンパイル引数) (追加引数: -fPICは必須) (コンパイラ: c++)
  buildO oFile srcJob weakArgs (compiler:="c++")

-- 2. nauty.c のコンパイル設定 (Nauty本体)
-- ※ もし naututil.c など他のファイルも必要なら同様に追加します
target nauty.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "native" / "nauty.o"
  let srcFIle := pkg.dir / "native" / "nauty.c"
  let srcJob ← inputFile srcFIle false
  let weakArgs := #["-I", (pkg.dir / "native").toString]
  -- こちらはC言語なのでコンパイラ指定は "cc" (または "clang")
  buildO oFile srcJob weakArgs (compiler:="cc")

-- 3. コンパイルした .o ファイルをまとめて静的ライブラリにする
extern_lib liblean_glue pkg := do
  -- 1. ライブラリファイル名を作る (例: "liblean_glue.a")
  let name := nameToStaticLib "lean_glue"
  -- 2. 依存する .o ファイルの Job を取得する
  -- fetch は Job System.FilePath を返します
  let glueO ← fetch <| pkg.target ``glue.o
  let nautyO ← fetch <| pkg.target ``nauty.o
  -- 3. 出力先のパス (System.FilePath) を正しく作る
  -- pkg.nativeLibDir は使えないので、pkg.buildDir / "lib" を使います
  let libDir := pkg.buildDir / "lib"
  let libFile := libDir / name  -- これが buildStaticLib の第1引数になります
  -- 4. 定義通りに buildStaticLib を呼ぶ
  -- 第1引数: libFile (System.FilePath)
  -- 第2引数: oFileJobs (Array (Job System.FilePath))
  buildStaticLib libFile #[glueO, nautyO]
