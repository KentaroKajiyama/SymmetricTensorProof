import Lake
open Lake DSL

package SymmetricTensorProof where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩
  ]
  moreLeancArgs := #["-O3"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «SymmetricTensorProof» where

---------------------------------------------------------------------
-- 1. リンク設定 (パスの明示的な指定)
---------------------------------------------------------------------
def commonLinkArgs : Array String :=
  #[
    -- 1. システムの C++ ライブラリがある場所を明示的に追加 (Ubuntu 64bit 標準)
    "-L/usr/lib/x86_64-linux-gnu",
    -- 2. その上でライブラリを指定
    "-lstdc++",
    -- 3. Lean ツールチェーンのパス (jesus さん用)
    "-L/home/jesus/.elan/toolchains/leanprover--lean4---v4.27.0-rc1/lib",
    -- 4. 新しい glibc で削除されたシンボルのダミー定義 (これをしないとリンクエラー)
    "-Wl,--defsym=__libc_csu_init=0",
    "-Wl,--defsym=__libc_csu_fini=0"
  ]

lean_exe «graph-enum-claim5» where
  root := `SymmetricTensorProof.GraphEnum.Main
  exeName := "graph-enum-claim5"
  moreLinkArgs := commonLinkArgs

---------------------------------------------------------------------
-- 2. C++ (Nauty) コンパイル設定 (16.04 の設定を維持)
---------------------------------------------------------------------

def nautySrcs : Array String := #[
  "nauty.c", "nautil.c", "gtools.c", "naututil.c", "nautinv.c", "schreier.c",
  "nausparse.c", "naurng.c", "naugraph.c"
]

target glue.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "native" / "glue.o"
  let srcFile := pkg.dir / "native" / "glue.cpp"
  let srcJob ← inputFile srcFile false
  let leanIncludeDir ← getLeanIncludeDir

  let weakArgs := #[
    "-I", (pkg.dir / "native").toString,
    "-I", leanIncludeDir.toString
  ]

  let traceArgs := #[
    "-O3",
    "-std=c++14",
    "-fPIC"
  ]
  buildO oFile srcJob weakArgs traceArgs "c++"

extern_lib liblean_glue pkg := do
  let glueJob ← fetch <| pkg.target ``glue.o
  let buildDir := pkg.buildDir / "native"
  let srcDir := pkg.dir / "native"
  let mut nautyJobs : Array (Job System.FilePath) := #[]

  let nautyTraceArgs := #[
    "-O3",
    "-DMAXN=64",
    "-fPIC"
  ]
  let nautyWeakArgs := #["-I", srcDir.toString]

  for src in nautySrcs do
    let oFile := buildDir / (src ++ ".o")
    let srcFile := srcDir / src
    let srcJob ← inputFile srcFile false
    let job ← buildO oFile srcJob nautyWeakArgs nautyTraceArgs "cc"
    nautyJobs := nautyJobs.push job

  let libFile := pkg.buildDir / "lib" / "liblean_glue.a"
  buildStaticLib libFile (#[glueJob] ++ nautyJobs)
