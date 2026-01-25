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
-- 1. リンク設定 (シンプルになります)
---------------------------------------------------------------------
def commonLinkArgs : Array String :=
  #[
    "-L/home/jesus/.elan/toolchains/leanprover--lean4---v4.27.0-rc1/lib",
    "-Wl,--defsym=__libc_csu_init=0",
    "-Wl,--defsym=__libc_csu_fini=0"
  ]

lean_exe «graph-enum-claim5» where
  root := `SymmetricTensorProof.GraphEnum.Main
  exeName := "graph-enum-claim5"
  moreLinkArgs := commonLinkArgs

---------------------------------------------------------------------
-- 2. C++ (Nauty) コンパイル設定
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
  
  -- ★修正ポイント: Lean ツールチェーン内の clang++ のパスを取得
  let clangpp := (leanIncludeDir.parentDirectory / "bin" / "clang++").toString

  let weakArgs := #[
    "-I", (pkg.dir / "native").toString,
    "-I", leanIncludeDir.toString,
    "-fPIC",
    "-x", "c++"  -- 明示的に C++ として扱う
  ]

  let traceArgs := #[
    "-O3",
    "-std=c++14"
  ]
  -- ★修正ポイント: "c++" ではなく、Lean 付属の clang++ を使う
  buildO oFile srcJob weakArgs traceArgs clangpp

extern_lib liblean_glue pkg := do
  let glueJob ← fetch <| pkg.target ``glue.o
  let buildDir := pkg.buildDir / "native"
  let srcDir := pkg.dir / "native"
  let mut nautyJobs : Array (Job System.FilePath) := #[]

  let nautyTraceArgs := #["-O3", "-DMAXN=64", "-fPIC"]
  let nautyWeakArgs := #["-I", srcDir.toString]

  for src in nautySrcs do
    let oFile := buildDir / (src ++ ".o")
    let srcFile := srcDir / src
    let srcJob ← inputFile srcFile false
    -- Nauty は C なので、これはシステムの cc (gcc) のままでも、leanc に変えてもOKです
    let job ← buildO oFile srcJob nautyWeakArgs nautyTraceArgs "cc"
    nautyJobs := nautyJobs.push job

  let libFile := pkg.buildDir / "lib" / "liblean_glue.a"
  buildStaticLib libFile (#[glueJob] ++ nautyJobs)