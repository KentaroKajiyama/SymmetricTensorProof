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
  moreLeancArgs := #[
    "-O3", "-D_WIN32", "-DWIN32",
    "-DAVOID_SYS_WAIT_H", "-DHAVE_WAIT_H=0",
    "-I./native"
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «SymmetricTensorProof» where

---------------------------------------------------------------------
-- 1. 共通パス設定 (MSYS2 UCRT64)
---------------------------------------------------------------------
def msysRoot := "C:/msys64/ucrt64"
def sysLibPath := s!"{msysRoot}/lib"
def gccVersion := "13.2.0"
def gccLibPath := s!"{msysRoot}/lib/gcc/x86_64-w64-mingw32/{gccVersion}"

-- コンパイル用のヘッダーパス
def cxxIncludePath1 := s!"{msysRoot}/include/c++/{gccVersion}"
def cxxIncludePath2 := s!"{msysRoot}/include/c++/{gccVersion}/x86_64-w64-mingw32"

---------------------------------------------------------------------
-- 2. リンク設定 (重複許可 & 強制リンク)
---------------------------------------------------------------------
def commonLinkArgs : Array String :=
  #[
    "-static",

    -- 【重要】重複定義エラーを無視するフラグ
    -- libc++.a と libstdc++.a が衝突しても、先に見つかった方を使って続行させます
    "-Wl,--allow-multiple-definition",

    "-Wl,--start-group",

    -- MSYS2 ライブラリ群
    s!"{sysLibPath}/libmingw32.a",
    s!"{sysLibPath}/libstdc++.a",
    s!"{gccLibPath}/libgcc.a",
    s!"{gccLibPath}/libgcc_eh.a",
    s!"{sysLibPath}/libmoldname.a",
    s!"{sysLibPath}/libmingwex.a",
    s!"{sysLibPath}/libucrt.a",

    "-Wl,--end-group",

    -- Windows システム DLL
    "-lmsvcrt", "-lkernel32", "-luser32", "-ladvapi32", "-lshell32"
  ]

lean_exe «graph-enum-claim5» where
  root := `SymmetricTensorProof.GraphEnum.Main
  exeName := "graph-enum-claim5"
  moreLinkArgs := commonLinkArgs

lean_exe «graph-enum-test» where
  root := `SymmetricTensorProof.GraphEnum.Test
  exeName := "graph-enum-test"
  moreLinkArgs := commonLinkArgs

---------------------------------------------------------------------
-- 3. C++ (Nauty) コンパイル設定
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
    "-I", leanIncludeDir.toString,
    "-I", cxxIncludePath1,
    "-I", cxxIncludePath2
  ]

  -- GCCでコンパイル
  let traceArgs := #[
    "-D_WIN32", "-O3", "-std=c++14",
    "-Wno-unused-command-line-argument"
  ]

  buildO oFile srcJob weakArgs traceArgs "c++"

extern_lib liblean_glue pkg := do
  let glueJob ← fetch <| pkg.target ``glue.o
  let buildDir := pkg.buildDir / "native"
  let srcDir := pkg.dir / "native"
  let mut nautyJobs : Array (Job System.FilePath) := #[]

  let nautyTraceArgs := #[
    "-D_WIN32", "-O3", "-DMAXN=64", "-Dflockfile=_lock_file",
    "-Dfunlockfile=_unlock_file", "-Dgetc_unlocked=_getc_nolock",
    "-Dputc_unlocked=_putc_nolock"
  ]
  let nautyWeakArgs := #["-I", srcDir.toString]

  for src in nautySrcs do
    let oFile := buildDir / (src ++ ".o")
    let srcFile := srcDir / src
    let srcJob ← inputFile srcFile false
    let job ← buildO oFile srcJob nautyWeakArgs nautyTraceArgs "clang"
    nautyJobs := nautyJobs.push job

  let libFile := pkg.buildDir / "lib" / "liblean_glue.a"
  buildStaticLib libFile (#[glueJob] ++ nautyJobs)
