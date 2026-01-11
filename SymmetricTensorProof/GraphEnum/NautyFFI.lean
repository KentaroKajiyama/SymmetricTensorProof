namespace SymmetricTensorProof

-- 行列の型定義
def AdjMat := ByteArray

-- 【ここを追加】AdjMat がデフォルト値 (空のByteArray) を持つことを教える
instance : Inhabited AdjMat := ⟨ByteArray.empty⟩

-- FFI 1: 読み込み
@[extern "cpp_load_graphs"]
opaque loadGraphs (n : @& Nat) (path : @& String) : IO (Array AdjMat)

-- FFI 2: 同型除去
@[extern "cpp_reduce_iso"]
opaque reduceIso (n : @& Nat) (graphs : @& Array AdjMat) (anchors : @& Array (Fin n)) : Array AdjMat

-- FFI 3: 書き出し
@[extern "cpp_dump_graph6"]
opaque dumpGraph6 (n : @& Nat) (path : @& String) (graphs : @& Array AdjMat) : IO Unit

end SymmetricTensorProof
