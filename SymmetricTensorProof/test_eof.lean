
def main : IO Unit := do
  let handle ← IO.FS.Handle.mk "test_input.txt" IO.FS.Mode.write
  handle.putStrLn "line1"
  handle.putStrLn "line2"
  -- no newline at end of file for line2? putStrLn adds one.
  -- let's try just pure strings

  let handle2 ← IO.FS.Handle.mk "test_input_2.txt" IO.FS.Mode.write
  handle2.putStr "hello"

  let h_read ← IO.FS.Handle.mk "test_input_2.txt" IO.FS.Mode.read
  let l1 ← h_read.getLine
  IO.println s!"Line 1: '{l1}' (len: {l1.length})"
  let l2 ← h_read.getLine
  IO.println s!"Line 2: '{l2}' (len: {l2.length})"
  if l2 == "" then
    IO.println "EOF detected by empty string"
  else
    IO.println "EOF NOT detected"
