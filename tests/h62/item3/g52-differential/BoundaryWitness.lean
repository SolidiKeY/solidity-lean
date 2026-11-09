import Solidity.Tools.SolCases

/-! Guarded regression: half-word/sign-boundary operands and near-maximum pairs
must not be omitted from the admitted real executable primitive witness corpus.
Reuse the existing emitter and Prog.run; no replacement arithmetic oracle.
Original 4x4 operand pairs are excluded, so cases are not padded by replay.
-/
def main (_args : List String) : IO UInt32 := do
  let w : Nat := 2^256
  let h : Nat := 2^255
  let pool : Array Nat := #[0, 1, 2, w-1, h-1, h, h+1, w-2]
  let out ← IO.getStdout
  let mut index := 0
  for i in [:pool.size] do
    for j in [:pool.size] do
      if !(i < 4 && j < 4) then
        for kind in [:10] do
          match Solidity.Tools.SolCases.emit 0 index pool[i]! pool[j]! kind with
          | .ok record => out.putStrLn record.compress
          | .error reason => throw (IO.userError reason)
          index := index + 1
  return 0
