import Solidity.Tools.SolCases

/-!
Executable input driver for the existing typed SolCases adapter. Guards against
mistaking rotated boundary enumeration for random programs. Refusals are JSONL
records and remain in the denominator. This is external testing, not a theorem.
-/

private def next (n : Nat) : Nat := (6364136223846793005 * n + 1442695040888963407) % 2^64

private def word (state : Nat) : Nat × Nat := Id.run do
  let mut s := state
  let mut n := 0
  for _ in [:4] do
    s := next s
    n := n * 2^64 + s
  return (s, n)

private def emit (seed index a b kind : Nat) : IO Unit := do
  let out ← IO.getStdout
  match Solidity.Tools.SolCases.emit seed index a b kind with
  | .ok r => out.putStrLn r.compress
  | .error reason => out.putStrLn (Lean.Json.mkObj [
      ("index", Lean.toJson index), ("seed", Lean.toJson seed),
      ("refusal", Lean.toJson reason)]).compress

def main (args : List String) : IO UInt32 := do
  match args with
  | ["case", seed, index, a, b, kind] =>
    let some seed := seed.toNat? | throw (IO.userError "seed")
    let some index := index.toNat? | throw (IO.userError "index")
    let some a := a.toNat? | throw (IO.userError "a")
    let some b := b.toNat? | throw (IO.userError "b")
    let some kind := kind.toNat? | throw (IO.userError "kind")
    emit seed index a b kind
  | ["sample", seed, count] =>
    let some seed := seed.toNat? | throw (IO.userError "seed")
    let some count := count.toNat? | throw (IO.userError "count")
    if count > 10000 then throw (IO.userError "count exceeds 10000")
    let pool := #[0, 1, 2, 2^256-1]
    let mut s := seed
    for index in [:count] do
      let (s₁, a) := word s
      let (s₂, b) := word s₁
      let familyState := next s₂
      let aState := next familyState
      let bState := next aState
      s := next bState
      -- First twenty are the corpus: each family with zero and max operands.
      let kind := if index < 20 then index % 10 else (familyState / 2^32) % 10
      let a := if index < 20 then pool[index / 10 * 3]! else
        if (aState / 2^32) % 4 == 0 then pool[(aState / 2^34) % 4]! else a
      let b := if index < 20 then pool[3 - index / 10 * 3]! else
        if (bState / 2^32) % 4 == 0 then pool[(bState / 2^34) % 4]! else b
      emit seed index a b kind
  | _ => throw (IO.userError "sample SEED COUNT | case SEED INDEX A B KIND")
  return 0
