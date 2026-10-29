import Solidity.Tools.SolCases

/-- Deterministic bounded enumeration; seed rotates the boundary pool. stdout is JSONL. -/
def main (args : List String) : IO UInt32 := do
  if args.length > 1 then throw (IO.userError "solcases expects at most one natural seed")
  let some seed := (args[0]?.getD "0").toNat?
    | throw (IO.userError "solcases seed must be a natural number")
  let pool := #[0, 1, 2, 2^256-1]
  let out ← IO.getStdout
  let mut index := 0
  for i in [:pool.size] do
    for j in [:pool.size] do
      for kind in [:10] do
        let a := pool[(i + seed) % pool.size]!
        let b := pool[(j + seed) % pool.size]!
        match Solidity.Tools.SolCases.emit seed index a b kind with
        | .ok record => out.putStrLn record.compress
        | .error reason => throw (IO.userError reason)
        index := index + 1
  return 0
