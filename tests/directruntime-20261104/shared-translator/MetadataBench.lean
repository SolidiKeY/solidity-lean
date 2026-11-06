import Solidity.Frontend.ExecutableAst.Shared.Translate

/-! Serial component measurements in Lean's development evaluator.
No standalone native/WASM runtime or source-equivalence claim is made. -/
open Lean Solidity Solidity.Frontend Solidity.Frontend.ExecutableAst.Shared
private def checked {α : Type} : Except String α → IO α
  | .ok x => pure x | .error e => throw (IO.userError e)
private def measureMetadataSample (label : String) (run : Json → Except String RawExpr)
    (inputs : Array Json) (iterations : Nat) : IO Json := do
  let start ← IO.monoNanosNow
  let mut accepted := 0
  for i in [:iterations] do
    match run inputs[i % inputs.size]! with
    | .ok _ => accepted := accepted + 1
    | .error _ => pure ()
  let elapsed := (← IO.monoNanosNow) - start
  unless accepted == iterations do throw (IO.userError "benchmark input admission changed")
  return Json.mkObj [("phase", toJson label), ("iterations", toJson iterations),
    ("accepted", toJson accepted), ("nanos", toJson elapsed)]
private def benchmark : IO Unit := do
  let fixture ← checked (Json.parse (← IO.FS.readFile "tests/directruntime-20261104/shared-translator/artifacts/h68-bulk/ReaderFixtures.ast.json"))
  let ast ← checked (field fixture "ast")
  let header ← checked (field fixture "header")
  let inputs := ((J.nodes ast).filter fun j => match expression j with
    | .ok _ => true | .error _ => false).toArray
  unless !inputs.isEmpty do throw (IO.userError "empty benchmark inputs")
  let mut samples := #[]
  for _ in [:3] do
    samples := samples.push (← measureMetadataSample "legacyRawDecode" expression inputs 20000)
    samples := samples.push (← measureMetadataSample "wholeRootChecked" checkedExpression inputs 20000)
  let report := Json.mkObj [("scope", "Lean development evaluator; not standalone native/WASM"),
    ("sourceSha256", ← checked (field header "sourceSha256")),
    ("inputExpressions", toJson inputs.size), ("samples", toJson samples)]
  IO.FS.writeFile "tests/directruntime-20261104/shared-translator/artifacts/evidence/metadata-component-bench.json" (report.compress ++ "\n")
  IO.println report.compress
#eval benchmark
