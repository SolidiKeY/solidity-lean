import Solidity.Frontend.ExecutableAst.ControlTuple.Adapter
import Solidity.Syntax.Splice
import Solidity.Semantics.RunFuel

/-! External native fixture probe. No Lean Environment, serialized environment,
kernel, command elaboration or tactics are invoked by main. This tests existing
intrinsic model execution, not EVM/source equivalence or verifier completeness. -/
open Lean Solidity Solidity.Semantics
open Solidity.Frontend.ExecutableAst

private def localValues {C : Contract} {H : HTy} : (Γ : Ctx) → TEnv C H Γ → List (Option String)
  | [], _ => []
  | .val .bool :: Γ, (v, vs) => some (Bool.casesOn (show Bool from v) "false" "true") :: localValues Γ vs
  | .val .uint :: Γ, (v, vs) => some (toString v.1) :: localValues Γ vs
  | .val .int :: Γ, (v, vs) => some (toString v.1) :: localValues Γ vs
  | _ :: Γ, (_, vs) => none :: localValues Γ vs

private def rawType : Ty → Except String RawTy
  | .prim p => .ok (.named p.toStr)
  | _ => .error "probe only observes primitive returns"

private def execute (base : Contract) (j : Json) (args : List RawExpr) : Except String (List String) := do
  let (name, d) ← Shared.function ControlTuple.reader j j.compress
  let C := { base with funs := [(name, d)] }
  let call := RawExpr.call name args
  let vs ← d.rets.zipIdx.mapM fun ((_, t), i) => do
    return some (← rawType t, s!"probe{i}")
  let raw ← match vs with
    | [some (t, n)] => pure [RawStmt.decl t n (some call)]
    | _ => pure [RawStmt.tupleDecl vs call]
  let ⟨Γ, program⟩ ← elabProgS C raw
  match program.runF 1000 (State.init C) with
  | .error .revert => throw "model halted: revert"
  | .error halt => throw s!"unexpected model halt: {repr halt}"
  | .ok outcome =>
    let pairs := (program.outNames []).zip (localValues Γ outcome.st.env)
    d.rets.zipIdx.mapM fun (_, i) => do
      let some (_, some v) := pairs.find? (fun (n, _) => toString n == s!"probe{i}")
        | throw "probe output missing"
      return v

private def run : IO Unit := do
  let fixture ← IO.ofExcept (Json.parse (← IO.FS.readFile
    "tests/directruntime-20261104/control-tuples/Controls.ast.json"))
  let ast ← IO.ofExcept (fixture.getObjVal? "ast")
  let nodes ← IO.ofExcept (ast.getObjValAs? (Array Json) "nodes")
  let some source := nodes.find? (fun j => (j.getObjValAs? String "name").toOption == some "ControlTuples")
    | throw (IO.userError "fixture contract missing")
  let base ← IO.ofExcept (Shared.contract ControlTuple.reader source)
  let nodes ← IO.ofExcept (source.getObjValAs? (Array Json) "nodes")
  for (name, args, expected) in [
      ("executeFirst", [], ["1"]), ("whileZero", [], ["0"]),
      ("continueTest", [], ["2"]), ("breakTest", [], ["1"]),
      ("earlyReturn", [], ["7"]), ("swap", [.num 1, .num 2], ["2", "1"]),
      ("declaration", [], ["3", "true"]), ("skipped", [.num 0], ["5"]),
      ("repeated", [.num 0], ["1"])] do
    let some j := nodes.find? (fun j => (j.getObjValAs? String "name").toOption == some name)
      | throw (IO.userError s!"missing {name}")
    let actual ← IO.ofExcept (execute base j args)
    unless actual == expected do throw (IO.userError s!"{name}: {repr actual}, expected {repr expected}")
    IO.println s!"MODEL_PASS {name}: {repr actual}"
  for name in ["aliased", "sideEffect", "inlineArray", "callTuple"] do
    let some j := nodes.find? (fun j => (j.getObjValAs? String "name").toOption == some name)
      | throw (IO.userError s!"missing {name}")
    match Shared.function ControlTuple.reader j source.compress with
    | .error reason => IO.println s!"UNKNOWN {name}: {reason}"
    | .ok _ => throw (IO.userError s!"unexpected admission: {name}")

private def runFailureAlias : IO Unit := do
  let fixture ← IO.ofExcept (Json.parse (← IO.FS.readFile
    "tests/directruntime-20261104/control-tuples/FailureAlias.ast.json"))
  let ast ← IO.ofExcept (fixture.getObjVal? "ast")
  let nodes ← IO.ofExcept (ast.getObjValAs? (Array Json) "nodes")
  let some source := nodes.find? (fun j => (j.getObjValAs? String "name").toOption == some "ControlTupleFailureAlias")
    | throw (IO.userError "failure/alias contract missing")
  let base ← IO.ofExcept (Shared.contract ControlTuple.reader source)
  let nodes ← IO.ofExcept (source.getObjValAs? (Array Json) "nodes")
  let some stable := nodes.find? (fun j => (j.getObjValAs? String "name").toOption == some "stableAlias")
    | throw (IO.userError "stableAlias missing")
  let stableResult ← IO.ofExcept (execute base stable [])
  unless stableResult == ["1"] do throw (IO.userError "stable alias write order")
  IO.println "MODEL_PASS stableAlias: repeated literal-index target returns 1"
  let some dynamic := nodes.find? (fun j => (j.getObjValAs? String "name").toOption == some "dynamicAlias")
    | throw (IO.userError "dynamicAlias missing")
  let _ ← IO.ofExcept (Shared.function ControlTuple.reader dynamic source.compress)
  match execute base dynamic [.num 0] with
  | .error reason =>
    unless (reason.splitOn "two targets that are not stack locals").length > 1 do
      throw (IO.userError s!"unexpected dynamic alias refusal: {reason}")
    IO.println s!"INTRINSIC_UNKNOWN dynamicAlias after reader admission: {reason}"
  | .ok _ => throw (IO.userError "dynamic aliases unexpectedly admitted intrinsically")
  let some failing := nodes.find? (fun j => (j.getObjValAs? String "name").toOption == some "discardedFailure")
    | throw (IO.userError "discardedFailure missing")
  let success ← IO.ofExcept (execute base failing [.num 1])
  unless success == ["2"] do throw (IO.userError "discarded division success")
  match execute base failing [.num 0] with
  | .error reason =>
    unless reason == "model halted: revert" do throw (IO.userError s!"not a model halt: {reason}")
    IO.println s!"MODEL_FAIL_PRESERVED discardedFailure(0): {reason}"
  | .ok _ => throw (IO.userError "discarded failing operand was skipped")
  IO.println "MODEL_PASS discardedFailure(1): returns 2"

def main : IO Unit := do
  run
  runFailureAlias
