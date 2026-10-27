import Solidity.Frontend.Import
import Solidity.Tools.Run
import Solidity.Semantics.RunFuel

/-!
# Replay upstream scalar semantic vectors

The JavaScript adapter reads Solidity's fixture format and supplies ABI-decoded
scalar arguments. This command imports each contract through `solc_import`, then
executes the vectors in order on the typed interpreter, retaining storage and
rolling back failed calls. It reports observations, not proofs. Unsupported
vectors, import gaps and exhausted loop fuel cannot count as passing tests.
-/

namespace Solidity.Tools.Upstream

open Lean Elab Command Meta Frontend

private def str (s : String) : Json := toJson s
private def result (status reason : String) (extra : List (String × Json) := []) : Json :=
  Json.mkObj ([("status", str status), ("reason", str reason)] ++ extra)

/-- Resource failures remain inconclusive even when an importer embeds the
exception text in a per-function row rather than throwing it. -/
def resourceLimited (reason : String) : Bool :=
  ["heartbeats", "maximum recursion", "out of memory"].any fun text =>
    (reason.toLower.splitOn text).length > 1

/-- Preserve all importer diagnostics; an earlier warning cannot hide a
later resource failure. This result never certifies a runtime observation. -/
def diagnosticFailure (messages : List String) : Json :=
  result (if messages.any resourceLimited then "blocked" else "broken")
    ("\n".intercalate messages)

private def argument (j : Json) : Except String RawExpr := do
  let value ← j.getStr?
  if value == "true" then return .bool true
  if value == "false" then return .bool false
  let some n := value.toInt? | throw s!"invalid scalar argument {value}"
  return if n < 0 then .unop .neg (.num n.natAbs) else .num n.toNat

private def word : Semantics.CallValue → Except String String
  | .uint n => pure (toString n.1)
  | .int n => pure (toString (n.1 % (2^256 : Int)))
  | .bool b => pure (if b then "1" else "0")

/-- Resolve source ABI entries by exact canonical signature and compiler identity.
No source-local helper, retained override or special entry is a fallback target.
The row-only path supports native (non-source) replay controls. -/
def resolveEntry (C : Contract) (rows : List ImportRow) (signature : String) : Except String String := do
  let source := C.funs.any fun (_, f) => f.sourceDecl.isSome
  let candidates := if source then C.funs.filterMap fun (name, f) => do
      let identity ← f.sourceDecl
      guard (identity.declaration.isSome && identity.externalEntry &&
        identity.signature == some signature)
      pure name
    else
      let canonical (s : String) := match s.splitOn "(" with
        | [name, args] => name ++ "(" ++
          ((args.replace "uint256" "uint").replace "int256" "int").replace "address payable" "address"
        | _ => s
      rows.filterMap fun r =>
        if canonical r.sourceSignature == canonical signature &&
            (Semantics.lookupBy r.name C.funs).isSome then some r.name else none
  match candidates with
  | [name] => pure name
  | [] => throw s!"no imported ABI entry for {signature}"
  | _ => throw s!"ambiguous imported ABI entry for {signature}"

/-- ABI bounds retained by the source reader, including enum membership.
The JavaScript adapter separately checks canonical word widths. -/
private def inRanges (row : ImportRow) (vector : Json) : Bool := Id.run do
  if row.paramRanges.isEmpty then return true
  let .ok args := vector.getObjValAs? (List String) "args" | return false
  if args.length != row.params.length then return false
  let values := row.params.zip args
  return row.paramRanges.all fun (name, lo, hi) =>
    (values.find? fun ((param, _), _) => param == name).any fun (_, value) =>
      value.toInt?.any fun n => lo ≤ n && n ≤ hi

/-- Replay complete supported vector sequences. Fuel exhaustion is inconclusive. -/
def replay (C : Contract) (rows : List ImportRow) (data : Json) : Json := Id.run do
  let bad := rows.filter fun r => r.status != .elaborated && r.status != .skipped
  if !bad.isEmpty then
    return result (if bad.any (resourceLimited ∘ ImportRow.reason) then "blocked" else "broken") "frontend import gaps" [("gaps", toJson (bad.map fun r =>
      Json.mkObj [("function", str r.sourceSignature), ("status", str r.status.toStr),
        ("reason", str r.reason)]))]
  if let .ok reason := data.getObjValAs? String "blocked" then
    return result "blocked" reason
  let .ok vectors := data.getObjValAs? (Array Json) "vectors"
    | return result "blocked" "missing execution vectors"
  if vectors.isEmpty then return result "blocked" "no execution vectors"
  let tx : TTx := { msgSender := PrimTy.ofIntD .uint 103164821458651970696730694074090566015747358738 }
  let mut state := State.deploy C tx
  let mut deployed := false
  let mut deploymentFailed := false
  let mut observed : Array Json := #[]
  for vector in vectors do
    if deploymentFailed then return result "blocked" "calls after failed deployment need the upstream empty-code host"
    let .ok signature := vector.getObjValAs? String "signature"
      | return result "blocked" "missing signature"
    let .ok args := (vector.getObjValAs? (Array Json) "args").bind fun xs => xs.toList.mapM argument
      | return result "blocked" "unsupported scalar argument"
    let ctor := signature == "constructor"
    if !deployed && !ctor then
      let .ok ⟨_, Q⟩ := ctorProgS C []
        | return result "broken" "default deployment does not elaborate"
      match Prog.runF 1000 Q state with
      | .error .diverge => return result "blocked" "deployment exhausted loop fuel"
      | .error .exhausted => return result "blocked" "deployment reached a model resource bound"
      | .error _ => return result "broken" "unexpected default deployment failure"
      | .ok o => state := o.st.glob
      deployed := true
    let resolved := resolveEntry C rows signature
    let function := resolved.toOption
    let declaration := if ctor then C.ctor else function.bind (Semantics.lookupBy · C.funs)
    if let some declaration := declaration then
      for ((parameter, _), arg) in declaration.params.zip args do
        if (Semantics.lookupBy (parameter ++ "#address") declaration.widths).isSome then
          let some value := arg.litVal?
            | return result "blocked" "non-scalar address ABI argument"
          unless 0 ≤ value && value < 2^160 do
            return result "blocked" "noncanonical address ABI argument"
    let program := if ctor then ctorProgS C args else do
      let name ← resolved
      elabProgS C [← runStmt C name args]
    if let .error reason := program then
      return result "broken" s!"call does not elaborate: {signature}: {reason}"
    let .ok ⟨_, Q⟩ := program
      | return result "blocked" "missing call program"
    let before := state
    let rangeRow := if ctor then rows.find? (·.sourceName == "constructor")
      else function.bind fun name => rows.find? (·.name == name)
    let badRange := rangeRow.any (fun row => !inRanges row vector)
    let outcome := if badRange then .error .revert else if ctor && !((C.ctor.map (·.payable)).getD false) && state.tx.msgValue.1 != 0
      then .error .revert else Prog.runF 1000 Q state
    let actual : Except String (Bool × List String) := do
      match outcome with
      | .error .diverge => throw "execution exhausted loop fuel"
      | .error .exhausted =>
        throw "execution reached a model resource bound (including recursive unrolling); not an EVM failure"
      | .error .revert => pure (true, [])
      | .error (.revertWith bytes) =>
        pure (true, if ctor then [] else [s!"revert-data: {bytes}"])
      | .error .panic =>
        if ctor then pure (true, []) else throw "generic model panic does not retain the ABI panic code"
      | .ok o =>
        let vals := localVals (Q.outNames []) o.st.env
        let count := if ctor then 0 else
          ((function.bind fun f => Semantics.lookupBy f C.funs).map (·.rets.length)).getD 0
        let values ← (List.range count).mapM fun i => do
          let name := if count == 1 then retLocal else s!"{retLocal}{i}"
          let some value := Semantics.lookupBy (Var.ofName name) vals
            | throw s!"missing returned scalar {name}"
          word value
        pure (false, values)
    let .ok (failed, values) := actual
      | return result "blocked" (match actual with
          | .error reason => reason
          | .ok _ => "unsupported execution result")
          [("observed", toJson observed), ("blockedVector", vector)]
    observed := observed.push (Json.mkObj [("signature", str signature),
      ("failed", toJson failed), ("values", toJson values)])
    let .ok expectedFailure := vector.getObjValAs? Bool "failure"
      | return result "blocked" "missing expected outcome"
    let .ok expectedValues := vector.getObjValAs? (List String) "expected"
      | return result "blocked" "missing expected return values"
    if failed != expectedFailure || values != expectedValues then
      return result "broken" s!"runtime expectation mismatch: {signature}"
        [("observed", toJson observed), ("expected", vector)]
    match outcome with
    | .ok o => state := o.st.glob
    | .error _ => state := before
    if ctor then
      deployed := true
      deploymentFailed := failed
  return result "working" "all scalar runtime vectors match" [("observed", toJson observed)]

syntax (name := upstreamBatch) "#upstream_batch " str " to " str : command

@[command_elab upstreamBatch]
def elabUpstreamBatch : CommandElab := fun stx => do
  let input := stx[1].isStrLit?.getD ""
  let output := stx[3].isStrLit?.getD ""
  let cases ← ofExcept ((Json.parse (← IO.FS.readFile input)).bind Json.getArr?)
  let mut results : Array Json := #[]
  for entry in cases do
    let baseline ← get
    let path ← ofExcept (entry.getObjValAs? String "path")
    let outcome ← (do
      try
      let fixture ← ofExcept (entry.getObjValAs? String "fixture")
      let contract ← ofExcept (entry.getObjValAs? String "contract")
      let name := Lean.Name.str `Upstream contract
      let bytes ← IO.FS.readBinFile fixture
      let command := s!"solc_import {toJson fixture |>.compress} hash {hex16 (fnv1a64 bytes)} as Upstream.«{contract}» testing entrypoints"
      let env ← getEnv
      let parsed ← ofExcept (Parser.runParserCategory env `command command)
      elabCommand parsed
      let diagnostics ← ((← get).messages.toList.filter fun message =>
        message.severity == .error || message.severity == .warning).mapM fun message =>
          message.data.toString
      unless diagnostics.isEmpty do return diagnosticFailure diagnostics
      liftTermElabM do
        let term ← `($(mkCIdent ``replay) $(mkCIdent name)
          $(mkCIdent (name ++ `report))
          ((Json.parse $(quote entry.compress)).toOption.getD Json.null))
        let expression ← Term.elabTermEnsuringType term (mkConst ``Json)
        Term.synthesizeSyntheticMVarsNoPostponing
        let expression ← instantiateMVars expression
        unsafe evalExpr Json (mkConst ``Json) expression
      catch ex =>
        let reason ← ex.toMessageData.toString
        let limited := resourceLimited reason
        let status := if limited
          then "blocked" else "broken"
        pure (result status reason) : CommandElabM Json)
    set baseline
    let fields := outcome.getObj?.toOption.map (·.toList) |>.getD []
    let pipeline := (entry.getObjValAs? String "pipeline").toOption.getD "legacy"
    results := results.push (Json.mkObj (("path", str path) :: ("pipeline", str pipeline) :: fields))
    IO.FS.writeFile output (toJson results |>.pretty)

end Solidity.Tools.Upstream
