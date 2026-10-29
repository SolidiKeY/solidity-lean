import Solidity.Frontend.PaymentImport

/-! # Ordered source observations through certified payment composition
Gas rows are retained as independent bytecode obligations, never Lean gas
claims. Resource stops and source-plan admission failures stay blocked. -/
namespace Solidity.Tools.PaymentReplay
open Lean Elab Command Meta
open Solidity.ContractWorld Solidity.Frontend.PaymentSource
private def sender : Address := ⟨⟨100, by decide +kernel⟩, by decide +kernel⟩
private def ownerAddress : Address := ⟨⟨200, by decide +kernel⟩, by decide +kernel⟩
private def recipientAddress : Address := ⟨⟨300, by decide +kernel⟩, by decide +kernel⟩
private def funding (a : Address) : Word :=
  if a = sender then ⟨10^30, by decide +kernel⟩ else PrimTy.dflt .uint
private def result (status reason : String) (observed : Array Json := #[]) : Json :=
  Json.mkObj [("status", toJson status), ("reason", toJson reason), ("observed", toJson observed)]

/-- Actual typed frame outcomes are computed before expected values are read. -/
def replay {K : Type} [DecidableEq K] {contracts : K → Contract} {owner recipient : K}
    (model : Interface contracts owner recipient) (data : Json) : Json := Id.run do
  let .ok vectors := data.getObjValAs? (Array Json) "vectors"
    | return result "blocked" "missing payment vectors"
  let mut w := World.empty contracts funding
  let mut handles : Option (Handle owner × Option (Handle recipient)) := none
  let mut observed : Array Json := #[]
  let mut deploymentFailed := false
  let mut createdOnce := false
  for v in vectors do
    if deploymentFailed then return result "blocked" "calls after failed source deployment are not adapted" observed
    let .ok signature := v.getObjValAs? String "signature"
      | return result "blocked" "missing signature" observed
    let .ok value := v.getObjValAs? String "value"
      | return result "blocked" "missing incoming value" observed
    let some n := value.toInt? | return result "blocked" "invalid incoming value" observed
    let some payment := PrimTy.ofInt? .uint n | return result "blocked" "incoming value outside uint256" observed
    let ctx : ContractWorld.Context := { sender := sender, mode := .ordinary payment }
    if handles.isNone && signature != "constructor" then
      match model.deploy w ownerAddress recipientAddress {sender := sender} with
      | .error _ => return result "blocked" "implicit source deployment failed" observed
      | .ok (next, refs) => w := next; handles := some refs
    if model.createsPerCall && createdOnce && signature != "constructor" then
      return result "blocked" "repeated source creation needs fresh-address allocation" observed
    let before := w
    let deployment := if signature == "constructor" && handles.isNone then
      some (model.deploy w ownerAddress recipientAddress ctx) else none
    let outcome : TRes (World contracts × List String) :=
      if signature == "constructor" then
        match deployment with
        | none => .error .exhausted
        | some (.error e) => .error e
        | some (.ok (next, _)) => .ok (next, [])
      else match handles with
        | none => .error .exhausted
        | some (self, target) => model.invoke w self target ctx recipientAddress signature
    let actual : Bool × List String × List Nat := match outcome with
      | .ok (_, values) => (false, values, [])
      | .error e => (true, [], e.data.map UInt8.toNat)
    if let .error e := outcome then
      if !catchable e then return result "blocked" "payment source exhausted or diverged" observed
    let committed := match outcome with | .ok (next, _) => next | .error _ => before
    observed := observed.push (Json.mkObj [("signature", toJson signature),
      ("failed", toJson actual.1), ("values", toJson actual.2.1),
      ("revertBytes", toJson actual.2.2), ("returnBytes", toJson ([] : List Nat)),
      ("worldAfter", Json.mkObj [("senderBalance", toJson (toString (committed.balance sender).1)),
        ("ownerBalance", toJson (toString (committed.balance ownerAddress).1)),
        ("recipientBalance", toJson (toString (committed.balance recipientAddress).1)),
        ("ownerInstalled", toJson (committed.accounts ownerAddress).isSome),
        ("recipientInstalled", toJson (committed.accounts recipientAddress).isSome)])])
    let .ok failed := v.getObjValAs? Bool "failure"
      | return result "blocked" "missing expected failure" observed
    let .ok values := v.getObjValAs? (List String) "expected"
      | return result "blocked" "missing expected values" observed
    let .ok bytes := v.getObjValAs? (List Nat) "revertBytes"
      | return result "blocked" "missing expected failure bytes" observed
    if actual != (failed, values, bytes) then
      return result "broken" ("payment source observation mismatch: " ++ signature) observed
    match outcome with
    | .error _ =>
      w := before
      if signature == "constructor" then deploymentFailed := true
    | .ok (next, _) =>
      w := next
      if signature == "constructor" then
        match deployment with
        | some (.ok (_, refs)) => handles := some refs
        | _ => return result "blocked" "deployment witness mismatch" observed
      else if model.createsPerCall then createdOnce := true
  return Json.mkObj [("status", toJson ("working" : String)),
    ("reason", toJson ("all ordered functional payment source observations match actual typed world frames" : String)),
    ("observed", toJson observed),
    ("originalOrderedObservations", (data.getObjVal? "originalOrderedObservations").toOption.getD Json.null),
    ("independentGasObservations", (data.getObjVal? "independentGasObservations").toOption.getD Json.null),
    ("scope", toJson ("unmetered deterministic typed source/world composition; gas validated only by independent bytecode replay; legacy callback semantics unchanged" : String))]

syntax (name := paymentBatch) "#payment_batch " str " to " str : command
@[command_elab paymentBatch]
def elabPaymentBatch : CommandElab := fun stx => do
  let input := stx[1].isStrLit?.getD ""
  let output := stx[3].isStrLit?.getD ""
  let entries ← ofExcept ((Json.parse (← IO.FS.readFile input)).bind Json.getArr?)
  let mut results : Array Json := #[]
  for entry in entries do
    if (entry.getObjValAs? Bool "paymentSource").toOption != some true then
      let ordinaryInput := input ++ ".ordinary.json"
      let ordinaryOutput := output ++ ".ordinary.json"
      IO.FS.writeFile ordinaryInput (toJson #[entry] |>.compress)
      elabCommand (← `(#upstream_batch $(quote ordinaryInput) to $(quote ordinaryOutput)))
      let rows ← ofExcept ((Json.parse (← IO.FS.readFile ordinaryOutput)).bind Json.getArr?)
      results := results ++ rows
    else
      let baseline ← get
      let outcome ← (do
        try
        let fixture ← ofExcept (entry.getObjValAs? String "fixture")
        let bytes ← IO.FS.readBinFile fixture
        let cmd := s!"solc_payment_source {toJson fixture |>.compress} hash {(Frontend.fnv1a64 bytes).toNat} as PaymentCase"
        elabCommand (← ofExcept (Parser.runParserCategory (← getEnv) `command cmd))
        let errors ← ((← get).messages.toList.filter (fun m => m.severity == .error)).mapM (fun m => m.data.toString)
        unless errors.isEmpty do return result "blocked" (String.intercalate "\n" errors)
        liftTermElabM do
          let term ← `($(mkCIdent ``replay) $(mkCIdent `PaymentCase.interface)
            ((Json.parse $(quote entry.compress)).toOption.getD Json.null))
          let e ← Term.elabTermEnsuringType term (mkConst ``Json)
          Term.synthesizeSyntheticMVarsNoPostponing
          let e ← instantiateMVars e
          unsafe evalExpr Json (mkConst ``Json) e
        catch ex => pure (result "blocked" (← ex.toMessageData.toString)) : CommandElabM Json)
      set baseline
      let fields := outcome.getObj?.toOption.map (·.toList) |>.getD []
      results := results.push (Json.mkObj (("path", (entry.getObjVal? "path").toOption.getD Json.null) ::
        ("pipeline", (entry.getObjVal? "pipeline").toOption.getD Json.null) :: fields))
    IO.FS.writeFile output (toJson results |>.pretty)
end Solidity.Tools.PaymentReplay
