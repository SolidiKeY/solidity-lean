import Solidity.Tools.Upstream
import Solidity.Semantics.Lifetime

/-! Diagnostic only. Zero-argument ABI-resolved source actions, actual Lifetime
entry guard and payment interface. No independently implemented payment guard.
Loop/recursion-free source is required by the caller; System.run uses Prog.run.
Funding is an explicit environment assumption checked by this diagnostic, not
an additional claimed capability of Lifetime or an EVM execution. -/
namespace BaselineValue
open Lean Solidity Solidity.Frontend Solidity.Tools Solidity.Tools.Upstream
open Solidity.Lifetime

structure Action (C : Contract) where
  signature : String
  name : String
  sourceId : Int
  payable : Bool
  body : Prog C [] []

def action (C : Contract) (rows : List ImportRow) (signature : String) : Except String (Action C) := do
  let name ← resolveEntry C rows signature
  let some d := Semantics.lookupBy name C.funs | throw "resolved declaration absent"
  let some identity := d.sourceDecl | throw "source identity absent"
  unless identity.externalEntry && identity.signature == some signature do
    throw "resolved source ABI identity does not match"
  let candidates := rows.filter fun r => r.name == name && r.sourceSignature == signature
  let [row] := candidates | throw "unique imported report row absent"
  unless row.status == .elaborated && row.admissionChecked && row.sourceId >= 0 do
    throw "entry lacks admitted modern typed report"
  unless identity.declaration == some row.sourceId do throw "compiler declaration identity disagreement"
  unless row.payable == d.payable do throw "payability metadata disagreement"
  unless d.params.isEmpty && d.rets.isEmpty do throw "diagnostic supports only zero-argument void ABI entries"
  let ⟨_, body⟩ ← entryProg C [← runStmt C name []]
  pure ⟨signature, name, row.sourceId, d.payable, .cons (.block body) .nil⟩

def worldJson {C : Contract} (w : World C) : Json := Json.mkObj [
  ("storage", toJson (fmtStorage C w.storage)),
  ("balance", toJson (toString w.balance.1)),
  ("ledger", toJson (w.net.map fun (a,n) => Json.mkObj [("address",toJson (toString a.1)),("amount",toJson (toString n))])),
  ("selfAddress", toJson (toString w.address.1)), ("timestamp",toJson (toString w.timestamp.1))]

def txJson (tx : TTx) : Json := Json.mkObj [
  ("sender",toJson (toString tx.msgSender.1)),("value",toJson (toString tx.msgValue.1)),
  ("selfAddress",toJson (toString tx.selfAddress.1)),("timestamp",toJson (toString tx.timestamp.1))]

def run (C : Contract) (rows : List ImportRow) : Except String Json := do
  unless (rows.filter fun r => r.status != .elaborated && r.status != .skipped).isEmpty do
    throw "frontend import gaps; no runtime execution"
  let deployTx : TTx := { msgSender := PrimTy.ofIntD .uint 7, selfAddress := PrimTy.ofIntD .uint 9 }
  let some ctor := C.ctor | throw "explicit imported constructor absent"
  unless !ctor.payable do throw "unexpected constructor metadata"
  let ⟨_, constructor⟩ ← entryProg C [.call (.name "constructor") []]
  let closedConstructor : Prog C [] [] := .cons (.block constructor) .nil
  let .ok initial := C.deployT closedConstructor deployTx | throw "actual imported deployment failed"
  let mut world := World.ofState initial
  let deployed := worldJson world
  let mut funds : Int := 100
  let mut observations : Array Json := #[]
  let tests : List (String × Nat) := [("nonpayableEntry()",0),("nonpayableEntry()",1),
    ("payableEntry()",5),("writeFail()",2),("internalCall()",3),("nonpayableEntry()",1),("ordinary()",1),("ordinary()",0)]
  for ((signature, value), index) in tests.zipIdx do
    let a ← action C rows signature
    let model : System C Unit (Action C) := {
      deploy := fun _ => closedConstructor, call := Action.body, payable := Action.payable }
    let tx : TTx := { deployTx with
      msgValue := PrimTy.ofIntD .uint (Int.ofNat value)
      timestamp := PrimTy.ofIntD .uint (Int.ofNat (index+1)) }
    let accepted := tx.selfAddress == world.address && world.timestamp.1 <= tx.timestamp.1 && tx.msgSender != world.address
    unless accepted do throw "World.accepts premises fail"
    unless tx.msgValue.1 <= funds do throw "explicit environment funding assumption fails"
    let before := worldJson world
    let outcome := model.run world a tx
    let (failed, bytes) ← match outcome with
      | .ok next => do
        world := next
        funds := funds - tx.msgValue.1
        pure (false, ([] : List Nat))
      | .error .revert => do
        world := world.atTime tx.timestamp
        pure (true, [])
      | .error (.revertWith data) => do
        world := world.atTime tx.timestamp
        pure (true, data.map UInt8.toNat)
      | .error e => throw s!"inconclusive model halt: {fmtHalt e}"
    observations := observations.push (Json.mkObj [
      ("signature",toJson signature),("resolvedName",toJson a.name),("sourceId",toJson a.sourceId),
      ("payableFromDeclarationAndRow",toJson a.payable),("tx",txJson tx),("acceptedPremises",toJson accepted),
      ("fundingAssumptionRemaining",toJson (toString funds)),("before",before),
      ("failed",toJson failed),("revertBytes",toJson bytes),("runReturnedWorld",toJson (!failed)),
      ("after",worldJson world),("failurePolicy",toJson (if failed then "retain prior World.atTime under existing Step.rollback relation; run returned no world" else "commit actual System.run world"))])
  let refusal := match action C rows "helper()" with
    | .error reason => Json.mkObj [("refused",toJson true),("reason",toJson reason)]
    | .ok _ => Json.mkObj [("refused",toJson false)]
  pure (Json.mkObj [("deployed",deployed),("observed",toJson observations),("internalOnlyAbi",refusal),
    ("fundingPolicy",toJson "Explicit assumed caller funds100, updated only on successful payments. Lifetime does not model environment spendable balances."),
    ("runtimeEvidenceNotUniversalProof",toJson true)])

end BaselineValue
