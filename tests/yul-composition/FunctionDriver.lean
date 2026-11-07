import Solidity.Yul.Composition.FunctionPhysical

/-! Actual producer executions. Null is missing evidence, never zero.
The runner validates these finite projections separately from kernel laws. -/
open Lean Solidity.Yul Solidity.Yul.Composition Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Yul.Composition.LocalPhysicalControls

def flowName {c} : Closed.Flow c → String
  | .normal => "normal"
  | .leave_ _ => "leave"
  | .break_ _ => "break"
  | .continue_ _ => "continue"

def describe {c} : Except Solidity.Source.Halt (Option (LocalBlockOutcome ctx c)) → Json
  | .error (.revert bytes) => Json.mkObj [("tag",toJson "halt"),("reason",toJson "revert"),("bytes",toJson (bytes.map UInt8.toNat))]
  | .error _ => Json.mkObj [("tag",toJson "unexpected-halt")]
  | .ok none => Json.mkObj [("tag",toJson "exhausted")]
  | .ok (some result) => Json.mkObj [("tag",toJson "complete"),("flow",toJson (flowName result.flow)),
      ("cells",toJson ((snapshot result.state).map toString))]

def rawWord (s : Solidity.Source.St originEnv) (r : ResidualJournal complementCarrierOwnership)
    (encoding : BoolEncodingJournal) : Option String :=
  (reencodePersistentSlot (representedBanks originRegistry false encoding) ⟨s.ex,r⟩ account 43).map (fun w=>toString w.val)

def nonword : Option Nat := match Solidity.Yul.Composition.FunctionPhysical.completed.state.1.get memoryRef.index with
  | .clean (.memRef _ id) => some id
  | _ => none

def heapPayload : Option (List Nat) := match Solidity.Yul.Composition.FunctionPhysical.completed.state.2.heap.get 0 with
  | some ⟨_,.bytes bytes⟩ => some (bytes.map UInt8.toNat)
  | _ => none

def main : IO Unit := do
  let fuels := [0,1,2,4,8,16,32]
  let horizons := fuels.map fun fuel => Json.mkObj [("fuel",toJson fuel),("outcome",describe (Solidity.Yul.Composition.FunctionPhysical.joint fuel).2)]
  let statics := fuels.map fun fuel => Json.mkObj [("fuel",toJson fuel),("outcome",describe
    (representedThenLocal ctx originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
      {packedStepFrame with static:=true} ownedOriginPlan initial ownedOriginResidual (Solidity.Yul.Composition.FunctionPhysical.code true false) (Solidity.Yul.Composition.FunctionPhysical.policy true false) fuel).2)]
  let rawResume := LocalState.runClean (Solidity.Source.applyOp packedStepFrame ownedOriginPlan.packed.sourceOp) Solidity.Yul.Composition.FunctionPhysical.completed.state
  let sourceLogs := Solidity.Yul.Composition.FunctionPhysical.completed.state.2.logs.map (fun (addr,bytes)=>(toString addr.val,bytes.map UInt8.toNat))
  let wrongRead := fun (s : Solidity.Source.St originEnv) =>
    match (s.ex.world.accounts account).storage.read (originPath "c") with
    | some (.bool value) => some value
    | _ => none
  IO.println (Json.mkObj [("schema",toJson (1:Nat)),("cells",toJson ((snapshot Solidity.Yul.Composition.FunctionPhysical.completed.state).map toString)),
    ("flow",toJson (flowName Solidity.Yul.Composition.FunctionPhysical.completed.flow)),("cleanBridgeAccepted",toJson (LocalState.clean? Solidity.Yul.Composition.FunctionPhysical.completed.state).isSome),
    ("rawResumeRefused",toJson rawResume.isNone),("nonwordId",toJson nonword),("heapBytes",toJson heapPayload),
    ("sourceLogs",toJson sourceLogs),("horizons",toJson horizons),("staticHorizons",toJson statics),
    ("arities",toJson (Solidity.Yul.Composition.FunctionPhysical.F.map (fun sig=>[sig.args,sig.rets]))),
    ("wrongCells",toJson ((Solidity.Yul.Composition.FunctionPhysical.run true true 32).map (fun result=>(snapshot result.state).map toString))),
    ("noLeaveCells",toJson ((Solidity.Yul.Composition.FunctionPhysical.run false false 32).map (fun result=>(snapshot result.state).map toString))),
    ("journalLengths",Json.mkObj [("residual",toJson Solidity.Yul.Composition.LocalPhysicalControls.firstPhysical.1.2.journal.length),("owned",toJson Solidity.Yul.Composition.LocalPhysicalControls.firstPhysical.2.journal.length),
      ("childResidual",toJson childPhysical.1.2.journal.length),("childOwned",toJson childPhysical.2.journal.length),
      ("outerResidual",toJson revertedCore.residual.journal.length),("outerOwned",toJson revertedEncoding.journal.length)]),("targetBytes",toJson (target.map (fun s=>[s.memory 30,s.memory 31,s.memory 32].map UInt8.toNat))),
    ("physical",Json.mkObj [("first",toJson (rawWord Solidity.Yul.Composition.FunctionPhysical.completed.state.2 Solidity.Yul.Composition.LocalPhysicalControls.firstPhysical.1.2 Solidity.Yul.Composition.LocalPhysicalControls.firstPhysical.2)),
      ("child",toJson (rawWord childPhysical.1.1.2.2 childPhysical.1.2 childPhysical.2)),
      ("outer",toJson (rawWord restored.2 revertedCore.residual revertedEncoding))]),
    ("wrongOwner",toJson (wrongOwnerRun.bind (fun out=>wrongRead out.1.1.2.2))),
    ("wrongSlot",toJson (wrongSlotRun.bind (fun out=>wrongRead out.1.1.2.2)))]).compress
