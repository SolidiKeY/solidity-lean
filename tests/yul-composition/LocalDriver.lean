import Solidity.Yul.Composition.LocalPhysicalControls

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

def nonword : Option Nat := match completed.state.1.get memoryRef.index with
  | .clean (.memRef _ id) => some id
  | _ => none

def heapPayload : Option (List Nat) := match completed.state.2.heap.get 0 with
  | some ⟨_,.bytes bytes⟩ => some (bytes.map UInt8.toNat)
  | _ => none

def main : IO Unit := do
  let fuels := [0,1,2,4,8,16,32]
  let horizons := fuels.map fun fuel => Json.mkObj [("fuel",toJson fuel),("outcome",describe (joint fuel).2)]
  let statics := fuels.map fun fuel => Json.mkObj [("fuel",toJson fuel),("outcome",describe
    (representedThenLocal ctx originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
      {packedStepFrame with static:=true} ownedOriginPlan initial ownedOriginResidual code (policy _) fuel).2)]
  let transfers := [("break",describe (.ok breakRun)),("continue",describe (.ok continueRun)),("leave",describe (.ok leaveRun))]
  let rawResume := LocalState.runClean (Solidity.Source.applyOp packedStepFrame ownedOriginPlan.packed.sourceOp) completed.state
  let sourceLogs := completed.state.2.logs.map (fun (addr,bytes)=>(toString addr.val,bytes.map UInt8.toNat))
  let wrongRead := fun (s : Solidity.Source.St originEnv) =>
    match (s.ex.world.accounts account).storage.read (originPath "c") with
    | some (.bool value) => some value
    | _ => none
  IO.println (Json.mkObj [("schema",toJson (1:Nat)),("cells",toJson ((snapshot completed.state).map toString)),
    ("flow",toJson (flowName completed.flow)),("cleanBridgeAccepted",toJson (LocalState.clean? completed.state).isSome),
    ("rawResumeRefused",toJson rawResume.isNone),("nonwordId",toJson nonword),("heapBytes",toJson heapPayload),
    ("sourceLogs",toJson sourceLogs),("horizons",toJson horizons),("staticHorizons",toJson statics),
    ("transfers",Json.mkObj transfers),("targetBytes",toJson (target.map (fun s=>[s.memory 30,s.memory 31,s.memory 32].map UInt8.toNat))),
    ("physical",Json.mkObj [("first",toJson (rawWord completed.state.2 firstPhysical.1.2 firstPhysical.2)),
      ("child",toJson (rawWord childPhysical.1.1.2.2 childPhysical.1.2 childPhysical.2)),
      ("outer",toJson (rawWord restored.2 revertedCore.residual revertedEncoding))]),
    ("wrongOwner",toJson (wrongOwnerRun.bind (fun out=>wrongRead out.1.1.2.2))),
    ("wrongSlot",toJson (wrongSlotRun.bind (fun out=>wrongRead out.1.1.2.2)))]).compress
