import Solidity.Yul.Composition.RawCatchPhysical
open Lean Solidity.Yul Solidity.Yul.Composition Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Yul.Composition.LocalPhysicalControls
open Solidity.Yul.Composition.RawCatchPhysical

def describe {c} : Option (LocalBlockOutcome ctx c) → Json
  | none => Json.mkObj [("tag",toJson "exhausted")]
  | some result => Json.mkObj [("tag",toJson "complete"),("flow",toJson result.flow.isNormal),
      ("cells",toJson ((snapshot result.state).map toString))]
def nonword : Option Nat := match RawCatchPhysical.completed.state.1.get memoryRef.index with
  | .clean (.memRef _ id) => some id
  | _ => none
def heapPayload : Option (List Nat) := match RawCatchPhysical.completed.state.2.heap.get 0 with
  | some ⟨_,.bytes bytes⟩ => some (bytes.map UInt8.toNat)
  | _ => none
def rawWord (s : Solidity.Source.St originEnv) (r : ResidualJournal complementCarrierOwnership)
    (encoding : BoolEncodingJournal) : Option String :=
  (reencodePersistentSlot (representedBanks originRegistry false encoding) ⟨s.ex,r⟩ account 43).map (fun w=>toString w.val)
def main : IO Unit := do
  let fuels := [0,1,2,4,8,16,32]
  let resumed := LocalState.runClean (Solidity.Source.applyOp packedStepFrame ownedOriginPlan.packed.sourceOp) RawCatchPhysical.completed.state
  let logs := RawCatchPhysical.completed.state.2.logs.map (fun (a,b)=>(toString a.val,b.map UInt8.toNat))
  let worldLogs := (reverted [0xde,0xad]).logs.map fun l => Json.mkObj [("emitter",toJson (toString l.emitter.val)),("topics",toJson (l.topics.toList.map (fun w=>toString w.val))),("data",toJson (l.data.map UInt8.toNat))]
  IO.println (Json.mkObj [("schema",toJson (1:Nat)),("cells",toJson ((snapshot RawCatchPhysical.completed.state).map toString)),
    ("prefixCells",toJson ((snapshot callerPrefix).map toString)),("rollbackCells",toJson ((snapshot afterRollback).map toString)),
    ("flow",toJson RawCatchPhysical.completed.flow.isNormal),("cleanBridgeAccepted",toJson (LocalState.clean? RawCatchPhysical.completed.state).isSome),
    ("rawResumeRefused",toJson resumed.isNone),("nonwordId",toJson nonword),("heapBytes",toJson heapPayload),("sourceLogs",toJson logs),
    ("horizons",toJson (fuels.map fun fuel => Json.mkObj [("fuel",toJson fuel),("outcome",describe (runCatch fuel))])),
    ("journalLengths",Json.mkObj [("residual",toJson LocalPhysicalControls.firstPhysical.1.2.journal.length),("owned",toJson LocalPhysicalControls.firstPhysical.2.journal.length),
      ("childResidual",toJson childPhysical.1.2.journal.length),("childOwned",toJson childPhysical.2.journal.length),
      ("outerResidual",toJson revertedCore.residual.journal.length),("outerOwned",toJson revertedEncoding.journal.length)]),
    ("targetBytes",toJson ((failureCopy [0xde,0xad]).map (fun out=>[out.2.memory 30,out.2.memory 31,out.2.memory 32,out.2.memory 33].map UInt8.toNat))),
    ("emptyTargetBytes",toJson ((failureCopy []).map (fun out=>[out.2.memory 30,out.2.memory 31,out.2.memory 32].map UInt8.toNat))),
    ("caughtBytes",toJson ((reverted [0xde,0xad]).returndata.map UInt8.toNat)),("emptyCaughtBytes",toJson ((reverted []).returndata.map UInt8.toNat)),("worldLogs",toJson worldLogs),
    ("physical",Json.mkObj [("child",toJson (rawWord childPhysical.1.1.2.2 childPhysical.1.2 childPhysical.2)),
      ("outer",toJson (rawWord RawCatchPhysical.completed.state.2 revertedCore.residual revertedEncoding))])]).compress
