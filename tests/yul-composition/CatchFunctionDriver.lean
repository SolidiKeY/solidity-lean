import Solidity.Yul.Composition.CatchFunctionPhysical
open Lean Solidity.Yul Solidity.Yul.Composition Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Yul.Composition.LocalPhysicalControls
open Solidity.Yul.Composition.CatchFunctionPhysical

def describe {c} : Option (LocalBlockOutcome ctx c) → Json
  | none => Json.mkObj [("tag",toJson "exhausted")]
  | some result => Json.mkObj [("tag",toJson "complete"),("flow",toJson result.flow.isNormal),
      ("cells",toJson ((snapshot result.state).map toString))]
def nonword : Option Nat := match CatchFunctionPhysical.completed.state.1.get memoryRef.index with
  | .clean (.memRef _ id) => some id
  | _ => none
def heapPayload : Option (List Nat) := match CatchFunctionPhysical.completed.state.2.heap.get 0 with
  | some ⟨_,.bytes bytes⟩ => some (bytes.map UInt8.toNat)
  | _ => none
def rawWord (s : Solidity.Source.St originEnv) (r : ResidualJournal complementCarrierOwnership)
    (encoding : BoolEncodingJournal) : Option String :=
  (reencodePersistentSlot (representedBanks originRegistry false encoding) ⟨s.ex,r⟩ account 43).map (fun w=>toString w.val)
def main : IO Unit := do
  let fuels := [0,1,2,4,8,16,32]
  let resumed := LocalState.runClean (Solidity.Source.applyOp packedStepFrame ownedOriginPlan.packed.sourceOp) CatchFunctionPhysical.completed.state
  let logs := CatchFunctionPhysical.completed.state.2.logs.map (fun (a,b)=>(toString a.val,b.map UInt8.toNat))
  let worldLogs := (RawCatchPhysical.reverted [0xde,0xad]).logs.map fun l => Json.mkObj [("emitter",toJson (toString l.emitter.val)),("topics",toJson (l.topics.toList.map (fun w=>toString w.val))),("data",toJson (l.data.map UInt8.toNat))]
  IO.println (Json.mkObj [("schema",toJson (1:Nat)),("cells",toJson ((snapshot CatchFunctionPhysical.completed.state).map toString)),
    ("inputCells",toJson ((snapshot RawCatchPhysical.completed.state).map toString)),
    ("wrongCells",toJson ((CatchFunctionPhysical.run true true 32).map (fun result=>(snapshot result.state).map toString))),
    ("poisonCells",toJson ((CatchFunctionPhysical.run false false 32).map (fun result=>(snapshot result.state).map toString))),
    ("resetCells",toJson ((runFrom true false 32 (LocalState.ofClean LocalPhysicalControls.initial)).map (fun result=>(snapshot result.state).map toString))),
    ("arities",toJson (FunctionPhysical.F.map (fun sig=>[sig.args,sig.rets]))),
    ("flow",toJson CatchFunctionPhysical.completed.flow.isNormal),("cleanBridgeAccepted",toJson (LocalState.clean? CatchFunctionPhysical.completed.state).isSome),
    ("rawResumeRefused",toJson resumed.isNone),("nonwordId",toJson nonword),("heapBytes",toJson heapPayload),("sourceLogs",toJson logs),
    ("horizons",toJson (fuels.map fun fuel => Json.mkObj [("fuel",toJson fuel),("outcome",describe (CatchFunctionPhysical.run true false fuel))])),
    ("journalLengths",Json.mkObj [("residual",toJson LocalPhysicalControls.firstPhysical.1.2.journal.length),("owned",toJson LocalPhysicalControls.firstPhysical.2.journal.length),
      ("childResidual",toJson childPhysical.1.2.journal.length),("childOwned",toJson childPhysical.2.journal.length),
      ("outerResidual",toJson revertedCore.residual.journal.length),("outerOwned",toJson revertedEncoding.journal.length)]),
    ("targetBytes",toJson ((RawCatchPhysical.failureCopy [0xde,0xad]).map (fun out=>[out.2.memory 30,out.2.memory 31,out.2.memory 32,out.2.memory 33].map UInt8.toNat))),
    ("emptyTargetBytes",toJson ((RawCatchPhysical.failureCopy []).map (fun out=>[out.2.memory 30,out.2.memory 31,out.2.memory 32].map UInt8.toNat))),
    ("caughtBytes",toJson ((RawCatchPhysical.reverted [0xde,0xad]).returndata.map UInt8.toNat)),("emptyCaughtBytes",toJson ((RawCatchPhysical.reverted []).returndata.map UInt8.toNat)),("worldLogs",toJson worldLogs),
    ("physical",Json.mkObj [("child",toJson (rawWord childPhysical.1.1.2.2 childPhysical.1.2 childPhysical.2)),
      ("outer",toJson (rawWord CatchFunctionPhysical.completed.state.2 revertedCore.residual revertedEncoding))])]).compress
