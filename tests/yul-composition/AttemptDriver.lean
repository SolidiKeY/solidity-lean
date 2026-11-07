import Solidity.Yul.Composition.AttemptPhysical
open Lean Solidity.Yul Solidity.Yul.Composition Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Yul.Composition.LocalPhysicalControls Solidity.Yul.Composition.AttemptPhysical

def haltJson : Solidity.Source.Halt → Json
  | .revert bytes => Json.mkObj [("tag",toJson "revert"),("bytes",toJson (bytes.map UInt8.toNat))]
  | .timeout => Json.mkObj [("tag",toJson "timeout")]
  | .stuck why => Json.mkObj [("tag",toJson "stuck"),("reason",toJson why)]
def outcomeJson : Except Solidity.Source.Halt (List UInt8) → Json
  | .ok bytes => Json.mkObj [("tag",toJson "success"),("bytes",toJson (bytes.map UInt8.toNat))]
  | .error h => haltJson h
def routedJson : Except Solidity.Source.Halt ((List UInt8) ⊕ (List UInt8 × Option (LocalBlockOutcome ctx ⟨false,false⟩))) → Json
  | .error h => haltJson h
  | .ok (.inl bytes) => Json.mkObj [("tag",toJson "success"),("bytes",toJson (bytes.map UInt8.toNat))]
  | .ok (.inr (bytes,result)) => Json.mkObj [("tag",toJson "catch"),("bytes",toJson (bytes.map UInt8.toNat)),
      ("cells",toJson (result.map (fun r=>(snapshot r.state).map toString))),("normal",toJson (result.map (fun r=>r.flow.isNormal)))]
def row (name : String) (result : Except Solidity.Source.Halt (List UInt8)) : Json :=
  let actual := AttemptPhysical.run result 32
  Json.mkObj [("name",toJson name),("captured",match actual.1.1.1 with
    | .ok captured => outcomeJson captured
    | .error h => Json.mkObj [("unexpectedOuterHalt",haltJson h)]),
    ("postRaw",toJson ((snapshot actual.1.2).map toString)),
    ("postLogs",toJson (actual.1.2.2.logs.map (fun (a,b)=>(toString a.val,b.map UInt8.toNat)))),
    ("routed",routedJson actual.2)]
def main : IO Unit := do
  let entries := [row "success" (.ok [0xbe,0xef]),row "revert" (.error (.revert [0xde,0xad])),
    row "empty" (.error (.revert [])),row "panic" (Solidity.Source.panic .assert),row "timeout" (.error .timeout),row "stuck" (.error (.stuck "sentinel"))]
  IO.println (Json.mkObj [("schema",toJson (1:Nat)),("inputCells",toJson ((snapshot input).map toString)),
    ("cells",toJson ((snapshot AttemptPhysical.completed.state).map toString)),
    ("emptyCells",toJson ((continued [] 32).map (fun r=>(snapshot r.state).map toString))),
    ("panicCells",toJson ((continued (Solidity.Source.panicData .assert) 32).map (fun r=>(snapshot r.state).map toString))),
    ("sourceLogs",toJson (AttemptPhysical.completed.state.2.logs.map (fun (a,b)=>(toString a.val,b.map UInt8.toNat)))),
    ("rawClean",toJson (LocalState.clean? AttemptPhysical.completed.state).isSome),
    ("nonword",toJson (match AttemptPhysical.completed.state.1.get memoryRef.index with | .clean (.memRef _ id) => some id | _ => none)),
    ("cases",toJson entries),("zeroRevert",routedJson (AttemptPhysical.run (.error (.revert [0xde,0xad])) 0).2)]).compress
