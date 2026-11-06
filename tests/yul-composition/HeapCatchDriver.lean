import Solidity.Yul.Composition.HeapCatchPhysical
open Lean Solidity.Yul Solidity.Yul.Composition Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Yul.Composition.LocalPhysicalControls Solidity.Yul.Composition.HeapCatchPhysical

def reference (v : Solidity.Source.Val originEnv.layout (.bytes .memory)) : Json :=
  match v with
  | .memRef _ id => Json.mkObj [("kind",toJson "memory"),("logicalIndex",toJson id)]
  | .storRef bad _ => nomatch bad
  | .cdRef bad _ => nomatch bad

def cell (s : Solidity.Source.St originEnv) (id : Nat) : Json :=
  match s.heap.get id with
  | none => Json.null
  | some ⟨_,.bytes bytes⟩ => Json.mkObj [("kind",toJson "bytes"),("bytes",toJson (bytes.map UInt8.toNat)),("length",toJson bytes.length)]
  | some ⟨_,.val (.bool value)⟩ => Json.mkObj [("kind",toJson "bool"),("value",toJson value)]
  | some _ => Json.mkObj [("kind",toJson "other")]

def haltJson : Solidity.Source.Halt → Json
  | .revert bytes => Json.mkObj [("tag",toJson "revert"),("bytes",toJson (bytes.map UInt8.toNat))]
  | .timeout => Json.mkObj [("tag",toJson "timeout")]
  | .stuck why => Json.mkObj [("tag",toJson "stuck"),("reason",toJson why)]

def resultJson : Except Solidity.Source.Halt (Except Solidity.Source.Halt ((List UInt8) ⊕ (Solidity.Source.Val originEnv.layout (.bytes .memory) × List UInt8))) → Json
  | .error h => Json.mkObj [("outerError",haltJson h)]
  | .ok (.error h) => haltJson h
  | .ok (.ok (.inl bytes)) => Json.mkObj [("tag",toJson "success"),("bytes",toJson (bytes.map UInt8.toNat))]
  | .ok (.ok (.inr (ref,bytes))) => Json.mkObj [("tag",toJson "allocated"),("ref",reference ref),("bytes",toJson (bytes.map UInt8.toNat)),("length",toJson bytes.length)]

def continuedJson (bytes : List UInt8) : Json :=
  match continued bytes 32 with
  | .ok (.ok (some result)) => Json.mkObj [("cells",toJson ((snapshot result.state).map toString)),("normal",toJson result.flow.isNormal),
      ("allocated",cell result.state.2 1),("alias",cell result.state.2 0),("next",toJson result.state.2.heap.next),("clean",toJson (LocalState.clean? result.state).isSome)]
  | _ => Json.mkObj [("unexpected",toJson true)]

def row (name : String) (outcome : Except Solidity.Source.Halt (List UInt8)) : Json :=
  let result := (capture outcome).2
  Json.mkObj [("name",toJson name),("result",resultJson result.1.1),("next",toJson result.2.2.heap.next),
    ("object",cell result.2.2 1),("alias",cell result.2.2 0),
    ("raw",toJson ((snapshot result.2).map toString)),("logs",toJson (result.2.2.logs.map (fun (a,b)=>(toString a.val,b.map UInt8.toNat))))]

def main : IO Unit := do
  let rows := [row "success" (.ok [0xbe,0xef]),row "revert" (.error (.revert [0xde,0xad])),row "empty" (.error (.revert [])),
    row "panic" (Solidity.Source.panic .assert),row "timeout" (.error .timeout),row "stuck" (.error (.stuck "sentinel"))]
  IO.println (Json.mkObj [("schema",toJson (1:Nat)),("addressDomain",toJson "logical-heap-index"),("cases",toJson rows),
    ("continuations",toJson [continuedJson [0xde,0xad],continuedJson [],continuedJson (Solidity.Source.panicData .assert)]),
    ("badAllocation",Json.mkObj [("outcome",match badAllocation.1.1 with | .ok (.error h) => haltJson h | _ => Json.null),
       ("next",toJson badAllocation.2.2.heap.next),("object",cell badAllocation.2.2 1)]),
    ("nonbyteRead",match (Solidity.Source.heapBytes 1 : Solidity.Source.EM originEnv [] _).run (.nil,badAllocation.2.2) with | (.error h,_) => haltJson h | _ => Json.null),
    ("danglingRead",match (Solidity.Source.heapBytes 2 : Solidity.Source.EM originEnv [] _).run (.nil,(allocated [0xde,0xad]).2.2) with | (.error h,_) => haltJson h | _ => Json.null)]).compress
