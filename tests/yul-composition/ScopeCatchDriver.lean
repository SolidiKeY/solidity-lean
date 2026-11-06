import Solidity.Yul.Composition.ScopeCatchPhysical
open Lean Solidity.Yul Solidity.Yul.Composition Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Yul.Composition.LocalPhysicalControls Solidity.Yul.Composition.ScopeCatchPhysical
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


def refs (values : Solidity.Source.Locals originEnv.layout Inner) : List Json :=
  [reference (values.get .here),reference (values.get (.there .here))]
def resultJson : Except Solidity.Source.Halt (Except Solidity.Source.Halt ((List UInt8) ⊕ (Solidity.Source.Val originEnv.layout (.bytes .memory) × (List UInt8 × Solidity.Source.Locals originEnv.layout Inner)))) → Json
  | .error h => Json.mkObj [("outerError",haltJson h)]
  | .ok (.error h) => haltJson h
  | .ok (.ok (.inl bytes)) => Json.mkObj [("tag",toJson "success"),("bytes",toJson (bytes.map UInt8.toNat))]
  | .ok (.ok (.inr (ref,(bytes,values)))) => Json.mkObj [("tag",toJson "scoped"),("ref",reference ref),("bytes",toJson (bytes.map UInt8.toNat)),("length",toJson bytes.length),("inner",toJson (refs values))]
def row (name : String) (outcome : Except Solidity.Source.Halt (List UInt8)) : Json :=
  let execution := (ScopeCatchPhysical.run outcome).2
  Json.mkObj [("name",toJson name),("result",resultJson execution.1.1),
    ("restored",reference (execution.1.2.1.get .here)),("raw",toJson ((snapshot execution.2).map toString)),
    ("next",toJson execution.2.2.heap.next),("object",cell execution.2.2 1),("alias",cell execution.2.2 0),
    ("logs",toJson (execution.2.2.logs.map (fun (a,b)=>(toString a.val,b.map UInt8.toNat))))]
def continuationJson (bytes : List UInt8) : Json :=
  match continued (.error (.revert bytes)) 32 with
  | .ok (.ok (.inr (ref,read,some result))) => Json.mkObj [("ref",reference ref),("read",toJson (read.map UInt8.toNat)),
      ("cells",toJson ((snapshot result.state).map toString)),("normal",toJson result.flow.isNormal),("clean",toJson (LocalState.clean? result.state).isSome),
      ("allocated",cell result.state.2 1),("alias",cell result.state.2 0)]
  | _ => Json.mkObj [("unexpected",toJson true)]
def haltRow (halt : Solidity.Source.Halt) : Json :=
  let execution := haltScope halt
  Json.mkObj [("outcome",match execution.1.1 with | .ok (.error h) => haltJson h | _ => Json.null),
    ("restored",reference (execution.1.2.1.get .here)),("raw",toJson ((snapshot execution.2).map toString)),
    ("logs",toJson (execution.2.2.logs.map (fun (a,b)=>(toString a.val,b.map UInt8.toNat))))]
def main : IO Unit := do
  let cases := [row "success" (.ok [0xbe,0xef]),row "revert" (.error (.revert [0xde,0xad])),row "empty" (.error (.revert [])),
    row "panic" (Solidity.Source.panic .assert),row "timeout" (.error .timeout),row "stuck" (.error (.stuck "sentinel"))]
  let wrong := (Solidity.Source.EM.sub inner wrongIndex : Solidity.Source.EM originEnv Outer _).run (outer,(HeapCatchPhysical.allocated [0xde,0xad]).2.2)
  let wrongType := (Solidity.Source.EM.sub inner badScopeRead : Solidity.Source.EM originEnv Outer _).run (outer,(HeapCatchPhysical.allocated [0xde,0xad]).2.2)
  IO.println (Json.mkObj [("schema",toJson (1:Nat)),("addressDomain",toJson "logical-heap-index"),("outerTypes",toJson ["bytes.memory"]),("innerTypes",toJson ["bytes.memory","bytes.memory"]),
    ("cases",toJson cases),("continuations",toJson [continuationJson [0xde,0xad],continuationJson [],continuationJson (Solidity.Source.panicData .assert)]),
    ("haltScopes",toJson ([Solidity.Source.Halt.revert [0xde,0xad],.revert [],.revert (Solidity.Source.panicData .assert),.timeout,.stuck "scope-sentinel"].map haltRow)),
    ("wrongIndex",Json.mkObj [("bytes",toJson (wrong.1.toOption.map (fun pair=>pair.1.map UInt8.toNat))),("restored",reference (wrong.2.1.get .here))]),
    ("wrongType",Json.mkObj [("outcome",match wrongType.1 with | .error h => haltJson h | _ => Json.null),("restored",reference (wrongType.2.1.get .here))])]).compress
