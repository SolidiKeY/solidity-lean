import Solidity.Yul.Composition.UncheckedLoopPhysical
open Lean Solidity.Yul Solidity.Yul.Composition Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Yul.Composition.LocalPhysicalControls Solidity.Yul.Composition.UncheckedLoopPhysical
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


/-- An inhabited Glob fixture; rethrow laws hold for ANY Glob. No calls/hash
or compiler execution is substituted by this empty program. -/
def global : Solidity.Source.Glob originEnv where
  prog := {
    body := fun _ => none
    consts := fun _ => none
    inits := fun _ => []
    ctor := fun _ => none
    ctorLocals := fun _ => []
    baseArgs := fun _ => []
    contracts := [] }
  pipeline := .legacy
  fixed := {
    evm := Solidity.Roadmap.Evm.withKeccak
    ledger := fun balance _ address => balance address
    regionLen := 1
    rootSlots := 1 }
  balance0 := fun _=>0
  hasCode := fun _ _=>false
  callee := fun _=>.answer (.success [])
  timestamp := 0

def frameJson (state : Solidity.Source.St originEnv) : Json :=
  match state.fnLocals with
  | ⟨types,values⟩ =>
    let boolValue := match values.getAt 0 .bool with | .ok (.bool flag) => toJson flag | .error _ => Json.null
    let refAt := fun n => match values.getAt n (.bytes .memory) with | .ok ref => reference ref | .error _ => Json.null
    Json.mkObj [("types",toJson (types.map fun t=>match t with | .bool=>"bool" | .bytes .memory=>"bytes.memory" | _=>"other")),
      ("bool",boolValue),("refs",toJson [refAt 0,refAt 1])]

def stateJson (raw : LocalState originEnv ctx.tys) : Json :=
  Json.mkObj [("raw",toJson ((snapshot raw).map toString)),("next",toJson raw.2.heap.next),
    ("object",cell raw.2 1),("alias",cell raw.2 0),("frame",frameJson raw.2),
    ("logs",toJson (raw.2.logs.map (fun (a,b)=>(toString a.val,b.map UInt8.toNat)))),
    ("clean",toJson (LocalState.clean? raw).isSome)]

def resultJson {α : Type} : Except Solidity.Source.Halt (Except Solidity.Source.Halt α) → Json
  | .error h => Json.mkObj [("outerError",haltJson h)]
  | .ok (.error h) => haltJson h
  | .ok (.ok _) => Json.mkObj [("tag",toJson "success")]


def physicalJson (state : Solidity.Source.St originEnv) : Json :=
  let encoded := reencodePersistentSlot (representedBanks originRegistry false firstPhysical.2)
    ⟨state.ex,firstPhysical.1.2⟩ account 43
  Json.mkObj [("word",toJson (encoded.map fun x=>toString x.val)),
    ("sourceJournalLength",toJson state.ex.journal.length),
    ("residualJournal",toJson (firstPhysical.1.2.journal.map fun (k,v)=>
      Json.arr #[toJson k.transient,toJson (toString k.address.val),toJson (toString k.slot.val),toJson (toString v.val)])),
    ("ownedJournal",toJson (firstPhysical.2.journal.map fun (k,v)=>
      Json.arr #[toJson k.transient,toJson (toString k.account.val),toJson (toString k.slot.val),toJson k.offset.val,toJson v.val.val]))]

def row (name : String) (bytes : List UInt8)
    (action : Solidity.Source.EM originEnv ScopeCatchPhysical.Outer Unit) : Json :=
  let before := sampleRaw bytes
  let actual := AttemptPhysical.companion action ScopeCatchPhysical.outer before
  Json.mkObj [("name",toJson name),("before",stateJson before),("result",resultJson actual.1.1),
    ("after",stateJson actual.2),("physicalBefore",physicalJson before.2),("physicalAfter",physicalJson actual.2.2),
    ("outerRef",match actual.1.2.1 with | .cons value .nil=>reference value)]

def loopAction (g : Solidity.Source.Glob originEnv) (flag : Bool) (fuel : Nat)
    (index : Solidity.Source.Idx ScopeCatchPhysical.Inner (.bytes .memory)) (bytes : List UInt8) :
    Solidity.Source.EM originEnv ScopeCatchPhysical.Outer Unit := do
  let _ ← Solidity.Source.EM.sub .nil (Solidity.Source.execS g packedStepFrame fuel 0 none
    (loop (R:=[]) (M:=false) (l:=false) (u:=false) flag index) (sampleInside bytes))
  pure ()

def controlAction (g : Solidity.Source.Glob originEnv) (cont : Bool) (fuel : Nat) :
    Solidity.Source.EM originEnv ScopeCatchPhysical.Outer Unit := do
  let body : Solidity.Source.RStmt originEnv [] false ⟨true,false⟩ ScopeCatchPhysical.Inner ScopeCatchPhysical.Inner :=
    if cont then .cont else .brk
  let _ ← Solidity.Source.EM.sub .nil (Solidity.Source.execS g packedStepFrame fuel 0 none
    (.whileLoop (l:=false) (.bool true) body) (sampleInside [0xde,0xad]))
  pure ()

def normalAction (g : Solidity.Source.Glob originEnv) : Solidity.Source.EM originEnv ScopeCatchPhysical.Outer Unit := do
  let _ ← Solidity.Source.EM.sub .nil (Solidity.Source.execItems g packedStepFrame 8 0 none
    (.unchecked (.stmt (.declInit (.local (.here : Solidity.Source.Idx ScopeCatchPhysical.Inner (.bytes .memory))) rfl :
      Solidity.Source.RStmt originEnv [] false ⟨false,true⟩ ScopeCatchPhysical.Inner (.bytes .memory::ScopeCatchPhysical.Inner)) .nil) poison)
    (sampleInside [0xde,0xad]))
  pure ()

def model (pipeline : Solidity.Roadmap.Pipeline) : Json := Id.run do
  let g := {global with pipeline:=pipeline}
  let action := fun bytes fuel index=>execute g packedStepFrame fuel index (sampleInside bytes) poison
  let rows := [row "unchecked-DEAD" [0xde,0xad] (action [0xde,0xad] 4 .here),
    row "unchecked-empty" [] (action [] 4 .here),
    row "unchecked-panic" (Solidity.Source.panicData .assert) (action (Solidity.Source.panicData .assert) 4 .here),
    row "wrong-alias" [0xde,0xad] (action [0xde,0xad] 4 (.there .here)),
    row "normal-rest" [0xde,0xad] (normalAction g)]
  let rows := rows++([0,1,2,3].map fun fuel=>row ("unchecked-fuel-"++toString fuel) [0xde,0xad] (action [0xde,0xad] fuel .here))
  let rows := rows++[row "while-DEAD" [0xde,0xad] (loopAction g true 5 .here [0xde,0xad]),
    row "while-empty" [] (loopAction g true 5 .here []),
    row "while-panic" (Solidity.Source.panicData .assert) (loopAction g true 5 .here (Solidity.Source.panicData .assert)),
    row "while-wrong-alias" [0xde,0xad] (loopAction g true 5 (.there .here) [0xde,0xad]),
    row "while-false" [0xde,0xad] (loopAction g false 2 .here [0xde,0xad]),
    row "while-break" [0xde,0xad] (controlAction g false 2),
    row "while-continue" [0xde,0xad] (controlAction g true 32)]
  let rows := rows++([0,1,2,3,4].map fun fuel=>row ("while-fuel-"++toString fuel) [0xde,0xad] (loopAction g true fuel .here [0xde,0xad]))
  let badInside : Solidity.Source.Locals originEnv.layout ScopeCatchPhysical.Inner :=
    .cons (.memRef rfl 99) (.cons (.memRef rfl 0) .nil)
  let rows := rows++[row "dangling-reference" [0xde,0xad] (execute g packedStepFrame 4 .here badInside poison)]
  return Json.mkObj [("pipeline",toJson (match pipeline with | .legacy=>"legacy" | .viaIR=>"viaIR")),("cases",toJson rows)]

def main : IO Unit := IO.println (Json.compress (Json.mkObj [("schema",toJson (1:Nat)),
  ("engine",toJson "actual-Source-evaluator"),("nativeComparisons",toJson (0:Nat)),("fullProofGate",toJson "pending"),
  ("profiles",toJson [model .legacy,model .viaIR])]))
