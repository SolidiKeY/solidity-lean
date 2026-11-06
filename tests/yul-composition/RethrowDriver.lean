import Solidity.Yul.Composition.RethrowPhysical
open Lean Solidity.Yul Solidity.Yul.Composition Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Yul.Composition.LocalPhysicalControls
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

def resultJson : Except Solidity.Source.Halt (Except Solidity.Source.Halt (List UInt8)) → Json
  | .error h => Json.mkObj [("outerError",haltJson h)]
  | .ok (.error h) => haltJson h
  | .ok (.ok bytes) => Json.mkObj [("tag",toJson "success"),("bytes",toJson (bytes.map UInt8.toNat))]

def stateJson (raw : LocalState originEnv ctx.tys) : Json :=
  Json.mkObj [("raw",toJson ((snapshot raw).map toString)),("next",toJson raw.2.heap.next),
    ("object",cell raw.2 1),("alias",cell raw.2 0),
    ("logs",toJson (raw.2.logs.map (fun (a,b)=>(toString a.val,b.map UInt8.toNat))))]

def scopeJson (result : Except Solidity.Source.Halt (Except Solidity.Source.Halt ((List UInt8) ⊕
    (Solidity.Source.Val originEnv.layout (.bytes .memory) × (List UInt8 × Solidity.Source.Locals originEnv.layout ScopeCatchPhysical.Inner))))) : Json :=
  match result with
  | .error h => Json.mkObj [("outerError",haltJson h)]
  | .ok (.error h) => haltJson h
  | .ok (.ok (.inl bytes)) => Json.mkObj [("tag",toJson "success"),("bytes",toJson (bytes.map UInt8.toNat))]
  | .ok (.ok (.inr (ref,(bytes,values)))) => Json.mkObj [("tag",toJson "scoped"),("ref",reference ref),
    ("bytes",toJson (bytes.map UInt8.toNat)),("inner",toJson [reference (values.get .here),reference (values.get (.there .here))])]

def row (name : String) (outcome : Except Solidity.Source.Halt (List UInt8)) (fuel : Nat) : Json :=
  let execution := RethrowPhysical.run global outcome fuel
  Json.mkObj [("name",toJson name),("fuel",toJson fuel),("capturedScope",scopeJson execution.1.1.1),
    ("before",stateJson execution.1.2),("result",resultJson execution.2.1.1),
    ("restoredBefore",reference (execution.1.1.2.1.get .here)),
    ("restoredAfter",reference (execution.2.1.2.1.get .here)),("after",stateJson execution.2.2)]

def controlRow (name : String) (fuel : Nat) (index : Solidity.Source.Idx ScopeCatchPhysical.Inner (.bytes .memory))
    (inside : Solidity.Source.Locals originEnv.layout ScopeCatchPhysical.Inner) : Json :=
  let raw := (ScopeCatchPhysical.run (.error (.revert [0xde,0xad]))).2.2
  let execution := AttemptPhysical.companion (RethrowPhysical.scopedRethrow global packedStepFrame fuel index inside) ScopeCatchPhysical.outer raw
  Json.mkObj [("name",toJson name),("fuel",toJson fuel),("inside",toJson [reference (inside.get .here),reference (inside.get (.there .here))]),
    ("result",resultJson execution.1.1),("restored",reference (execution.1.2.1.get .here)),
    ("before",stateJson raw),("after",stateJson execution.2)]

def main : IO Unit := do
  let caught := [("revert",[0xde,0xad]),("empty",[]),("panic",Solidity.Source.panicData .assert)]
  let cases := caught.flatMap fun (name,bytes)=>[0,1,32].map fun fuel=>row name (.error (.revert bytes)) fuel
  let cases := cases++[row "success" (.ok [0xbe,0xef]) 0,row "timeout" (.error .timeout) 32,row "stuck" (.error (.stuck "sentinel")) 32]
  let controls := [0,1,32].flatMap fun fuel=>[controlRow "wrong-index" fuel (.there .here) ScopeCatchPhysical.inner,
    controlRow "dangling" fuel .here RethrowPhysical.danglingInner]
  IO.println (Json.mkObj [("schema",toJson (1:Nat)),("addressDomain",toJson "logical-heap-index"),
    ("global",toJson "inhabited-legacy-source-fixture; laws quantify arbitrary Glob"),
    ("cases",toJson cases),("controls",toJson controls)]).compress
