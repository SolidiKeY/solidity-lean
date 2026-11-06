import Solidity.Yul.Composition.RuntimeBlockPhysical
open Lean Solidity.Yul Solidity.Yul.Composition Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Yul.Composition.LocalPhysicalControls Solidity.Yul.Composition.RuntimeBlockPhysical
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
    ("logs",toJson (raw.2.logs.map (fun (a,b)=>(toString a.val,b.map UInt8.toNat)))),
    ("clean",toJson (LocalState.clean? raw).isSome)]

def row (name : String) (action : Solidity.Source.EM originEnv ScopeCatchPhysical.Outer (List UInt8)) : Json :=
  let execution := AttemptPhysical.companion action ScopeCatchPhysical.outer AttemptPhysical.input
  Json.mkObj [("name",toJson name),("result",resultJson execution.1.1),
    ("restored",reference (execution.1.2.1.get .here)),("after",stateJson execution.2)]

def dead (fuel : Nat) : Json := row ("dead-"++toString fuel)
  (fromOutcome global packedStepFrame fuel (.revert [0xde,0xad]))

def main : IO Unit := do
  let deadState := allocatedState AttemptPhysical.input.2 [0xde,0xad]
  let declaration := (Solidity.Source.execS global packedStepFrame 2 0 none
    (aliasDecl (.here : Solidity.Source.Idx ScopeCatchPhysical.Inner (.bytes .memory))) ScopeCatchPhysical.inner).run (.nil,deadState)
  let declared := match declaration.1 with
    | .ok (.normal values) => Json.mkObj [("refs",toJson [reference (values.get .here),reference (values.get (.there .here)),reference (values.get (.there (.there .here)))]),
      ("heap",cell declaration.2.2 1)]
    | _ => Json.null
  let cases := [dead 0,dead 3,dead 4,dead 32,
    row "empty" (fromOutcome global packedStepFrame 4 (.revert [])),
    row "panic" (fromOutcome global packedStepFrame 32 (.revert (Solidity.Source.panicData .assert))),
    row "success" (fromOutcome global packedStepFrame 0 (.success [0xbe,0xef])),
    row "timeout" (runtime global packedStepFrame 32 (Solidity.Source.EM.halt .timeout)),
    row "stuck" (runtime global packedStepFrame 32 (Solidity.Source.EM.halt (.stuck "sentinel"))),
    row "external-revert" (runtime global packedStepFrame 32 (externalResult [.bool] (.revert [0xde,0xad]))),
    row "external-short" (runtime global packedStepFrame 32 (externalResult [.bool] (.success [0xde,0xad]))),
    row "stuck-prefix" (runtime global packedStepFrame 32 (do
      Solidity.Source.EM.modSt fun state=>{state with logs:=(account,[0x99])::state.logs}
      Solidity.Source.EM.halt (.stuck "prefix")))]
  let wrong := AttemptPhysical.companion
    (executeBound global packedStepFrame 32 (.there .here) ScopeCatchPhysical.inner : Solidity.Source.EM originEnv ScopeCatchPhysical.Outer _)
    ScopeCatchPhysical.outer (AttemptPhysical.input.1,deadState)
  IO.println (Json.mkObj [("schema",toJson (1:Nat)),("addressDomain",toJson "logical-heap-index"),
    ("input",stateJson AttemptPhysical.input),("declared",declared),("cases",toJson cases),
    ("wrongAlias",Json.mkObj [("result",resultJson wrong.1.1),("restored",reference (wrong.1.2.1.get .here)),("after",stateJson wrong.2)])]).compress
