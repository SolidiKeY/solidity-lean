import Solidity.Yul.Composition.ModifierPhysical
open Lean Solidity.Yul Solidity.Yul.Composition Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Yul.Composition.LocalPhysicalControls Solidity.Yul.Composition.ModifierPhysical
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

def row {α : Type} (name : String) (bytes : List UInt8) (action : Solidity.Source.EM originEnv [] α) : Json :=
  let before := (AttemptPhysical.input.1,callerState bytes)
  let execution := AttemptPhysical.companion action .nil before
  Json.mkObj [("name",toJson name),("before",stateJson before),("result",resultJson execution.1.1),("after",stateJson execution.2)]

def pipelineRows (pipeline : Solidity.Roadmap.Pipeline) : Json :=
  let g := {global with pipeline:=pipeline}
  let state := callerState [0xde,0xad]
  let initial := parameterValues (E:=originEnv) 0 1
  let action := fun fuel => Solidity.Source.callInternal (program g .here) packedStepFrame fuel functionDecl (arguments 0 1) []
  let rows := [row "plain" [0xde,0xad] (Solidity.Source.runMods g packedStepFrame 32 (body (E:=originEnv) (.here : Solidity.Source.Idx Parameters (.bytes .memory))) [] initial),
    row "modifier" [0xde,0xad] (Solidity.Source.runMods (withAround g) packedStepFrame 32 (body (E:=originEnv) (.here : Solidity.Source.Idx Parameters (.bytes .memory))) [invocation originEnv Parameters] initial),
    row "internal" [0xde,0xad] (action 32),
    row "empty" [] (action 32),row "panic" (Solidity.Source.panicData .assert) (action 32),
    row "wrong-alias" [0xde,0xad] (Solidity.Source.callInternal (program g (.there .here)) packedStepFrame 32 functionDecl (arguments 0 1) [])]
  let rows := rows++([0,1,2,3,4,5,6,7].map fun fuel=>row ("fuel-"++toString fuel) [0xde,0xad] (action fuel))
  let rows := rows++[
    row "missing-modifier" [0xde,0xad] (Solidity.Source.runMods (noBodies g) packedStepFrame 32 (body (E:=originEnv) (.here : Solidity.Source.Idx Parameters (.bytes .memory))) [invocation originEnv Parameters] initial),
    row "modifier-parameters" [0xde,0xad] (Solidity.Source.runMods (mismatchedProgram g) packedStepFrame 32 (body (E:=originEnv) (.here : Solidity.Source.Idx Parameters (.bytes .memory))) [invocation originEnv Parameters] initial),
    row "missing-function" [0xde,0xad] (Solidity.Source.callInternal (noBodies g) packedStepFrame 32 functionDecl (arguments 0 1) []),
    row "invalid-call-frame" [0xde,0xad] (Solidity.Source.callInternal (program g .here) packedStepFrame 32 functionDecl Solidity.Source.Vals.nil []),
    row "placeholder-outside" [0xde,0xad] (Solidity.Source.execS g packedStepFrame 1 0 none (.placeholder rfl : Solidity.Source.RStmt originEnv [] true .body [] []) .nil),
    row "invalid-placeholder-frame" [0xde,0xad] (Solidity.Source.execS g packedStepFrame 1 0 (some ⟨body (E:=originEnv) (.here : Solidity.Source.Idx Parameters (.bytes .memory)),[],initial⟩) (.placeholder rfl : Solidity.Source.RStmt originEnv [] true .body [] []) .nil)]
  let alternateState := {state with fnLocals:=⟨[Solidity.Source.STy.bytes .memory],Solidity.Source.Locals.cons (.memRef rfl 0) .nil⟩}
  let alternate := AttemptPhysical.companion (action 32) .nil (AttemptPhysical.input.1,alternateState)
  let rows := rows++[Json.mkObj [("name",toJson "alternate-saved-frame"),("before",stateJson (AttemptPhysical.input.1,alternateState)),
    ("result",resultJson alternate.1.1),("after",stateJson alternate.2)]]
  let installed := {state with fnLocals:=⟨Parameters,initial⟩}
  let placeholder := AttemptPhysical.companion
    (Solidity.Source.execS g packedStepFrame 32 0 (some ⟨body (E:=originEnv) (.here : Solidity.Source.Idx Parameters (.bytes .memory)),[],initial⟩)
      (.placeholder rfl : Solidity.Source.RStmt originEnv [] true .body [] []) .nil) .nil (AttemptPhysical.input.1,installed)
  Json.mkObj [("pipeline",toJson (match pipeline with | .legacy=>"legacy" | .viaIR=>"viaIR")),("cases",toJson rows),
    ("directPlaceholder",Json.mkObj [("before",stateJson (AttemptPhysical.input.1,installed)),("result",resultJson placeholder.1.1),("after",stateJson placeholder.2)])]

def main : IO Unit := do
  IO.println (Json.mkObj [("schema",toJson (1:Nat)),("addressDomain",toJson "logical-heap-index"),
    ("scope",toJson "selected-resolved-runtime-not-frontend-admission"),("pipelines",toJson [pipelineRows .legacy,pipelineRows .viaIR])]).compress
