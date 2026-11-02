import Solidity.Yul.Composition.DoWhilePhysical
open Lean Solidity.Yul Solidity.Yul.Composition Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Yul.Composition.LocalPhysicalControls Solidity.Yul.Composition.ForPhysical
open Solidity.Yul.Composition.DoWhilePhysical
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

def physicalJson (state : Solidity.Source.St originEnv) : Json :=
  let encoded := reencodePersistentSlot (representedBanks originRegistry false firstPhysical.2)
    ⟨state.ex,firstPhysical.1.2⟩ account 43
  Json.mkObj [("word",toJson (encoded.map fun x=>toString x.val)),
    ("sourceJournalLength",toJson state.ex.journal.length),
    ("residualJournal",toJson (firstPhysical.1.2.journal.map fun (k,v)=>
      Json.arr #[toJson k.transient,toJson (toString k.address.val),toJson (toString k.slot.val),toJson (toString v.val)])),
    ("ownedJournal",toJson (firstPhysical.2.journal.map fun (k,v)=>
      Json.arr #[toJson k.transient,toJson (toString k.account.val),toJson (toString k.slot.val),toJson k.offset.val,toJson v.val.val]))]


def localJson {Γ : Solidity.Source.RCtx} : Solidity.Source.Locals originEnv.layout Γ → List Json
  | .nil => []
  | .cons value rest =>
    let current := match value with
      | .bool b => Json.mkObj [("type",toJson "bool"),("value",toJson b)]
      | .memRef _ id => Json.mkObj [("type",toJson "memory"),("logicalIndex",toJson id)]
      | _ => Json.mkObj [("type",toJson "other")]
    current :: localJson rest

def flowJson {Γ Δ : Solidity.Source.RCtx} : Solidity.Source.Out originEnv.layout Γ Δ → Json
  | .normal values => Json.mkObj [("tag",toJson "success"),("flow",toJson "normal"),("locals",toJson (localJson values))]
  | .brk values => Json.mkObj [("tag",toJson "success"),("flow",toJson "break"),("locals",toJson (localJson values))]
  | .cont values => Json.mkObj [("tag",toJson "success"),("flow",toJson "continue"),("locals",toJson (localJson values))]
  | .ret values => Json.mkObj [("tag",toJson "success"),("flow",toJson "return"),("locals",toJson (localJson values))]

def resultJson {Γ Δ : Solidity.Source.RCtx} :
    Except Solidity.Source.Halt (Except Solidity.Source.Halt (Solidity.Source.Out originEnv.layout Γ Δ)) → Json
  | .error h => Json.mkObj [("outerError",haltJson h)]
  | .ok (.error h) => haltJson h
  | .ok (.ok flow) => flowJson flow

def row {Γ Δ : Solidity.Source.RCtx} (name : String) (bytes : List UInt8)
    (input : Solidity.Source.Locals originEnv.layout Clean)
    (action : Solidity.Source.EM originEnv ScopeCatchPhysical.Outer (Solidity.Source.Out originEnv.layout Γ Δ)) : Json :=
  let before := UncheckedLoopPhysical.sampleRaw bytes
  let actual := AttemptPhysical.companion action ScopeCatchPhysical.outer before
  Json.mkObj [("name",toJson name),("inputLocals",toJson (localJson input)),("before",stateJson before),
    ("result",resultJson actual.1.1),("after",stateJson actual.2),
    ("physicalBefore",physicalJson before.2),("physicalAfter",physicalJson actual.2.2),
    ("outerRef",match actual.1.2.1 with | .cons value .nil=>reference value)]


abbrev Program := Solidity.Source.RStmt originEnv [] false ⟨false,false⟩ Clean Clean

def badCondition : Solidity.Source.RExpr originEnv Clean .bool :=
  .compare .eq (.indexBytes (.local dataIndex) (.const (Solidity.Source.Q.ofInt 100)) (by decide))
    (.indexBytes (.local dataIndex) (.const (Solidity.Source.Q.ofInt 100)) (by decide))
def rethrowProgram (index : Solidity.Source.Idx Clean (.bytes .memory)) : Program :=
  DoWhilePhysical.loop index (.bool false)
def poisonRethrow : Program := DoWhilePhysical.loop dataIndex badCondition
def breakProgram : Program := .doWhile .brk badCondition
def returnProgram : Program := .doWhile (.ret rfl) badCondition
def continueProgram : Program := .doWhile .cont (.assign (.local .here) (.bool false))
def normalProgram : Program :=
  .doWhile (.declInit (.bool true) rfl : Solidity.Source.RStmt originEnv [] false ⟨true,false⟩ Clean (.bool::Clean))
    (.assign (.local .here) (.bool false))
def continueFalse : Program := .doWhile .cont (.bool false)
def continueTrue : Program := .doWhile .cont (.bool true)
def poisonContinue : Program := .doWhile .cont badCondition
def poisonNormal : Program := .doWhile .skip badCondition

def itemsAction (g : Solidity.Source.Glob originEnv) (fuel : Nat)
    (code : Solidity.Source.RItems originEnv [] false ⟨false,false⟩ Clean Clean)
    (inside : Solidity.Source.Locals originEnv.layout Clean) :
    Solidity.Source.EM originEnv ScopeCatchPhysical.Outer (Solidity.Source.Out originEnv.layout Clean Clean) := do
  let (out,_) ← Solidity.Source.EM.sub .nil (Solidity.Source.execItems g packedStepFrame fuel 0 none code inside)
  pure out

def model (pipeline : Solidity.Roadmap.Pipeline) : Json := Id.run do
  let g := {global with pipeline:=pipeline}
  let obs := fun name bytes fuel code=>row name bytes (sampleInside bytes)
    (DoWhilePhysical.execute g packedStepFrame fuel code (sampleInside bytes))
  let dead : List UInt8 := [0xde,0xad]
  let panic := Solidity.Source.panicData .assert
  let rows := [obs "do-DEAD-false-condition" dead 5 (rethrowProgram dataIndex),
    obs "do-empty" [] 5 (rethrowProgram dataIndex),obs "do-panic" panic 5 (rethrowProgram dataIndex),
    obs "wrong-alias" dead 5 (rethrowProgram (.there (.there .here))),
    obs "revert-poison-condition-skipped" dead 8 poisonRethrow,
    obs "break-poison-condition-skipped" dead 8 breakProgram,
    obs "continue-condition-assigns" dead 3 continueProgram,
    obs "normal-restores-scope" dead 3 normalProgram,
    obs "continue-false" dead 2 continueFalse,
    obs "return-poison-condition-skipped" dead 2 returnProgram,
    obs "continue-true-timeout" dead 32 continueTrue,
    obs "continue-poison-executed" dead 8 poisonContinue,
    obs "normal-poison-executed" dead 8 poisonNormal,
    row "revert-skips-rest" dead (sampleInside dead) (itemsAction g 8
      (.stmt (rethrowProgram dataIndex) (.stmt (.rethrow (.there (.there .here))) .nil)) (sampleInside dead)),
    row "break-then-rest-executed" dead (sampleInside dead) (itemsAction g 8
      (.stmt breakProgram (.stmt (.rethrow (.there (.there .here))) .nil)) (sampleInside dead))]
  let rows := rows++([0,1,2,3,4].map fun fuel=>obs ("do-fuel-"++toString fuel) dead fuel (rethrowProgram dataIndex))
  let rows := rows++([0,1,2].map fun fuel=>obs ("continue-fuel-"++toString fuel) dead fuel continueProgram)
  let badInside : Solidity.Source.Locals originEnv.layout Clean :=
    .cons (.bool true) (.cons (.memRef rfl 99) (.cons (.memRef rfl 0) .nil))
  let rows := rows++[row "dangling-reference" dead badInside
      (DoWhilePhysical.execute g packedStepFrame 5 (rethrowProgram dataIndex) badInside),
    row "break-dangling-condition-not-read" dead badInside
      (DoWhilePhysical.execute g packedStepFrame 3 breakProgram badInside)]
  return Json.mkObj [("pipeline",toJson (match pipeline with | .legacy=>"legacy" | .viaIR=>"viaIR")),("cases",toJson rows)]

def main : IO Unit := IO.println (Json.compress (Json.mkObj [("schema",toJson (1:Nat)),
  ("engine",toJson "actual-Source-doWhile"),("nativeComparisons",toJson (0:Nat)),("fullProofGate",toJson "pending"),
  ("profiles",toJson [model .legacy,model .viaIR])]))
