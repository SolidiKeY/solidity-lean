import Solidity.Yul.Composition.NestedModifierPhysical
open Lean Solidity.Yul Solidity.Yul.Composition Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Yul.Composition.LocalPhysicalControls Solidity.Yul.Composition.ModifierPostPhysical
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

def eventJson : Solidity.Roadmap.Event → Json
  | .credit a v=>Json.mkObj [("kind",toJson "credit"),("address",toJson (toString a.val)),("value",toJson (toString v.val))]
  | other=>Json.mkObj [("unexpected",toJson (reprStr other))]

def stateJson (raw : LocalState originEnv ctx.tys) : Json :=
  Json.mkObj [("raw",toJson ((snapshot raw).map toString)),("next",toJson raw.2.heap.next),
    ("object",cell raw.2 1),("alias",cell raw.2 0),("frame",frameJson raw.2),
    ("logs",toJson (raw.2.logs.map (fun (a,b)=>(toString a.val,b.map UInt8.toNat)))),
    ("events",toJson (raw.2.events.map eventJson)),("clean",toJson (LocalState.clean? raw).isSome)]

def boolValue {τ : Solidity.Source.STy} : Solidity.Source.Val originEnv.layout τ → Json
  | .bool b=>toJson b
  | _=>toJson "unsupported-type"

def boolStorage {L : Solidity.Source.SPath → Solidity.Source.STy}
    (s : Solidity.Source.Storage originEnv.layout L) : Json :=
  Json.mkObj [("cPresent",toJson (s.cell (originPath "c")).isSome),
    ("cValue",match s.read (originPath "c") with | some v=>boolValue v | none=>Json.null)]
def accountJson {L} (a : Solidity.Source.Account originEnv.layout L) : Json :=
  Json.mkObj [("balance",toJson (toString a.balance.val)),("nonce",toJson a.nonce),("code",toJson a.code),("storage",boolStorage a.storage)]
def entryJson : Solidity.Source.Entry originEnv.layout originEnv.lay originEnv.lay → Json
  | .account a old=>Json.mkObj [("kind",toJson "account"),("address",toJson (toString a.val)),("old",accountJson old)]
  | .transient a old=>Json.mkObj [("kind",toJson "transient"),("address",toJson (toString a.val)),("old",boolStorage old)]
def physicalJson (state : Solidity.Source.St originEnv) : Json :=
  let encoded := reencodePersistentSlot (representedBanks originRegistry false firstPhysical.2)
    ⟨state.ex,firstPhysical.1.2⟩ account 43
  Json.mkObj [("word",toJson (encoded.map fun x=>toString x.val)),
    ("sourceJournalLength",toJson state.ex.journal.length),("sourceJournal",toJson (state.ex.journal.map entryJson)),
    ("currentAccount",accountJson (state.ex.world.accounts account)),("currentTransient",boolStorage (state.ex.transient.cells account)),
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


abbrev Parameters := ModifierPhysical.Parameters

def resultJson : Except Solidity.Source.Halt (Except Solidity.Source.Halt (Solidity.Source.Locals originEnv.layout Parameters)) → Json
  | .error h=>Json.mkObj [("outerError",haltJson h)]
  | .ok (.error h)=>haltJson h
  | .ok (.ok locals)=>Json.mkObj [("tag",toJson "success"),("locals",toJson (localJson locals))]

def row (name : String) (bytes : List UInt8) (inside : Solidity.Source.Locals originEnv.layout Parameters)
    (action : Solidity.Source.EM originEnv ScopeCatchPhysical.Outer (Solidity.Source.Locals originEnv.layout Parameters)) : Json :=
  let before := ModifierPostPhysical.raw bytes
  let actual := AttemptPhysical.companion action ScopeCatchPhysical.outer before
  Json.mkObj [("name",toJson name),("inputLocals",toJson (localJson inside)),("before",stateJson before),
    ("result",resultJson actual.1.1),("after",stateJson actual.2),
    ("physicalBefore",physicalJson before.2),("physicalAfter",physicalJson actual.2.2),
    ("outerRef",match actual.1.2.1 with | .cons value .nil=>reference value)]


def emptyOuter (G : Solidity.Source.Glob originEnv) : Solidity.Source.Glob originEnv :=
  ModifierPostPhysical.program {G with prog := {G.prog with body := fun d => if d.name = "ownedOuter" then Option.some (ModifierPostPhysical.emptyBody originEnv) else G.prog.body d}}
def emptyInner (G : Solidity.Source.Glob originEnv) := NestedModifierPhysical.outerBase (emptyProgram G)
def missingInner (G : Solidity.Source.Glob originEnv) := NestedModifierPhysical.outerBase (ModifierPhysical.noBodies G)
def missingOuter (G : Solidity.Source.Glob originEnv) := ModifierPostPhysical.program (ModifierPhysical.noBodies G)
def badInner (G : Solidity.Source.Glob originEnv) := NestedModifierPhysical.outerBase (badProgram G)
def badOuter (G : Solidity.Source.Glob originEnv) := ModifierPostPhysical.program (badProgram G)

def model (pipeline : Solidity.Roadmap.Pipeline) : Json := Id.run do
  let g := {global with pipeline:=pipeline}
  let inside := fun bytes=>UncheckedLoopPhysical.sampleInside bytes
  let body := fun idx=>ModifierPhysical.body (E:=originEnv) idx
  let normal := plain originEnv Parameters false
  let returned := plain originEnv Parameters true
  let mods : List (Solidity.Source.RModInv originEnv Parameters) :=
    [NestedModifierPhysical.outerInvocation .here,invocation (.there .here)]
  let switched : List (Solidity.Source.RModInv originEnv Parameters) :=
    [NestedModifierPhysical.outerInvocation (.there .here),invocation .here]
  let run := fun selected fuel code calls input=>ModifierPostPhysical.execute selected packedStepFrame fuel code calls input
  let obs := fun name bytes action=>row name bytes (inside bytes) action
  let dead : List UInt8 := [0xde,0xad]
  let panic := Solidity.Source.panicData .assert
  let outerDangling : Solidity.Source.Locals originEnv.layout Parameters := .cons (.memRef rfl 99) (.cons (.memRef rfl 0) .nil)
  let innerDangling : Solidity.Source.Locals originEnv.layout Parameters := .cons (.memRef rfl 1) (.cons (.memRef rfl 99) .nil)
  let rows := [obs "body-DEAD" dead (run (NestedModifierPhysical.program g) 12 (body .here) mods (inside dead)),obs "body-empty" [] (run (NestedModifierPhysical.program g) 12 (body .here) mods (inside [])),
    obs "body-panic" panic (run (NestedModifierPhysical.program g) 12 (body .here) mods (inside panic)),obs "wrong-body-alias" dead (run (NestedModifierPhysical.program g) 12 (body (.there .here)) mods (inside dead)),
    obs "normal-inner-AABB" dead (run (NestedModifierPhysical.program g) 12 normal mods (inside dead)),obs "return-inner-AABB" dead (run (NestedModifierPhysical.program g) 12 returned mods (inside dead)),
    obs "wrong-inner-argument-DEAD" dead (run (NestedModifierPhysical.program g) 12 normal switched (inside dead)),
    obs "reversed-modifier-order-DEAD" dead (run (NestedModifierPhysical.program g) 12 normal mods.reverse (inside dead)),
    row "normal-outer-dangling-unread" dead outerDangling (run (NestedModifierPhysical.program g) 12 normal mods outerDangling),
    row "body-inner-dangling-unread" dead innerDangling (run (NestedModifierPhysical.program g) 12 (body .here) mods innerDangling),
    row "normal-inner-dangling-read" dead innerDangling (run (NestedModifierPhysical.program g) 12 normal mods innerDangling),
    row "return-inner-dangling-read" dead innerDangling (run (NestedModifierPhysical.program g) 12 returned mods innerDangling),
    row "empty-outer-suppresses-all" dead (inside dead) (run (emptyOuter g) 12 (body .here) mods (inside dead)),
    row "empty-outer-dangling-unread" dead outerDangling (run (emptyOuter g) 12 (body .here) mods outerDangling),
    row "empty-inner-outer-postlude-DEAD" dead (inside dead) (run (emptyInner g) 12 normal mods (inside dead)),
    row "empty-inner-dangling-body-suppressed" dead outerDangling
      (run (emptyInner g) 12 (body .here) [NestedModifierPhysical.outerInvocation (.there .here),invocation (.there .here)] outerDangling),
    row "missing-inner-body" dead (inside dead) (run (missingInner g) 12 (body .here) mods (inside dead)),
    row "missing-outer-body" dead (inside dead) (run (missingOuter g) 12 (body .here) mods (inside dead)),
    row "bad-inner-parameters" dead (inside dead) (run (badInner g) 12 (body .here) mods (inside dead)),
    row "bad-outer-parameters" dead (inside dead) (run (badOuter g) 12 (body .here) mods (inside dead)),
    obs "inner-postlude-empty" [] (run (NestedModifierPhysical.program g) 12 normal switched (inside [])),obs "inner-postlude-full-panic" panic (run (NestedModifierPhysical.program g) 12 returned switched (inside panic))]
  let rows := rows++([0,1,2,3,4,5,6,7,8,9,10,11].map fun fuel=>obs ("body-fuel-"++toString fuel) dead (run (NestedModifierPhysical.program g) fuel (body .here) mods (inside dead)))
  let rows := rows++[obs "normal-fuel9" dead (run (NestedModifierPhysical.program g) 9 normal mods (inside dead)),obs "normal-fuel10" dead (run (NestedModifierPhysical.program g) 10 normal mods (inside dead)),
    obs "return-fuel10" dead (run (NestedModifierPhysical.program g) 10 returned mods (inside dead)),obs "return-fuel11" dead (run (NestedModifierPhysical.program g) 11 returned mods (inside dead)),
    row "body-dangling-read" dead outerDangling (run (NestedModifierPhysical.program g) 12 (body .here) mods outerDangling)]
  return Json.mkObj [("pipeline",toJson (match pipeline with | .legacy=>"legacy" | .viaIR=>"viaIR")),("cases",toJson rows)]

def main : IO Unit := IO.println (Json.compress (Json.mkObj [("schema",toJson (1:Nat)),
  ("engine",toJson "actual-Source-nested-modifier"),("nativeComparisons",toJson (0:Nat)),("fullProofGate",toJson "pending"),
  ("profiles",toJson [model .legacy,model .viaIR])]))
