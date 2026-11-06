import Solidity.Yul.Composition.ModifierPhysical
import Solidity.Yul.Composition.UncheckedLoopPhysical

/-! Selected real modifier argument/alias/placeholder/postlude consumers.
No new evaluator or general frontend/modifier/raw-session adequacy. -/
namespace Solidity.Yul.Composition.ModifierPostPhysical
open Solidity.Yul.Views Solidity.Yul.Views.Controls LocalPhysicalControls

def postDecl : Source.Decl :=
  ⟨.modifier,"ownedPost",none,false,
    .modifier "ownedPost" (.some (.cons (.param (.elem .bytes) (some .memory) (some "tail")) .nil)) false none
      (.some (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "_")))) .nil)))⟩

def postBody (E : Source.Env) : Source.RBody E where
  ps := [.bytes .memory]
  rs := []
  inModifier := true
  locals := [.bytes .memory]
  out := [.bytes .memory,.bytes .memory]
  items := .stmt (.declInit (.local .here) rfl)
    (.stmt (.placeholder rfl) (.stmt (.rethrow .here) .nil))

def invocation {E : Source.Env} {Γ : Source.RCtx} (index : Source.Idx Γ (.bytes .memory)) : Source.RModInv E Γ :=
  ⟨postDecl,[.bytes .memory],.cons (.local index) rfl .nil⟩

def program {E : Source.Env} (G : Source.Glob E) : Source.Glob E :=
  {G with prog := {G.prog with body := fun d=>if d.name="ownedPost" then some (postBody E) else G.prog.body d}}

theorem lookup_post {E : Source.Env} (G : Source.Glob E) (F : Source.Fr) :
    (program G).prog.body ((program G).dispatchMod F.contract postDecl) = some (postBody E) := rfl

def plain (E : Source.Env) (Γ : Source.RCtx) (returns : Bool) : Source.RBody E where
  ps := Γ.reverse
  rs := []
  inModifier := false
  locals := Γ
  out := Γ
  items := if returns then .stmt (.ret rfl) .nil else .nil

/-- Both actual normal and return outcomes yield the function's typed locals. -/
theorem plain_run {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (returns : Bool) (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.runMods G F (fuel+3) (plain E Γ returns) [] inside).run (.nil,state) = (.ok inside,(.nil,state)) := by
  cases returns
  · rw [Source.runMods]
    change (Source.EM.lift (inside.restore Γ) : Source.EM E [] _).run (.nil,state) = _
    have restored : inside.restore Γ = .ok inside := by
      unfold Source.Locals.restore
      rw [Nat.sub_self]
      simp only [List.drop_zero,dif_pos rfl]
      rfl
    rw [restored]
    rfl
  · rfl

theorem placeholder_plain {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (returns : Bool) (inside : Source.Locals E.layout Γ) (state : Source.St E)
    (modifierLocals : Source.Locals E.layout [.bytes .memory,.bytes .memory]) :
    (Source.execS G F (fuel+4) 1 (some ⟨plain E Γ returns,[],inside⟩)
      (.placeholder rfl : Source.RStmt E [] true .body _ _) modifierLocals).run
      (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.ok (.normal modifierLocals),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := by
  rw [Source.execS,Source.Hoare.run_bind]
  have read : (Source.EM.st : Source.EM E [] _).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.ok {state with fnLocals:=⟨Γ,inside⟩},(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl
  rw [read]
  dsimp only [plain]
  rw [dif_pos rfl]
  change ((do
    let lin ← match G.pipeline with
      | .legacy => pure inside
      | .viaIR => Source.zeroInner (fuel+3) 0 inside
    let out ← Source.runMods G F (fuel+3) (plain E Γ returns) [] lin
    Source.EM.modSt fun s=>{s with fnLocals:=⟨Γ,out⟩}
    pure (.normal modifierLocals) : Source.EM E [] (Source.Out E.layout [.bytes .memory,.bytes .memory] [.bytes .memory,.bytes .memory])).run
      (.nil,{state with fnLocals:=⟨Γ,inside⟩})) = _
  cases pipe : G.pipeline <;>
    change ((do
      let out ← Source.runMods G F (fuel+3) (plain E Γ returns) [] inside
      Source.EM.modSt fun s=>{s with fnLocals:=⟨Γ,out⟩}
      pure (.normal modifierLocals) : Source.EM E [] (Source.Out E.layout [.bytes .memory,.bytes .memory] [.bytes .memory,.bytes .memory])).run
        (.nil,{state with fnLocals:=⟨Γ,inside⟩})) = _
  all_goals
    rw [Source.Hoare.run_bind,plain_run]
    rfl

theorem placeholder_revert {E : Source.Env} {Γ Δ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel address nps : Nat) (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory))
    (values : Source.Locals E.layout Γ) (state : Source.St E) (modifierLocals : Source.Locals E.layout Δ)
    (reference : values.get index = .memRef rfl address)
    (found : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execS G F (fuel+5) nps (some ⟨ModifierPhysical.body (E:=E) index,[],values⟩)
      (.placeholder rfl : Source.RStmt E [] true .body Δ Δ) modifierLocals).run
      (.nil,{state with fnLocals:=⟨Γ,values⟩}) =
      (Except.error (.revert bytes),(.nil,{state with fnLocals:=⟨Γ,values⟩})) := by
  rw [Source.execS,Source.Hoare.run_bind]
  have readState : (Source.EM.st : Source.EM E [] _).run (.nil,{state with fnLocals:=⟨Γ,values⟩}) =
    (Except.ok {state with fnLocals:=⟨Γ,values⟩},(.nil,{state with fnLocals:=⟨Γ,values⟩})) := rfl
  rw [readState]
  dsimp only [ModifierPhysical.body]
  rw [dif_pos rfl]
  change ((do
    let lin ← match G.pipeline with
      | .legacy => pure values
      | .viaIR => Source.zeroInner (fuel+4) 0 values
    let result ← Source.runMods G F (fuel+4) (ModifierPhysical.body (E:=E) index) [] lin
    Source.EM.modSt fun s => {s with fnLocals:=⟨Γ,result⟩}
    pure (.normal modifierLocals) : Source.EM E [] (Source.Out E.layout Δ Δ)).run
      (.nil,{state with fnLocals:=⟨Γ,values⟩})) = _
  cases pipeline : G.pipeline <;>
    change ((do
      let result ← Source.runMods G F (fuel+4) (ModifierPhysical.body (E:=E) index) [] values
      Source.EM.modSt fun s => {s with fnLocals:=⟨Γ,result⟩}
      pure (.normal modifierLocals) : Source.EM E [] (Source.Out E.layout Δ Δ)).run
        (.nil,{state with fnLocals:=⟨Γ,values⟩})) = _
  all_goals
    rw [Source.Hoare.run_bind,ModifierPhysical.no_modifiers G F fuel address bytes index values {state with fnLocals:=⟨Γ,values⟩} reference found]

/-- Declaration aliases the real converted modifier argument. Body revert
skips the entire postlude, even if that postlude reference is dangling. -/
theorem post_items_revert {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel address argument : Nat) (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (state : Source.St E)
    (reference : inside.get index=.memRef rfl address)
    (found : state.heap.get address=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execItems G F (fuel+7) 1 (some ⟨ModifierPhysical.body index,[],inside⟩)
      (postBody E).items (.cons (.memRef rfl argument) .nil)).run
      (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error (.revert bytes),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := by
  unfold postBody
  rw [Source.execItems,Source.Hoare.run_bind,UncheckedLoopPhysical.declare]
  dsimp only
  rw [Source.Hoare.run_bind,Source.execItems,Source.Hoare.run_bind]
  rw [placeholder_revert G F fuel address 1 bytes index inside state _ reference found]

/-- Normal/return from the function body does NOT skip the modifier postlude. -/
theorem post_items_plain {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel argument : Nat) (bytes : List UInt8) (returns : Bool)
    (inside : Source.Locals E.layout Γ) (state : Source.St E)
    (found : state.heap.get argument=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execItems G F (fuel+7) 1 (some ⟨plain E Γ returns,[],inside⟩)
      (postBody E).items (.cons (.memRef rfl argument) .nil)).run
      (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error (.revert bytes),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := by
  unfold postBody
  rw [Source.execItems,Source.Hoare.run_bind,UncheckedLoopPhysical.declare]
  dsimp only
  rw [Source.Hoare.run_bind,Source.execItems,Source.Hoare.run_bind,
    placeholder_plain G F (fuel+1) returns inside state]
  dsimp only
  rw [Source.Hoare.run_bind,Source.execItems,Source.Hoare.run_bind,
    UncheckedLoopPhysical.rethrow G F (fuel+3) 1 argument (some ⟨plain E Γ returns,[],inside⟩) bytes .here _ {state with fnLocals:=⟨Γ,inside⟩} rfl found]

/-- Full selected actual runMods entry: converted argument, real body lookup,
frame install/attempt, placeholder body revert, and finally saved-frame restore. -/
theorem modifier_revert {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel address argument : Nat) (bytes : List UInt8) (bodyIndex argIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (state : Source.St E)
    (bodyRef : inside.get bodyIndex=.memRef rfl address)
    (argRef : inside.get argIndex=.memRef rfl argument)
    (found : state.heap.get address=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.runMods (program G) F (fuel+8) (ModifierPhysical.body bodyIndex) [invocation argIndex] inside).run (.nil,state) =
      (.error (.revert bytes),(.nil,state)) := by
  rw [Source.runMods,Source.Hoare.run_bind]
  have args : (Source.EM.sub inside (Source.evalConvArgs (program G) F (fuel+7) (invocation argIndex).args) : Source.EM E [] _).run
      (.nil,state) = (.ok (Source.Vals.cons (.memRef rfl argument) .nil,inside),(.nil,state)) := by
    change ((Except.ok ((Source.Vals.cons (inside.get argIndex) .nil : Source.Vals E.layout [.bytes .memory]),inside), (Source.Locals.nil,state)) :
      Except Source.Halt (Source.Vals E.layout [.bytes .memory] × Source.Locals E.layout Γ) × Source.EMState E []) = _
    rw [argRef]
  rw [args]
  dsimp only [invocation]
  rw [lookup_post]
  dsimp only [postBody]
  rw [dif_pos (show ([Source.STy.bytes .memory] : Source.RCtx).reverseAux [] = [Source.STy.bytes .memory] from rfl),Source.Hoare.run_bind]
  have read : (Source.EM.st : Source.EM E [] _).run (.nil,state) = (.ok state,(.nil,state)) := rfl
  rw [read]
  dsimp only
  rw [Source.Hoare.run_bind]
  dsimp only [ModifierPhysical.body]
  have install : (Source.EM.modSt (fun s : Source.St E=>{s with fnLocals:=⟨Γ,inside⟩}) : Source.EM E [] Unit).run
      (.nil,state) = (.ok (),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl
  rw [install]
  dsimp only
  rw [Source.Hoare.run_bind,AttemptPhysical.attempt_run]
  have ran := post_items_revert (program G) F fuel address argument bytes bodyIndex inside state bodyRef found
  dsimp only [ModifierPhysical.body,postBody] at ran
  dsimp only [Source.Vals.onto,Source.L0,List.length_cons,List.length_nil]
  rw [ran]
  rfl

theorem modifier_plain {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel argument : Nat) (bytes : List UInt8) (returns : Bool) (argIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (state : Source.St E)
    (argRef : inside.get argIndex=.memRef rfl argument)
    (found : state.heap.get argument=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.runMods (program G) F (fuel+8) (plain E Γ returns) [invocation argIndex] inside).run (.nil,state) =
      (.error (.revert bytes),(.nil,state)) := by
  rw [Source.runMods,Source.Hoare.run_bind]
  have args : (Source.EM.sub inside (Source.evalConvArgs (program G) F (fuel+7) (invocation argIndex).args) : Source.EM E [] _).run
      (.nil,state) = (.ok (Source.Vals.cons (.memRef rfl argument) .nil,inside),(.nil,state)) := by
    change ((Except.ok ((Source.Vals.cons (inside.get argIndex) .nil : Source.Vals E.layout [.bytes .memory]),inside), (Source.Locals.nil,state)) :
      Except Source.Halt (Source.Vals E.layout [.bytes .memory] × Source.Locals E.layout Γ) × Source.EMState E []) = _
    rw [argRef]
  rw [args]
  dsimp only [invocation]
  rw [lookup_post]
  dsimp only [postBody]
  rw [dif_pos (show ([Source.STy.bytes .memory] : Source.RCtx).reverseAux [] = [Source.STy.bytes .memory] from rfl),Source.Hoare.run_bind]
  have read : (Source.EM.st : Source.EM E [] _).run (.nil,state) = (.ok state,(.nil,state)) := rfl
  rw [read]
  dsimp only
  rw [Source.Hoare.run_bind]
  dsimp only [plain]
  have install : (Source.EM.modSt (fun s : Source.St E=>{s with fnLocals:=⟨Γ,inside⟩}) : Source.EM E [] Unit).run
      (.nil,state) = (.ok (),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl
  rw [install]
  dsimp only
  rw [Source.Hoare.run_bind,AttemptPhysical.attempt_run]
  have ran := post_items_plain (program G) F fuel argument bytes returns inside state found
  dsimp only [plain,postBody] at ran
  dsimp only [Source.Vals.onto,Source.L0,List.length_cons,List.length_nil]
  rw [ran]
  rfl

def emptyBody (E : Source.Env) : Source.RBody E :=
  {postBody E with out:=[.bytes .memory],items:=.nil}
def emptyProgram {E : Source.Env} (G : Source.Glob E) : Source.Glob E :=
  {G with prog:={G.prog with body:=fun d=>if d.name="ownedPost" then some (emptyBody E) else G.prog.body d}}
theorem lookup_empty {E : Source.Env} (G : Source.Glob E) (F : Source.Fr) :
    (emptyProgram G).prog.body ((emptyProgram G).dispatchMod F.contract postDecl) = some (emptyBody E) := rfl

theorem empty_modifier {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel argument : Nat) (bodyIndex argIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (state : Source.St E)
    (argRef : inside.get argIndex=.memRef rfl argument)
    :
    (Source.runMods (emptyProgram G) F (fuel+8) (ModifierPhysical.body bodyIndex) [invocation argIndex] inside).run (.nil,state) =
      (.ok inside,(.nil,state)) := by
  rw [Source.runMods,Source.Hoare.run_bind]
  have args : (Source.EM.sub inside (Source.evalConvArgs (emptyProgram G) F (fuel+7) (invocation argIndex).args) : Source.EM E [] _).run
      (.nil,state) = (.ok (Source.Vals.cons (.memRef rfl argument) .nil,inside),(.nil,state)) := by
    change ((Except.ok ((Source.Vals.cons (inside.get argIndex) .nil : Source.Vals E.layout [.bytes .memory]),inside), (Source.Locals.nil,state)) :
      Except Source.Halt (Source.Vals E.layout [.bytes .memory] × Source.Locals E.layout Γ) × Source.EMState E []) = _
    rw [argRef]
  rw [args]
  dsimp only [invocation]
  rw [lookup_empty]
  dsimp only [emptyBody,postBody]
  rw [dif_pos (show ([Source.STy.bytes .memory] : Source.RCtx).reverseAux [] = [Source.STy.bytes .memory] from rfl),Source.Hoare.run_bind]
  have read : (Source.EM.st : Source.EM E [] _).run (.nil,state) = (.ok state,(.nil,state)) := rfl
  rw [read]
  dsimp only
  rw [Source.Hoare.run_bind]
  dsimp only [ModifierPhysical.body]
  have install : (Source.EM.modSt (fun s : Source.St E=>{s with fnLocals:=⟨Γ,inside⟩}) : Source.EM E [] Unit).run
      (.nil,state) = (.ok (),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl
  rw [install]
  dsimp only
  rw [Source.Hoare.run_bind,AttemptPhysical.attempt_run]
  dsimp only [Source.Vals.onto,Source.L0,List.length_cons,List.length_nil]
  have ran : (Source.execItems (emptyProgram G) F (fuel+7) 1
      (some ⟨ModifierPhysical.body bodyIndex,[],inside⟩) (emptyBody E).items
      (.cons (.memRef rfl argument) .nil)).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.ok (.normal (.cons (.memRef rfl argument) .nil)),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl
  dsimp only [emptyBody,postBody,ModifierPhysical.body] at ran
  rw [ran]
  change (if e : Γ=Γ then (pure (e ▸ inside) : Source.EM E [] _) else Source.EM.halt (.stuck "modifier frame")).run
    (.nil,{state with fnLocals:=state.fnLocals}) = _
  rw [dif_pos rfl]
  rfl


theorem missing_body {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (bodyIndex argIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.runMods (ModifierPhysical.noBodies G) F (fuel+3) (ModifierPhysical.body bodyIndex)
      [invocation argIndex] inside).run (.nil,state) =
      (.error (.stuck "modifier without a body"),(.nil,state)) := by
  rw [Source.runMods]
  rfl

def badProgram {E : Source.Env} (G : Source.Glob E) : Source.Glob E :=
  {G with prog:={G.prog with body:=fun _=>some (ModifierPhysical.aroundBody E)}}
theorem wrong_parameters {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (bodyIndex argIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.runMods (badProgram G) F (fuel+3) (ModifierPhysical.body bodyIndex)
      [invocation argIndex] inside).run (.nil,state) =
      (.error (.stuck "modifier parameters"),(.nil,state)) := by
  rw [Source.runMods]
  rfl

def callerState (bytes : List UInt8) : Source.St originEnv :=
  {(UncheckedLoopPhysical.sampleRaw bytes).2 with
    fnLocals:=⟨[Source.STy.bool],Source.Locals.cons (.bool true) .nil⟩
    events:=[.credit account (word 9),.credit account (word 17)]}
def raw (bytes : List UInt8) : LocalState originEnv ctx.tys := (AttemptPhysical.input.1,callerState bytes)
def execute {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (code : Source.RBody E) (mods : List (Source.RModInv E code.locals))
    (inside : Source.Locals E.layout code.locals) : Source.EM E Γ (Source.Locals E.layout code.locals) := do
  let (out,_) ← Source.EM.sub .nil (Source.runMods G F fuel code mods inside)
  pure out

def sample (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :=
  (AttemptPhysical.companion
    (execute (program G) packedStepFrame fuel (ModifierPhysical.body .here)
      [invocation (.there .here)] (UncheckedLoopPhysical.sampleInside bytes))
    ScopeCatchPhysical.outer (raw bytes),firstPhysical.1.2,firstPhysical.2)

theorem sample_run (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    sample G bytes (fuel+8) =
      (((.ok (.error (.revert bytes)),(ScopeCatchPhysical.outer,callerState bytes)),raw bytes),firstPhysical.1.2,firstPhysical.2) := by
  unfold sample
  rw [AttemptPhysical.companion_actual]
  unfold execute
  rw [Source.Hoare.run_bind,ScopeCatchPhysical.sub_run,
    modifier_revert G packedStepFrame fuel 1 0 bytes .here (.there .here) _ _ rfl rfl]
  · rfl
  · exact Source.Heap.alloc_get _ _

theorem sample_dead (G : Source.Glob originEnv) :
    (sample G [0xde,0xad] 8).1.1.1 = .ok (.error (.revert [0xde,0xad])) := by rw [sample_run G _ 0]
theorem sample_empty (G : Source.Glob originEnv) :
    (sample G [] 8).1.1.1 = .ok (.error (.revert [])) := by rw [sample_run G _ 0]
theorem sample_panic (G : Source.Glob originEnv) :
    (sample G (Source.panicData .assert) 8).1.1.1 = .ok (.error (.revert (Source.panicData .assert))) := by rw [sample_run G _ 0]

theorem placeholder_entry {E : Source.Env} {Γ Δ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (index : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (modifierLocals : Source.Locals E.layout Δ) (state : Source.St E) :
    (Source.execS G F (fuel+1) nps (some ⟨ModifierPhysical.body index,[],inside⟩)
      (.placeholder rfl : Source.RStmt E [] true .body Δ Δ) modifierLocals).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
    ((do let out ← Source.runMods G F fuel (ModifierPhysical.body index) [] inside
         Source.EM.modSt fun s=>{s with fnLocals:=⟨Γ,out⟩}
         pure (.normal modifierLocals) : Source.EM E [] (Source.Out E.layout Δ Δ)).run (.nil,{state with fnLocals:=⟨Γ,inside⟩})) := by
  rw [Source.execS,Source.Hoare.run_bind]
  have read : (Source.EM.st : Source.EM E [] _).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
    (.ok {state with fnLocals:=⟨Γ,inside⟩},(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl
  rw [read]
  dsimp only [ModifierPhysical.body]
  rw [dif_pos rfl]
  cases pipeline : G.pipeline <;> rfl


theorem placeholder_low_1 {E : Source.Env} {Γ Δ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (nps : Nat) (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (modifierLocals : Source.Locals E.layout Δ) (state : Source.St E) :
    (Source.execS G F 1 nps (some ⟨ModifierPhysical.body index,[],inside⟩)
      (.placeholder rfl : Source.RStmt E [] true .body Δ Δ) modifierLocals).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error .timeout,(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := by
  rw [placeholder_entry G F 0]
  rfl

theorem placeholder_low_2 {E : Source.Env} {Γ Δ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (nps : Nat) (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (modifierLocals : Source.Locals E.layout Δ) (state : Source.St E) :
    (Source.execS G F 2 nps (some ⟨ModifierPhysical.body index,[],inside⟩)
      (.placeholder rfl : Source.RStmt E [] true .body Δ Δ) modifierLocals).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error .timeout,(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := by
  rw [placeholder_entry G F 1]
  rfl

theorem placeholder_low_3 {E : Source.Env} {Γ Δ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (nps : Nat) (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (modifierLocals : Source.Locals E.layout Δ) (state : Source.St E) :
    (Source.execS G F 3 nps (some ⟨ModifierPhysical.body index,[],inside⟩)
      (.placeholder rfl : Source.RStmt E [] true .body Δ Δ) modifierLocals).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error .timeout,(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := by
  rw [placeholder_entry G F 2]
  rfl

theorem placeholder_low_4 {E : Source.Env} {Γ Δ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (nps : Nat) (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (modifierLocals : Source.Locals E.layout Δ) (state : Source.St E) :
    (Source.execS G F 4 nps (some ⟨ModifierPhysical.body index,[],inside⟩)
      (.placeholder rfl : Source.RStmt E [] true .body Δ Δ) modifierLocals).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error .timeout,(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := by
  rw [placeholder_entry G F 3]
  rfl

theorem post_items_low_0 {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (argument : Source.Val E.layout (.bytes .memory)) (state : Source.St E) :
    (Source.execItems G F 0 1 (some ⟨ModifierPhysical.body index,[],inside⟩) (postBody E).items
      (.cons argument .nil)).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error .timeout,(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl

theorem post_items_low_1 {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (argument : Source.Val E.layout (.bytes .memory)) (state : Source.St E) :
    (Source.execItems G F 1 1 (some ⟨ModifierPhysical.body index,[],inside⟩) (postBody E).items
      (.cons argument .nil)).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error .timeout,(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl

theorem post_items_low_2 {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (argument : Source.Val E.layout (.bytes .memory)) (state : Source.St E) :
    (Source.execItems G F 2 1 (some ⟨ModifierPhysical.body index,[],inside⟩) (postBody E).items
      (.cons argument .nil)).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error .timeout,(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl

theorem post_items_low_3 {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (argument : Source.Val E.layout (.bytes .memory)) (state : Source.St E) :
    (Source.execItems G F 3 1 (some ⟨ModifierPhysical.body index,[],inside⟩) (postBody E).items
      (.cons argument .nil)).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error .timeout,(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := by
  unfold postBody
  rw [Source.execItems,Source.Hoare.run_bind,UncheckedLoopPhysical.declare]
  dsimp only
  rw [Source.Hoare.run_bind,Source.execItems,Source.Hoare.run_bind,placeholder_low_1 G F 1 index inside _ state]

theorem post_items_low_4 {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (argument : Source.Val E.layout (.bytes .memory)) (state : Source.St E) :
    (Source.execItems G F 4 1 (some ⟨ModifierPhysical.body index,[],inside⟩) (postBody E).items
      (.cons argument .nil)).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error .timeout,(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := by
  unfold postBody
  rw [Source.execItems,Source.Hoare.run_bind,UncheckedLoopPhysical.declare]
  dsimp only
  rw [Source.Hoare.run_bind,Source.execItems,Source.Hoare.run_bind,placeholder_low_2 G F 1 index inside _ state]

theorem post_items_low_5 {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (argument : Source.Val E.layout (.bytes .memory)) (state : Source.St E) :
    (Source.execItems G F 5 1 (some ⟨ModifierPhysical.body index,[],inside⟩) (postBody E).items
      (.cons argument .nil)).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error .timeout,(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := by
  unfold postBody
  rw [Source.execItems,Source.Hoare.run_bind,UncheckedLoopPhysical.declare]
  dsimp only
  rw [Source.Hoare.run_bind,Source.execItems,Source.Hoare.run_bind,placeholder_low_3 G F 1 index inside _ state]

theorem post_items_low_6 {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (argument : Source.Val E.layout (.bytes .memory)) (state : Source.St E) :
    (Source.execItems G F 6 1 (some ⟨ModifierPhysical.body index,[],inside⟩) (postBody E).items
      (.cons argument .nil)).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error .timeout,(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := by
  unfold postBody
  rw [Source.execItems,Source.Hoare.run_bind,UncheckedLoopPhysical.declare]
  dsimp only
  rw [Source.Hoare.run_bind,Source.execItems,Source.Hoare.run_bind,placeholder_low_4 G F 1 index inside _ state]

theorem body_low_0 {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (bodyIndex argIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.runMods (program G) F 0 (ModifierPhysical.body bodyIndex) [invocation argIndex] inside).run (.nil,state) =
      (.error .timeout,(.nil,state)) := rfl

theorem body_low_1 {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (bodyIndex argIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.runMods (program G) F 1 (ModifierPhysical.body bodyIndex) [invocation argIndex] inside).run (.nil,state) =
      (.error .timeout,(.nil,state)) := rfl

theorem body_low_2 {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (bodyIndex argIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.runMods (program G) F 2 (ModifierPhysical.body bodyIndex) [invocation argIndex] inside).run (.nil,state) =
      (.error .timeout,(.nil,state)) := rfl

theorem body_low_3 {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (bodyIndex argIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.runMods (program G) F 3 (ModifierPhysical.body bodyIndex) [invocation argIndex] inside).run (.nil,state) =
      (.error .timeout,(.nil,state)) := by
  rw [Source.runMods,Source.Hoare.run_bind]
  have args : (Source.EM.sub inside (Source.evalConvArgs (program G) F 2 (invocation argIndex).args) : Source.EM E [] _).run
      (.nil,state) = (.ok (Source.Vals.cons (inside.get argIndex) .nil,inside),(.nil,state)) := by
    change ((Except.ok ((Source.Vals.cons (inside.get argIndex) .nil : Source.Vals E.layout [.bytes .memory]),inside), (Source.Locals.nil,state)) :
      Except Source.Halt (Source.Vals E.layout [.bytes .memory] × Source.Locals E.layout Γ) × Source.EMState E []) = _
    rfl
  rw [args]
  dsimp only [invocation]
  rw [lookup_post]
  dsimp only [postBody]
  rw [dif_pos (show ([Source.STy.bytes .memory] : Source.RCtx).reverseAux [] = [Source.STy.bytes .memory] from rfl),Source.Hoare.run_bind]
  have read : (Source.EM.st : Source.EM E [] _).run (.nil,state) = (.ok state,(.nil,state)) := rfl
  rw [read]
  dsimp only
  rw [Source.Hoare.run_bind]
  dsimp only [ModifierPhysical.body]
  have install : (Source.EM.modSt (fun s : Source.St E=>{s with fnLocals:=⟨Γ,inside⟩}) : Source.EM E [] Unit).run
      (.nil,state) = (.ok (),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl
  rw [install]
  dsimp only
  rw [Source.Hoare.run_bind,AttemptPhysical.attempt_run]
  have ran := post_items_low_2 (program G) F bodyIndex inside (inside.get argIndex) state
  dsimp only [ModifierPhysical.body,postBody] at ran
  dsimp only [Source.Vals.onto,Source.L0,List.length_cons,List.length_nil]
  rw [ran]
  rfl

theorem body_low_4 {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (bodyIndex argIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.runMods (program G) F 4 (ModifierPhysical.body bodyIndex) [invocation argIndex] inside).run (.nil,state) =
      (.error .timeout,(.nil,state)) := by
  rw [Source.runMods,Source.Hoare.run_bind]
  have args : (Source.EM.sub inside (Source.evalConvArgs (program G) F 3 (invocation argIndex).args) : Source.EM E [] _).run
      (.nil,state) = (.ok (Source.Vals.cons (inside.get argIndex) .nil,inside),(.nil,state)) := by
    change ((Except.ok ((Source.Vals.cons (inside.get argIndex) .nil : Source.Vals E.layout [.bytes .memory]),inside), (Source.Locals.nil,state)) :
      Except Source.Halt (Source.Vals E.layout [.bytes .memory] × Source.Locals E.layout Γ) × Source.EMState E []) = _
    rfl
  rw [args]
  dsimp only [invocation]
  rw [lookup_post]
  dsimp only [postBody]
  rw [dif_pos (show ([Source.STy.bytes .memory] : Source.RCtx).reverseAux [] = [Source.STy.bytes .memory] from rfl),Source.Hoare.run_bind]
  have read : (Source.EM.st : Source.EM E [] _).run (.nil,state) = (.ok state,(.nil,state)) := rfl
  rw [read]
  dsimp only
  rw [Source.Hoare.run_bind]
  dsimp only [ModifierPhysical.body]
  have install : (Source.EM.modSt (fun s : Source.St E=>{s with fnLocals:=⟨Γ,inside⟩}) : Source.EM E [] Unit).run
      (.nil,state) = (.ok (),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl
  rw [install]
  dsimp only
  rw [Source.Hoare.run_bind,AttemptPhysical.attempt_run]
  have ran := post_items_low_3 (program G) F bodyIndex inside (inside.get argIndex) state
  dsimp only [ModifierPhysical.body,postBody] at ran
  dsimp only [Source.Vals.onto,Source.L0,List.length_cons,List.length_nil]
  rw [ran]
  rfl

theorem body_low_5 {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (bodyIndex argIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.runMods (program G) F 5 (ModifierPhysical.body bodyIndex) [invocation argIndex] inside).run (.nil,state) =
      (.error .timeout,(.nil,state)) := by
  rw [Source.runMods,Source.Hoare.run_bind]
  have args : (Source.EM.sub inside (Source.evalConvArgs (program G) F 4 (invocation argIndex).args) : Source.EM E [] _).run
      (.nil,state) = (.ok (Source.Vals.cons (inside.get argIndex) .nil,inside),(.nil,state)) := by
    change ((Except.ok ((Source.Vals.cons (inside.get argIndex) .nil : Source.Vals E.layout [.bytes .memory]),inside), (Source.Locals.nil,state)) :
      Except Source.Halt (Source.Vals E.layout [.bytes .memory] × Source.Locals E.layout Γ) × Source.EMState E []) = _
    rfl
  rw [args]
  dsimp only [invocation]
  rw [lookup_post]
  dsimp only [postBody]
  rw [dif_pos (show ([Source.STy.bytes .memory] : Source.RCtx).reverseAux [] = [Source.STy.bytes .memory] from rfl),Source.Hoare.run_bind]
  have read : (Source.EM.st : Source.EM E [] _).run (.nil,state) = (.ok state,(.nil,state)) := rfl
  rw [read]
  dsimp only
  rw [Source.Hoare.run_bind]
  dsimp only [ModifierPhysical.body]
  have install : (Source.EM.modSt (fun s : Source.St E=>{s with fnLocals:=⟨Γ,inside⟩}) : Source.EM E [] Unit).run
      (.nil,state) = (.ok (),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl
  rw [install]
  dsimp only
  rw [Source.Hoare.run_bind,AttemptPhysical.attempt_run]
  have ran := post_items_low_4 (program G) F bodyIndex inside (inside.get argIndex) state
  dsimp only [ModifierPhysical.body,postBody] at ran
  dsimp only [Source.Vals.onto,Source.L0,List.length_cons,List.length_nil]
  rw [ran]
  rfl

theorem body_low_6 {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (bodyIndex argIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.runMods (program G) F 6 (ModifierPhysical.body bodyIndex) [invocation argIndex] inside).run (.nil,state) =
      (.error .timeout,(.nil,state)) := by
  rw [Source.runMods,Source.Hoare.run_bind]
  have args : (Source.EM.sub inside (Source.evalConvArgs (program G) F 5 (invocation argIndex).args) : Source.EM E [] _).run
      (.nil,state) = (.ok (Source.Vals.cons (inside.get argIndex) .nil,inside),(.nil,state)) := by
    change ((Except.ok ((Source.Vals.cons (inside.get argIndex) .nil : Source.Vals E.layout [.bytes .memory]),inside), (Source.Locals.nil,state)) :
      Except Source.Halt (Source.Vals E.layout [.bytes .memory] × Source.Locals E.layout Γ) × Source.EMState E []) = _
    rfl
  rw [args]
  dsimp only [invocation]
  rw [lookup_post]
  dsimp only [postBody]
  rw [dif_pos (show ([Source.STy.bytes .memory] : Source.RCtx).reverseAux [] = [Source.STy.bytes .memory] from rfl),Source.Hoare.run_bind]
  have read : (Source.EM.st : Source.EM E [] _).run (.nil,state) = (.ok state,(.nil,state)) := rfl
  rw [read]
  dsimp only
  rw [Source.Hoare.run_bind]
  dsimp only [ModifierPhysical.body]
  have install : (Source.EM.modSt (fun s : Source.St E=>{s with fnLocals:=⟨Γ,inside⟩}) : Source.EM E [] Unit).run
      (.nil,state) = (.ok (),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl
  rw [install]
  dsimp only
  rw [Source.Hoare.run_bind,AttemptPhysical.attempt_run]
  have ran := post_items_low_5 (program G) F bodyIndex inside (inside.get argIndex) state
  dsimp only [ModifierPhysical.body,postBody] at ran
  dsimp only [Source.Vals.onto,Source.L0,List.length_cons,List.length_nil]
  rw [ran]
  rfl

theorem body_low_7 {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (bodyIndex argIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.runMods (program G) F 7 (ModifierPhysical.body bodyIndex) [invocation argIndex] inside).run (.nil,state) =
      (.error .timeout,(.nil,state)) := by
  rw [Source.runMods,Source.Hoare.run_bind]
  have args : (Source.EM.sub inside (Source.evalConvArgs (program G) F 6 (invocation argIndex).args) : Source.EM E [] _).run
      (.nil,state) = (.ok (Source.Vals.cons (inside.get argIndex) .nil,inside),(.nil,state)) := by
    change ((Except.ok ((Source.Vals.cons (inside.get argIndex) .nil : Source.Vals E.layout [.bytes .memory]),inside), (Source.Locals.nil,state)) :
      Except Source.Halt (Source.Vals E.layout [.bytes .memory] × Source.Locals E.layout Γ) × Source.EMState E []) = _
    rfl
  rw [args]
  dsimp only [invocation]
  rw [lookup_post]
  dsimp only [postBody]
  rw [dif_pos (show ([Source.STy.bytes .memory] : Source.RCtx).reverseAux [] = [Source.STy.bytes .memory] from rfl),Source.Hoare.run_bind]
  have read : (Source.EM.st : Source.EM E [] _).run (.nil,state) = (.ok state,(.nil,state)) := rfl
  rw [read]
  dsimp only
  rw [Source.Hoare.run_bind]
  dsimp only [ModifierPhysical.body]
  have install : (Source.EM.modSt (fun s : Source.St E=>{s with fnLocals:=⟨Γ,inside⟩}) : Source.EM E [] Unit).run
      (.nil,state) = (.ok (),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl
  rw [install]
  dsimp only
  rw [Source.Hoare.run_bind,AttemptPhysical.attempt_run]
  have ran := post_items_low_6 (program G) F bodyIndex inside (inside.get argIndex) state
  dsimp only [ModifierPhysical.body,postBody] at ran
  dsimp only [Source.Vals.onto,Source.L0,List.length_cons,List.length_nil]
  rw [ran]
  rfl

theorem body_low {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (bodyIndex argIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    ([0,1,2,3,4,5,6,7].map fun fuel=>(Source.runMods (program G) F fuel (ModifierPhysical.body bodyIndex)
      [invocation argIndex] inside).run (.nil,state)) =
      List.replicate 8 (.error .timeout,(Source.Locals.nil,state)) := by
  simp only [List.map_cons,List.map_nil,body_low_0,body_low_1,body_low_2,body_low_3,
    body_low_4,body_low_5,body_low_6,body_low_7]
  rfl

end Solidity.Yul.Composition.ModifierPostPhysical
