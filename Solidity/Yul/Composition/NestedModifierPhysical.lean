import Solidity.Yul.Composition.ModifierPostPhysical

/-! Actual two-modifier consumers. Distinct declaration/argument identities,
real nested placeholders and two saved-frame restorations; no frontend Derived,
general modifier adequacy or raw-to-clean resumption claim. -/
namespace Solidity.Yul.Composition.NestedModifierPhysical
open Solidity.Yul.Views Solidity.Yul.Views.Controls LocalPhysicalControls

def outerDecl : Source.Decl :=
  ⟨.modifier,"ownedOuter",none,false,
    .modifier "ownedOuter" (.some (.cons (.param (.elem .bytes) (some .memory) (some "tail")) .nil)) false none
      (.some (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "_")))) .nil)))⟩
def outerInvocation {E : Source.Env} {Γ : Source.RCtx} (index : Source.Idx Γ (.bytes .memory)) : Source.RModInv E Γ :=
  ⟨outerDecl,[.bytes .memory],.cons (.local index) rfl .nil⟩
def outerBase {E : Source.Env} (G : Source.Glob E) : Source.Glob E :=
  {G with prog:={G.prog with body:=fun d=>if d.name="ownedOuter" then some (ModifierPostPhysical.postBody E) else G.prog.body d}}
def program {E : Source.Env} (G : Source.Glob E) : Source.Glob E := ModifierPostPhysical.program (outerBase G)
theorem lookup_outer {E : Source.Env} (G : Source.Glob E) (F : Source.Fr) :
    (program G).prog.body ((program G).dispatchMod F.contract outerDecl) = some (ModifierPostPhysical.postBody E) := rfl
theorem lookup_inner {E : Source.Env} (G : Source.Glob E) (F : Source.Fr) :
    (program G).prog.body ((program G).dispatchMod F.contract ModifierPostPhysical.postDecl) = some (ModifierPostPhysical.postBody E) := rfl

theorem placeholder_plain {E : Source.Env} {Γ Δ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel argument : Nat) (bytes : List UInt8) (returns : Bool) (innerIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (modifierLocals : Source.Locals E.layout Δ) (state : Source.St E)
    (reference : inside.get innerIndex=.memRef rfl argument)
    (found : state.heap.get argument=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execS (program G) F (fuel+9) 1 (some ⟨ModifierPostPhysical.plain E Γ returns,[ModifierPostPhysical.invocation innerIndex],inside⟩)
      (.placeholder rfl : Source.RStmt E [] true .body Δ Δ) modifierLocals).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error (.revert bytes),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := by
  rw [Source.execS,Source.Hoare.run_bind]
  have read : (Source.EM.st : Source.EM E [] _).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.ok {state with fnLocals:=⟨Γ,inside⟩},(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl
  rw [read]
  dsimp only [ModifierPostPhysical.plain]
  rw [dif_pos rfl]
  change ((do
    let lin ← match G.pipeline with
      | .legacy=>pure inside
      | .viaIR=>Source.zeroInner (fuel+8) 0 inside
    let out ← Source.runMods (program G) F (fuel+8) (ModifierPostPhysical.plain E Γ returns) [ModifierPostPhysical.invocation innerIndex] lin
    Source.EM.modSt fun st=>{st with fnLocals:=⟨Γ,out⟩}
    pure (.normal modifierLocals) : Source.EM E [] (Source.Out E.layout Δ Δ)).run (.nil,{state with fnLocals:=⟨Γ,inside⟩})) = _
  cases pipeline : G.pipeline <;>
    change ((do
      let out ← Source.runMods (program G) F (fuel+8) (ModifierPostPhysical.plain E Γ returns) [ModifierPostPhysical.invocation innerIndex] inside
      Source.EM.modSt fun st=>{st with fnLocals:=⟨Γ,out⟩}
      pure (.normal modifierLocals) : Source.EM E [] (Source.Out E.layout Δ Δ)).run (.nil,{state with fnLocals:=⟨Γ,inside⟩})) = _
  all_goals
    dsimp only [program]
    rw [Source.Hoare.run_bind,ModifierPostPhysical.modifier_plain (outerBase G) F fuel argument bytes returns innerIndex inside {state with fnLocals:=⟨Γ,inside⟩} reference found]

/-- The outer postlude is unreachable because the ACTUAL nested run reverts. -/
theorem outer_items_plain {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel argument outerArgument : Nat) (bytes : List UInt8) (returns : Bool) (innerIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (state : Source.St E)
    (reference : inside.get innerIndex=.memRef rfl argument)
    (found : state.heap.get argument=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execItems (program G) F (fuel+11) 1
      (some ⟨ModifierPostPhysical.plain E Γ returns,[ModifierPostPhysical.invocation innerIndex],inside⟩)
      (ModifierPostPhysical.postBody E).items (.cons (.memRef rfl outerArgument) .nil)).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error (.revert bytes),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := by
  unfold ModifierPostPhysical.postBody
  rw [Source.execItems,Source.Hoare.run_bind,UncheckedLoopPhysical.declare]
  dsimp only
  rw [Source.Hoare.run_bind,Source.execItems,Source.Hoare.run_bind,
    placeholder_plain G F fuel argument bytes returns innerIndex inside _ state reference found]

theorem nested_plain {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel argument outerArgument : Nat) (bytes : List UInt8) (returns : Bool)
    (outerIndex innerIndex : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ) (state : Source.St E)
    (outerRef : inside.get outerIndex=.memRef rfl outerArgument)
    (reference : inside.get innerIndex=.memRef rfl argument)
    (found : state.heap.get argument=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.runMods (program G) F (fuel+12) (ModifierPostPhysical.plain E Γ returns)
      [outerInvocation outerIndex,ModifierPostPhysical.invocation innerIndex] inside).run (.nil,state) =
      (.error (.revert bytes),(.nil,state)) := by
  rw [Source.runMods,Source.Hoare.run_bind]
  have args : (Source.EM.sub inside (Source.evalConvArgs (program G) F (fuel+11) (outerInvocation outerIndex).args) : Source.EM E [] _).run
      (.nil,state) = (.ok (Source.Vals.cons (.memRef rfl outerArgument) .nil,inside),(.nil,state)) := by
    change ((Except.ok ((Source.Vals.cons (inside.get outerIndex) .nil : Source.Vals E.layout [.bytes .memory]),inside),(Source.Locals.nil,state)) :
      Except Source.Halt (Source.Vals E.layout [.bytes .memory] × Source.Locals E.layout Γ) × Source.EMState E []) = _
    rw [outerRef]
  rw [args]
  dsimp only [outerInvocation]
  rw [lookup_outer]
  dsimp only [ModifierPostPhysical.postBody]
  rw [dif_pos (show ([Source.STy.bytes .memory] : Source.RCtx).reverseAux [] = [Source.STy.bytes .memory] from rfl),Source.Hoare.run_bind]
  have read : (Source.EM.st : Source.EM E [] _).run (.nil,state) = (.ok state,(.nil,state)) := rfl
  rw [read]
  dsimp only
  rw [Source.Hoare.run_bind]
  dsimp only [ModifierPostPhysical.plain]
  have install : (Source.EM.modSt (fun st : Source.St E=>{st with fnLocals:=⟨Γ,inside⟩}) : Source.EM E [] Unit).run
      (.nil,state) = (.ok (),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl
  rw [install]
  dsimp only
  rw [Source.Hoare.run_bind,AttemptPhysical.attempt_run]
  have ran := outer_items_plain G F fuel argument outerArgument bytes returns innerIndex inside state reference found
  dsimp only [ModifierPostPhysical.plain,ModifierPostPhysical.postBody] at ran
  dsimp only [Source.Vals.onto,Source.L0,List.length_cons,List.length_nil]
  rw [ran]
  rfl

theorem placeholder_revert {E : Source.Env} {Γ Δ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel bodyAddress argument : Nat) (bytes : List UInt8) (bodyIndex : Source.Idx Γ (.bytes .memory)) (innerIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (modifierLocals : Source.Locals E.layout Δ) (state : Source.St E)
    (reference : inside.get bodyIndex=.memRef rfl bodyAddress)
    (innerRef : inside.get innerIndex=.memRef rfl argument)
    (found : state.heap.get bodyAddress=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execS (program G) F (fuel+9) 1 (some ⟨ModifierPhysical.body bodyIndex,[ModifierPostPhysical.invocation innerIndex],inside⟩)
      (.placeholder rfl : Source.RStmt E [] true .body Δ Δ) modifierLocals).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error (.revert bytes),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := by
  rw [Source.execS,Source.Hoare.run_bind]
  have read : (Source.EM.st : Source.EM E [] _).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.ok {state with fnLocals:=⟨Γ,inside⟩},(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl
  rw [read]
  dsimp only [ModifierPhysical.body]
  rw [dif_pos rfl]
  change ((do
    let lin ← match G.pipeline with
      | .legacy=>pure inside
      | .viaIR=>Source.zeroInner (fuel+8) 0 inside
    let out ← Source.runMods (program G) F (fuel+8) (ModifierPhysical.body bodyIndex) [ModifierPostPhysical.invocation innerIndex] lin
    Source.EM.modSt fun st=>{st with fnLocals:=⟨Γ,out⟩}
    pure (.normal modifierLocals) : Source.EM E [] (Source.Out E.layout Δ Δ)).run (.nil,{state with fnLocals:=⟨Γ,inside⟩})) = _
  cases pipeline : G.pipeline <;>
    change ((do
      let out ← Source.runMods (program G) F (fuel+8) (ModifierPhysical.body bodyIndex) [ModifierPostPhysical.invocation innerIndex] inside
      Source.EM.modSt fun st=>{st with fnLocals:=⟨Γ,out⟩}
      pure (.normal modifierLocals) : Source.EM E [] (Source.Out E.layout Δ Δ)).run (.nil,{state with fnLocals:=⟨Γ,inside⟩})) = _
  all_goals
    dsimp only [program]
    rw [Source.Hoare.run_bind,ModifierPostPhysical.modifier_revert (outerBase G) F fuel bodyAddress argument bytes bodyIndex innerIndex inside {state with fnLocals:=⟨Γ,inside⟩} reference innerRef found]

/-- The outer postlude is unreachable because the ACTUAL nested run reverts. -/
theorem outer_items_revert {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel bodyAddress argument outerArgument : Nat) (bytes : List UInt8) (bodyIndex : Source.Idx Γ (.bytes .memory)) (innerIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (state : Source.St E)
    (reference : inside.get bodyIndex=.memRef rfl bodyAddress)
    (innerRef : inside.get innerIndex=.memRef rfl argument)
    (found : state.heap.get bodyAddress=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execItems (program G) F (fuel+11) 1
      (some ⟨ModifierPhysical.body bodyIndex,[ModifierPostPhysical.invocation innerIndex],inside⟩)
      (ModifierPostPhysical.postBody E).items (.cons (.memRef rfl outerArgument) .nil)).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error (.revert bytes),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := by
  unfold ModifierPostPhysical.postBody
  rw [Source.execItems,Source.Hoare.run_bind,UncheckedLoopPhysical.declare]
  dsimp only
  rw [Source.Hoare.run_bind,Source.execItems,Source.Hoare.run_bind,
    placeholder_revert G F fuel bodyAddress argument bytes bodyIndex innerIndex inside _ state reference innerRef found]

theorem nested_revert {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel bodyAddress argument outerArgument : Nat) (bytes : List UInt8) (bodyIndex : Source.Idx Γ (.bytes .memory))
    (outerIndex innerIndex : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ) (state : Source.St E)
    (outerRef : inside.get outerIndex=.memRef rfl outerArgument)
    (reference : inside.get bodyIndex=.memRef rfl bodyAddress)
    (innerRef : inside.get innerIndex=.memRef rfl argument)
    (found : state.heap.get bodyAddress=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.runMods (program G) F (fuel+12) (ModifierPhysical.body bodyIndex)
      [outerInvocation outerIndex,ModifierPostPhysical.invocation innerIndex] inside).run (.nil,state) =
      (.error (.revert bytes),(.nil,state)) := by
  rw [Source.runMods,Source.Hoare.run_bind]
  have args : (Source.EM.sub inside (Source.evalConvArgs (program G) F (fuel+11) (outerInvocation outerIndex).args) : Source.EM E [] _).run
      (.nil,state) = (.ok (Source.Vals.cons (.memRef rfl outerArgument) .nil,inside),(.nil,state)) := by
    change ((Except.ok ((Source.Vals.cons (inside.get outerIndex) .nil : Source.Vals E.layout [.bytes .memory]),inside),(Source.Locals.nil,state)) :
      Except Source.Halt (Source.Vals E.layout [.bytes .memory] × Source.Locals E.layout Γ) × Source.EMState E []) = _
    rw [outerRef]
  rw [args]
  dsimp only [outerInvocation]
  rw [lookup_outer]
  dsimp only [ModifierPostPhysical.postBody]
  rw [dif_pos (show ([Source.STy.bytes .memory] : Source.RCtx).reverseAux [] = [Source.STy.bytes .memory] from rfl),Source.Hoare.run_bind]
  have read : (Source.EM.st : Source.EM E [] _).run (.nil,state) = (.ok state,(.nil,state)) := rfl
  rw [read]
  dsimp only
  rw [Source.Hoare.run_bind]
  dsimp only [ModifierPhysical.body]
  have install : (Source.EM.modSt (fun st : Source.St E=>{st with fnLocals:=⟨Γ,inside⟩}) : Source.EM E [] Unit).run
      (.nil,state) = (.ok (),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl
  rw [install]
  dsimp only
  rw [Source.Hoare.run_bind,AttemptPhysical.attempt_run]
  have ran := outer_items_revert G F fuel bodyAddress argument outerArgument bytes bodyIndex innerIndex inside state reference innerRef found
  dsimp only [ModifierPhysical.body,ModifierPostPhysical.postBody] at ran
  dsimp only [Source.Vals.onto,Source.L0,List.length_cons,List.length_nil]
  rw [ran]
  rfl

/-- Timeout after the outer alias/placeholder and entered inner frame: both
actual runMods restorations still run. No body/read outcome is assumed. -/
theorem placeholder_late_timeout {E : Source.Env} {Γ Δ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (bodyIndex innerIndex : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (modifierLocals : Source.Locals E.layout Δ) (state : Source.St E) :
    (Source.execS (program G) F 8 1
      (some ⟨ModifierPhysical.body bodyIndex,[ModifierPostPhysical.invocation innerIndex],inside⟩)
      (.placeholder rfl : Source.RStmt E [] true .body Δ Δ) modifierLocals).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error .timeout,(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := by
  rw [Source.execS,Source.Hoare.run_bind]
  have read : (Source.EM.st : Source.EM E [] _).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.ok {state with fnLocals:=⟨Γ,inside⟩},(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl
  rw [read]
  dsimp only [ModifierPhysical.body]
  rw [dif_pos rfl]
  change ((do
    let lin ← match G.pipeline with | .legacy=>pure inside | .viaIR=>Source.zeroInner 7 0 inside
    let out ← Source.runMods (program G) F 7 (ModifierPhysical.body bodyIndex) [ModifierPostPhysical.invocation innerIndex] lin
    Source.EM.modSt fun st=>{st with fnLocals:=⟨Γ,out⟩}
    pure (.normal modifierLocals) : Source.EM E [] (Source.Out E.layout Δ Δ)).run (.nil,{state with fnLocals:=⟨Γ,inside⟩})) = _
  cases pipeline : G.pipeline <;>
    change ((do
      let out ← Source.runMods (program G) F 7 (ModifierPhysical.body bodyIndex) [ModifierPostPhysical.invocation innerIndex] inside
      Source.EM.modSt fun st=>{st with fnLocals:=⟨Γ,out⟩}
      pure (.normal modifierLocals) : Source.EM E [] (Source.Out E.layout Δ Δ)).run (.nil,{state with fnLocals:=⟨Γ,inside⟩})) = _
  all_goals
    dsimp only [program]
    rw [Source.Hoare.run_bind,ModifierPostPhysical.body_low_7]

theorem outer_items_late_timeout {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (bodyIndex innerIndex : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (argument : Source.Val E.layout (.bytes .memory)) (state : Source.St E) :
    (Source.execItems (program G) F 10 1
      (some ⟨ModifierPhysical.body bodyIndex,[ModifierPostPhysical.invocation innerIndex],inside⟩)
      (ModifierPostPhysical.postBody E).items (.cons argument .nil)).run (.nil,{state with fnLocals:=⟨Γ,inside⟩}) =
      (.error .timeout,(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := by
  unfold ModifierPostPhysical.postBody
  rw [Source.execItems,Source.Hoare.run_bind,UncheckedLoopPhysical.declare]
  dsimp only
  rw [Source.Hoare.run_bind,Source.execItems,Source.Hoare.run_bind,placeholder_late_timeout]

theorem nested_late_timeout {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (bodyIndex outerIndex innerIndex : Source.Idx Γ (.bytes .memory))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.runMods (program G) F 11 (ModifierPhysical.body bodyIndex)
      [outerInvocation outerIndex,ModifierPostPhysical.invocation innerIndex] inside).run (.nil,state) =
      (.error .timeout,(.nil,state)) := by
  rw [Source.runMods,Source.Hoare.run_bind]
  have args : (Source.EM.sub inside (Source.evalConvArgs (program G) F 10 (outerInvocation outerIndex).args) : Source.EM E [] _).run
      (.nil,state) = (.ok (Source.Vals.cons (inside.get outerIndex) .nil,inside),(.nil,state)) := by
    change ((Except.ok ((Source.Vals.cons (inside.get outerIndex) .nil : Source.Vals E.layout [.bytes .memory]),inside),(Source.Locals.nil,state)) :
      Except Source.Halt (Source.Vals E.layout [.bytes .memory] × Source.Locals E.layout Γ) × Source.EMState E []) = _
    rfl
  rw [args]
  dsimp only [outerInvocation]
  rw [lookup_outer]
  dsimp only [ModifierPostPhysical.postBody]
  rw [dif_pos (show ([Source.STy.bytes .memory] : Source.RCtx).reverseAux [] = [Source.STy.bytes .memory] from rfl),Source.Hoare.run_bind]
  have read : (Source.EM.st : Source.EM E [] _).run (.nil,state) = (.ok state,(.nil,state)) := rfl
  rw [read]
  dsimp only
  rw [Source.Hoare.run_bind]
  dsimp only [ModifierPhysical.body]
  have install : (Source.EM.modSt (fun st : Source.St E=>{st with fnLocals:=⟨Γ,inside⟩}) : Source.EM E [] Unit).run
      (.nil,state) = (.ok (),(.nil,{state with fnLocals:=⟨Γ,inside⟩})) := rfl
  rw [install]
  dsimp only
  rw [Source.Hoare.run_bind,AttemptPhysical.attempt_run]
  have ran := outer_items_late_timeout G F bodyIndex innerIndex inside (inside.get outerIndex) state
  dsimp only [ModifierPhysical.body,ModifierPostPhysical.postBody] at ran
  dsimp only [Source.Vals.onto,Source.L0,List.length_cons,List.length_nil]
  rw [ran]
  rfl

abbrev Parameters := ModifierPhysical.Parameters

def plainSample (G : Source.Glob originEnv) (bytes : List UInt8) (returns : Bool) (fuel : Nat) :=
  (AttemptPhysical.companion
    (ModifierPostPhysical.execute (program G) packedStepFrame fuel (ModifierPostPhysical.plain originEnv Parameters returns)
      [outerInvocation .here,ModifierPostPhysical.invocation (.there .here)] (UncheckedLoopPhysical.sampleInside bytes))
    ScopeCatchPhysical.outer (ModifierPostPhysical.raw bytes),firstPhysical.1.2,firstPhysical.2)
def bodySample (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :=
  (AttemptPhysical.companion
    (ModifierPostPhysical.execute (program G) packedStepFrame fuel (ModifierPhysical.body .here)
      [outerInvocation .here,ModifierPostPhysical.invocation (.there .here)] (UncheckedLoopPhysical.sampleInside bytes))
    ScopeCatchPhysical.outer (ModifierPostPhysical.raw bytes),firstPhysical.1.2,firstPhysical.2)

theorem plain_sample_run (G : Source.Glob originEnv) (bytes : List UInt8) (returns : Bool) (fuel : Nat) :
    plainSample G bytes returns (fuel+12) =
      (((.ok (.error (.revert [0xaa,0xbb])),(ScopeCatchPhysical.outer,ModifierPostPhysical.callerState bytes)),
        ModifierPostPhysical.raw bytes),firstPhysical.1.2,firstPhysical.2) := by
  unfold plainSample
  rw [AttemptPhysical.companion_actual]
  unfold ModifierPostPhysical.execute
  rw [Source.Hoare.run_bind,ScopeCatchPhysical.sub_run,
    nested_plain G packedStepFrame fuel 0 1 [0xaa,0xbb] returns .here (.there .here) _ _ rfl rfl]
  · rfl
  · rfl

theorem body_sample_run (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    bodySample G bytes (fuel+12) =
      (((.ok (.error (.revert bytes)),(ScopeCatchPhysical.outer,ModifierPostPhysical.callerState bytes)),
        ModifierPostPhysical.raw bytes),firstPhysical.1.2,firstPhysical.2) := by
  unfold bodySample
  rw [AttemptPhysical.companion_actual]
  unfold ModifierPostPhysical.execute
  rw [Source.Hoare.run_bind,ScopeCatchPhysical.sub_run,
    nested_revert G packedStepFrame fuel 1 0 1 bytes .here .here (.there .here) _ _ rfl rfl rfl]
  · rfl
  · exact Source.Heap.alloc_get _ _

theorem plain_completed_stability (G : Source.Glob originEnv) (bytes : List UInt8) (returns : Bool) (left right : Nat) :
    plainSample G bytes returns (left+12)=plainSample G bytes returns (right+12) := by
  rw [plain_sample_run,plain_sample_run]
theorem body_completed_stability (G : Source.Glob originEnv) (bytes : List UInt8) (left right : Nat) :
    bodySample G bytes (left+12)=bodySample G bytes (right+12) := by rw [body_sample_run,body_sample_run]

theorem body_dead (G : Source.Glob originEnv) :
    (bodySample G [0xde,0xad] 12).1.1.1=.ok (.error (.revert [0xde,0xad])) := by rw [body_sample_run G _ 0]
theorem body_empty (G : Source.Glob originEnv) :
    (bodySample G [] 12).1.1.1=.ok (.error (.revert [])) := by rw [body_sample_run G _ 0]
theorem body_panic (G : Source.Glob originEnv) :
    (bodySample G (Source.panicData .assert) 12).1.1.1=.ok (.error (.revert (Source.panicData .assert))) := by rw [body_sample_run G _ 0]

theorem complete_caller (G : Source.Glob originEnv) (bytes : List UInt8) (returns : Bool) (fuel : Nat) :
    (plainSample G bytes returns (fuel+12)).1.2=ModifierPostPhysical.raw bytes := by rw [plain_sample_run]
theorem physical_journals (G : Source.Glob originEnv) (bytes : List UInt8) (returns : Bool) (fuel : Nat) :
    (plainSample G bytes returns (fuel+12)).2=(firstPhysical.1.2,firstPhysical.2) := by rw [plain_sample_run]

theorem zero {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (bodyIndex outerIndex innerIndex : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.runMods (program G) F 0 (ModifierPhysical.body bodyIndex)
      [outerInvocation outerIndex,ModifierPostPhysical.invocation innerIndex] inside).run (.nil,state) =
      (.error .timeout,(.nil,state)) := rfl

def carryPlain {E : Source.Env} {Γ Δ Λ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (returns : Bool) (outerIndex innerIndex : Source.Idx Δ (.bytes .memory))
    (inside : Source.Locals E.layout Δ) (outer : Source.Locals E.layout Γ) (raw : LocalState E Λ)
    (residual : ResidualJournal complementCarrierOwnership) (owned : BoolEncodingJournal) :=
  (AttemptPhysical.companion
    (ModifierPostPhysical.execute (program G) F fuel (ModifierPostPhysical.plain E Δ returns)
      [outerInvocation outerIndex,ModifierPostPhysical.invocation innerIndex] inside) outer raw,residual,owned)

theorem carry_plain_run {E : Source.Env} {Γ Δ Λ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel argument outerArgument : Nat) (bytes : List UInt8) (returns : Bool)
    (outerIndex innerIndex : Source.Idx Δ (.bytes .memory)) (inside : Source.Locals E.layout Δ)
    (outer : Source.Locals E.layout Γ) (raw : LocalState E Λ)
    (residual : ResidualJournal complementCarrierOwnership) (owned : BoolEncodingJournal)
    (outerRef : inside.get outerIndex=.memRef rfl outerArgument)
    (innerRef : inside.get innerIndex=.memRef rfl argument)
    (found : raw.2.heap.get argument=some ⟨.bytes .memory,.bytes bytes⟩) :
    carryPlain G F (fuel+12) returns outerIndex innerIndex inside outer raw residual owned =
      (((.ok (.error (.revert bytes)),(outer,raw.2)),raw),residual,owned) := by
  unfold carryPlain
  rw [AttemptPhysical.companion_actual]
  unfold ModifierPostPhysical.execute
  rw [Source.Hoare.run_bind,ScopeCatchPhysical.sub_run,
    nested_plain G F fuel argument outerArgument bytes returns outerIndex innerIndex inside raw.2 outerRef innerRef found]

/-- Same-type indices are not interchangeable: changing which inner argument
is read yields the new payload, not the old AABB alias. -/
theorem wrong_inner_argument (G : Source.Glob originEnv) (bytes : List UInt8) (returns : Bool) (fuel : Nat) :
    carryPlain G packedStepFrame (fuel+12) returns (.there .here) .here
      (UncheckedLoopPhysical.sampleInside bytes) ScopeCatchPhysical.outer (ModifierPostPhysical.raw bytes)
      firstPhysical.1.2 firstPhysical.2 =
      (((.ok (.error (.revert bytes)),(ScopeCatchPhysical.outer,ModifierPostPhysical.callerState bytes)),
        ModifierPostPhysical.raw bytes),firstPhysical.1.2,firstPhysical.2) := by
  apply carry_plain_run G packedStepFrame fuel 1 0 bytes returns (.there .here) .here
    (UncheckedLoopPhysical.sampleInside bytes) ScopeCatchPhysical.outer (ModifierPostPhysical.raw bytes)
    firstPhysical.1.2 firstPhysical.2 rfl rfl
  exact Source.Heap.alloc_get _ _

end Solidity.Yul.Composition.NestedModifierPhysical
