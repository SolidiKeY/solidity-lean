import Solidity.Yul.Composition.RuntimeBlockPhysical

/-! Owned consumers of ACTUAL runMods/placeholder machinery. These resolved
runtime programs do not assert frontend derivation or general modifier adequacy. -/
namespace Solidity.Yul.Composition.ModifierPhysical
open Solidity.Yul.Views Solidity.Yul.Views.Controls LocalPhysicalControls

/-- Actual modifier declaration key and single-placeholder resolved body.
No claim that the frontend has derived this runtime program is made. -/
def aroundDecl : Source.Decl :=
  ⟨.modifier,"ownedAround",none,false,
    .modifier "ownedAround" (.some .nil) false none
      (.some (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "_")))) .nil)))⟩

def aroundBody (E : Source.Env) : Source.RBody E where
  ps := []
  rs := []
  inModifier := true
  locals := []
  out := []
  items := .stmt (.placeholder rfl) .nil

def invocation (E : Source.Env) (Γ : Source.RCtx) : Source.RModInv E Γ := ⟨aroundDecl,[],.nil⟩


/-- Parameters account for the initial context; returns are empty. -/
def body {E : Source.Env} {Γ : Source.RCtx} (index : Source.Idx Γ (.bytes .memory)) : Source.RBody E where
  ps := Γ.reverse
  rs := []
  inModifier := false
  locals := Γ
  out := .bytes .memory::Γ
  items := RuntimeBlockPhysical.aliasItems index
  mods := [invocation E Γ]

/-- Parameter-count metadata is irrelevant for these actual local/rethrow leaves. -/
theorem body_items {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel address : Nat) (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory))
    (values : Source.Locals E.layout Γ) (state : Source.St E)
    (reference : values.get index = .memRef rfl address)
    (found : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execItems G F (fuel+3) (body (E:=E) index).ps.length none (body (E:=E) index).items values).run (.nil,state) =
      (Except.error (.revert bytes),(.nil,state)) := by
  exact RuntimeBlockPhysical.items_run G F fuel address bytes index values state reference found

theorem no_modifiers {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel address : Nat) (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory))
    (values : Source.Locals E.layout Γ) (state : Source.St E)
    (reference : values.get index = .memRef rfl address)
    (found : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.runMods G F (fuel+4) (body (E:=E) index) [] values).run (.nil,state) =
      (Except.error (.revert bytes),(.nil,state)) := by
  rw [Source.runMods,Source.Hoare.run_bind,body_items G F fuel address bytes index values state reference found]


def withAround {E : Source.Env} (G : Source.Glob E) : Source.Glob E :=
  {G with prog := {G.prog with body := fun d => if d.name = "ownedAround" then some (aroundBody E) else G.prog.body d}}

theorem lookup_around {E : Source.Env} (G : Source.Glob E) (F : Source.Fr) :
    (withAround G).prog.body ((withAround G).dispatchMod F.contract aroundDecl) = some (aroundBody E) := rfl

/-- The ACTUAL placeholder enters the rest/body through both pipeline branches.
There are no return slots to reset; parameters remain the supplied typed values. -/
theorem placeholder_revert {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel address : Nat) (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory))
    (values : Source.Locals E.layout Γ) (state : Source.St E)
    (reference : values.get index = .memRef rfl address)
    (found : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execS G F (fuel+5) 0 (some ⟨body (E:=E) index,[],values⟩)
      (.placeholder rfl : Source.RStmt E [] true .body [] []) .nil).run
      (.nil,{state with fnLocals:=⟨Γ,values⟩}) =
      (Except.error (.revert bytes),(.nil,{state with fnLocals:=⟨Γ,values⟩})) := by
  rw [Source.execS,Source.Hoare.run_bind]
  have readState : (Source.EM.st : Source.EM E [] _).run (.nil,{state with fnLocals:=⟨Γ,values⟩}) =
    (Except.ok {state with fnLocals:=⟨Γ,values⟩},(.nil,{state with fnLocals:=⟨Γ,values⟩})) := rfl
  rw [readState]
  dsimp only [body]
  rw [dif_pos rfl]
  change ((do
    let lin ← match G.pipeline with
      | .legacy => pure values
      | .viaIR => Source.zeroInner (fuel+4) 0 values
    let result ← Source.runMods G F (fuel+4) (body (E:=E) index) [] lin
    Source.EM.modSt fun s => {s with fnLocals:=⟨Γ,result⟩}
    pure (.normal Source.Locals.nil) : Source.EM E [] (Source.Out E.layout [] [])).run
      (.nil,{state with fnLocals:=⟨Γ,values⟩})) = _
  cases pipeline : G.pipeline <;>
    change ((do
      let result ← Source.runMods G F (fuel+4) (body (E:=E) index) [] values
      Source.EM.modSt fun s => {s with fnLocals:=⟨Γ,result⟩}
      pure (.normal Source.Locals.nil) : Source.EM E [] (Source.Out E.layout [] [])).run
        (.nil,{state with fnLocals:=⟨Γ,values⟩})) = _
  all_goals
    rw [Source.Hoare.run_bind,no_modifiers G F fuel address bytes index values {state with fnLocals:=⟨Γ,values⟩} reference found]

theorem modifier_items_revert {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel address : Nat) (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory))
    (values : Source.Locals E.layout Γ) (state : Source.St E)
    (reference : values.get index = .memRef rfl address)
    (found : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execItems G F (fuel+6) 0 (some ⟨body (E:=E) index,[],values⟩)
      (aroundBody E).items .nil).run (.nil,{state with fnLocals:=⟨Γ,values⟩}) =
      (Except.error (.revert bytes),(.nil,{state with fnLocals:=⟨Γ,values⟩})) := by
  unfold aroundBody
  rw [Source.execItems,Source.Hoare.run_bind,placeholder_revert G F fuel address bytes index values state reference found]

/-- Actual dispatch, argument evaluation, frame install, placeholder execution,
error capture, and FINALLY saved-frame restoration. No execution assumption. -/
theorem one_modifier {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel address : Nat) (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory))
    (values : Source.Locals E.layout Γ) (state : Source.St E)
    (reference : values.get index = .memRef rfl address)
    (found : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.runMods (withAround G) F (fuel+7) (body (E:=E) index) [invocation E Γ] values).run (.nil,state) =
      (Except.error (.revert bytes),(.nil,state)) := by
  rw [Source.runMods,Source.Hoare.run_bind]
  have args : (Source.EM.sub values (Source.evalConvArgs (withAround G) F (fuel+6) (invocation E Γ).args) : Source.EM E [] _).run
      (.nil,state) = (Except.ok (Source.Vals.nil,values),(.nil,state)) := rfl
  rw [args]
  dsimp only [invocation]
  rw [lookup_around]
  dsimp only [aroundBody]
  rw [dif_pos (show ([] : Source.RCtx).reverseAux [] = [] from rfl),Source.Hoare.run_bind]
  have savedRead : (Source.EM.st : Source.EM E [] _).run (.nil,state) = (Except.ok state,(.nil,state)) := rfl
  rw [savedRead]
  dsimp only
  rw [Source.Hoare.run_bind]
  dsimp only [body]
  have installRun : (Source.EM.modSt (fun s : Source.St E => {s with fnLocals:=⟨Γ,values⟩}) : Source.EM E [] Unit).run
      (.nil,state) = (Except.ok (),(.nil,{state with fnLocals:=⟨Γ,values⟩})) := rfl
  rw [installRun]
  dsimp only
  rw [Source.Hoare.run_bind,AttemptPhysical.attempt_run]
  have innerRun := modifier_items_revert (withAround G) F fuel address bytes index values state reference found
  dsimp only [body,aroundBody] at innerRun
  dsimp only [List.length_nil,Source.Vals.onto,Source.L0]
  rw [innerRun]
  rfl

abbrev Parameters := ScopeCatchPhysical.Inner

def functionDecl : Source.Decl :=
  ⟨.function,"ownedRethrow",none,false,
    .function (.ident "ownedRethrow")
      (.cons (.param (.elem .bytes) (some .memory) (some "old"))
        (.cons (.param (.elem .bytes) (some .memory) (some "data")) .nil))
      (some .internal) none .nil false none .nil (.some (.block .nil))⟩

theorem function_signature (E : Source.Env) : functionDecl.fnSig E = some (Parameters,[]) := rfl

def arguments {E : Source.Env} (old current : Nat) : Source.Vals E.layout Parameters :=
  .cons (.memRef rfl old) (.cons (.memRef rfl current) .nil)

def parameterValues {E : Source.Env} (old current : Nat) : Source.Locals E.layout Parameters :=
  .cons (.memRef rfl current) (.cons (.memRef rfl old) .nil)

def functionBase {E : Source.Env} (G : Source.Glob E) (index : Source.Idx Parameters (.bytes .memory)) : Source.Glob E :=
  {G with prog := {G.prog with body := fun d => if d.name = "ownedRethrow" then some (body (E:=E) index) else G.prog.body d}}

def program {E : Source.Env} (G : Source.Glob E) (index : Source.Idx Parameters (.bytes .memory)) := withAround (functionBase G index)

theorem lookup_function {E : Source.Env} (G : Source.Glob E) (F : Source.Fr)
    (index : Source.Idx Parameters (.bytes .memory)) :
    (program G index).prog.body ((program G index).dispatchFn F.contract functionDecl) = some (body (E:=E) index) := rfl

/-- Actual parameter order and return-frame equality, not a call agreement premise. -/
theorem parameters_onto {E : Source.Env} (old current : Nat) :
    (arguments (E:=E) old current).onto (Source.L0 E) = parameterValues old current := rfl

theorem function_frame {E : Source.Env} (index : Source.Idx Parameters (.bytes .memory)) :
    ([] : Source.RCtx).reverseAux (Parameters.reverseAux []) = (body (E:=E) index).locals := rfl

/-- Selected real internal entry; no callAddr/world implementation is copied. -/
theorem internal_revert {E : Source.Env} (G : Source.Glob E) (F : Source.Fr) (fuel old current : Nat)
    (bytes : List UInt8) (index : Source.Idx Parameters (.bytes .memory)) (address : Nat)
    (state : Source.St E) (reference : (parameterValues (E:=E) old current).get index = .memRef rfl address)
    (found : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.callInternal (program G index) F (fuel+8) functionDecl (arguments old current) []).run (.nil,state) =
      (Except.error (.revert bytes),(.nil,state)) := by
  rw [Source.callInternal,lookup_function,Source.Hoare.run_bind]
  have zero : (Source.zeroVals (E:=E) (fuel+7) [] : Source.EM E [] _).run (.nil,state) =
    (Except.ok Source.Vals.nil,(.nil,state)) := rfl
  rw [zero]
  dsimp only [Source.Vals.onto,Source.L0]
  rw [dif_pos (function_frame (E:=E) index),Source.Hoare.run_bind]
  have execution := one_modifier (functionBase G index) {F with checked:=true} fuel address bytes index (parameterValues old current) state reference found
  dsimp only [program,body,arguments,parameterValues,Source.Vals.onto,Source.L0] at execution ⊢
  rw [execution]

theorem internal_zero {E : Source.Env} (G : Source.Glob E) (F : Source.Fr) (old current : Nat)
    (index : Source.Idx Parameters (.bytes .memory)) (state : Source.St E) :
    (Source.callInternal (program G index) F 0 functionDecl (arguments old current) []).run (.nil,state) =
      (Except.error .timeout,(.nil,state)) := rfl

theorem invalid_call_frame {E : Source.Env} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (state : Source.St E) :
    (Source.callInternal (program G .here) F (fuel+8) functionDecl Source.Vals.nil []).run (.nil,state) =
      (Except.error (.stuck "call frame"),(.nil,state)) := by
  rw [Source.callInternal,lookup_function]
  rfl

/-- Direct placeholder misuse does not masquerade as a modifier invocation. -/
theorem placeholder_outside {E : Source.Env} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (state : Source.St E) :
    (Source.execS G F (fuel+1) 0 none (.placeholder rfl : Source.RStmt E [] true .body [] []) .nil).run (.nil,state) =
      (Except.error (.stuck "placeholder outside a modifier"),(.nil,state)) := rfl

theorem invalid_placeholder_frame {E : Source.Env} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (values : Source.Locals E.layout Parameters) (state : Source.St E) :
    (Source.execS G F (fuel+1) 0 (some ⟨body (E:=E) (.here : Source.Idx Parameters (.bytes .memory)),[],values⟩)
      (.placeholder rfl : Source.RStmt E [] true .body [] []) .nil).run
      (.nil,{state with fnLocals:=⟨[Source.STy.bool],Source.Locals.cons (.bool true) .nil⟩}) =
      (Except.error (.stuck "placeholder frame"),(.nil,{state with fnLocals:=⟨[Source.STy.bool],Source.Locals.cons (.bool true) .nil⟩})) := rfl

def noBodies {E : Source.Env} (G : Source.Glob E) : Source.Glob E :=
  {G with prog := {G.prog with body := fun _ => none}}

theorem missing_modifier {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (index : Source.Idx Γ (.bytes .memory)) (values : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.runMods (noBodies G) F (fuel+2) (body (E:=E) index) [invocation E Γ] values).run (.nil,state) =
      (Except.error (.stuck "modifier without a body"),(.nil,state)) := by
  rw [Source.runMods]
  rfl

theorem missing_function {E : Source.Env} (G : Source.Glob E) (F : Source.Fr) (fuel old current : Nat) (state : Source.St E) :
    (Source.callInternal (noBodies G) F (fuel+1) functionDecl (arguments old current) []).run (.nil,state) =
      (Except.error (.stuck "function without a body"),(.nil,state)) := by
  rw [Source.callInternal]
  rfl

def mismatchedBody (E : Source.Env) : Source.RBody E where
  ps := []
  rs := []
  inModifier := true
  locals := [.bool]
  out := [.bool]
  items := .stmt (.placeholder rfl) .nil

def mismatchedProgram {E : Source.Env} (G : Source.Glob E) : Source.Glob E :=
  {G with prog := {G.prog with body := fun _ => some (mismatchedBody E)}}

/-- Deliberately incoherent runtime parameter metadata is refused by the actual
frame guard; it is not claimed to be a source-derived accepted program. -/
theorem modifier_parameters {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (index : Source.Idx Γ (.bytes .memory)) (values : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.runMods (mismatchedProgram G) F (fuel+2) (body (E:=E) index) [invocation E Γ] values).run (.nil,state) =
      (Except.error (.stuck "modifier parameters"),(.nil,state)) := by
  rw [Source.runMods]
  rfl

theorem modifier_zero {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (index : Source.Idx Γ (.bytes .memory)) (values : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.runMods (withAround G) F 0 (body (E:=E) index) [invocation E Γ] values).run (.nil,state) =
      (Except.error .timeout,(.nil,state)) := rfl

theorem modifier_args_timeout {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (index : Source.Idx Γ (.bytes .memory)) (values : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.runMods (withAround G) F 1 (body (E:=E) index) [invocation E Γ] values).run (.nil,state) =
      (Except.error .timeout,(.nil,state)) := rfl

/-- Eight actual low-horizon controls include timeout AFTER temporary frame
installation; the original arbitrary saved frame is restored on that error. -/
theorem internal_low {E : Source.Env} (G : Source.Glob E) (F : Source.Fr) (old current : Nat) (state : Source.St E) :
    ([0,1,2,3,4,5,6,7].map fun fuel =>
      (Source.callInternal (program G .here) F fuel functionDecl (arguments old current) []).run (.nil,state)) =
      List.replicate 8 ((Except.error Source.Halt.timeout : Except Source.Halt (Source.RVal E.layout (Source.STy.ret []))),(.nil,state)) := by
  dsimp only [program,withAround,functionBase]
  cases pipeline : G.pipeline <;> rfl

/-- Heap/prefix come from the existing physical/raw witness. A deliberately
DIFFERENT saved boolean frame must survive the memory-parameter function call. -/
def callerState (bytes : List UInt8) : Source.St originEnv :=
  {RuntimeBlockPhysical.allocatedState AttemptPhysical.input.2 bytes with
    fnLocals:=⟨[Source.STy.bool],Source.Locals.cons (.bool true) .nil⟩}

def sample (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat)
    (index : Source.Idx Parameters (.bytes .memory) := .here) :=
  AttemptPhysical.companion
    (Source.callInternal (program G index) packedStepFrame fuel functionDecl (arguments 0 1) [])
    .nil (AttemptPhysical.input.1,callerState bytes)

theorem sample_run (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    sample G bytes (fuel+8) =
      ((.ok (.error (.revert bytes)),(Source.Locals.nil,callerState bytes)),(AttemptPhysical.input.1,callerState bytes)) := by
  unfold sample
  rw [AttemptPhysical.companion_actual]
  have found : (callerState bytes).heap.get 1 = some ⟨.bytes .memory,.bytes bytes⟩ := by
    change (AttemptPhysical.input.2.heap.alloc ⟨.bytes .memory,.bytes bytes⟩).1.get 1 = _
    simpa only [ScopeCatchPhysical.input_next] using Source.Heap.alloc_get AttemptPhysical.input.2.heap ⟨.bytes .memory,.bytes bytes⟩
  rw [internal_revert G packedStepFrame fuel 0 1 bytes .here 1 _ rfl found]

theorem saved_frame (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    (sample G bytes (fuel+8)).2.2.fnLocals = ⟨[Source.STy.bool],Source.Locals.cons (.bool true) .nil⟩ := by
  rw [sample_run]
  rfl

theorem complete_state (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    (sample G bytes (fuel+8)).2.2 = callerState bytes := by rw [sample_run]

theorem caller_raw (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    (sample G bytes (fuel+8)).2.1 = AttemptPhysical.input.1 := by rw [sample_run]

theorem nonword_alias (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    (sample G bytes (fuel+8)).2.1.get memoryRef.index = (LocalValues.ofClean locals).get memoryRef.index := by
  rw [caller_raw]
  exact CatchFunctionPhysical.nonword_retained

theorem caller_prefix (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    (sample G bytes (fuel+8)).2.2.logs = AttemptPhysical.input.2.logs := by
  rw [complete_state]
  rfl

theorem wrong_alias (G : Source.Glob originEnv) (fuel : Nat) :
    sample G [0xde,0xad] (fuel+8) (.there .here) =
      ((.ok (.error (.revert [0xaa,0xbb])),(Source.Locals.nil,callerState [0xde,0xad])),
        (AttemptPhysical.input.1,callerState [0xde,0xad])) := by
  unfold sample
  rw [AttemptPhysical.companion_actual]
  have found : (callerState [0xde,0xad]).heap.get 0 = some ⟨.bytes .memory,.bytes [0xaa,0xbb]⟩ := by
    have other : 0 ≠ AttemptPhysical.input.2.heap.next := by rw [ScopeCatchPhysical.input_next]; decide
    change (AttemptPhysical.input.2.heap.alloc ⟨.bytes .memory,.bytes [0xde,0xad]⟩).1.get 0 = _
    rw [Source.Heap.alloc_other _ _ other]
    change CatchFunctionPhysical.completed.state.2.heap.get 0 = _
    rw [CatchFunctionPhysical.caller_source_retained]
    rfl
  rw [internal_revert G packedStepFrame fuel 0 1 [0xaa,0xbb] (.there .here) 0 _ rfl found]

theorem raw_not_clean (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    LocalState.clean? (sample G bytes (fuel+8)).2 = none := by
  rw [sample_run]
  change (LocalValues.clean? ctx.tys CatchFunctionPhysical.completed.state.1).map _ = none
  cases clean : LocalValues.clean? ctx.tys CatchFunctionPhysical.completed.state.1 with
  | none => rfl
  | some values =>
      have bad := CatchFunctionPhysical.raw_not_clean
      unfold LocalState.clean? at bad
      rw [clean] at bad
      cases bad

theorem no_clean_resume (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat)
    (action : Source.EM originEnv ctx.tys Unit) :
    LocalState.runClean action (sample G bytes (fuel+8)).2 = none :=
  LocalState.runClean_refuses action _ (raw_not_clean G bytes fuel)

#print axioms no_modifiers
end Solidity.Yul.Composition.ModifierPhysical
