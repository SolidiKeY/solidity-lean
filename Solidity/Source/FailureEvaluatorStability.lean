import Solidity.Source.FailureScopeStability

/-! Closed equality-or-timeout induction for the actual enabled-plan
mutual evaluator. Full results include locals, state and cursor. No external
execution oracle, NoFail or fragment premise. This does not establish event
prefix approximation on timeout or fixed-plan session/P8 adequacy.
Proof basis: Source/Horizon.lean SHA256 43ec3e6cf3450fa117a6816cbcb1fb5ee4382adc065a0e4a2bc7c1f4ec4c60dd. -/
namespace Solidity.Source.FailureExecution.PlannedBelow
open EM
variable {E : Env} (G : Glob E) {points : Roadmap.Evm.FailurePoints}

structure BelowAt (G : Glob E) (points : Roadmap.Evm.FailurePoints) (n : Nat) : Prop where
  evalE : ∀ (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ), Below (evalE (plan := some points) G F n e) (evalE (plan := some points) G F (n + 1) e)
  evalPair : ∀ (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ),
    Below (evalPair (plan := some points) G F n a b) (evalPair (plan := some points) G F (n + 1) a b)
  evalArgs : ∀ (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs),
    Below (evalArgs (plan := some points) G F n es) (evalArgs (plan := some points) G F (n + 1) es)
  evalConvArgs : ∀ (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs),
    Below (evalConvArgs (plan := some points) G F n es) (evalConvArgs (plan := some points) G F (n + 1) es)
  evalLoc : ∀ (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ), Below (evalLoc (plan := some points) G F n l) (evalLoc (plan := some points) G F (n + 1) l)
  evalBuiltin : ∀ (F : Fr) {Γ : RCtx} {σs : List STy} (b : Builtin) (args : RArgs E Γ σs) (τ : STy),
    Below (evalBuiltin (plan := some points) G F n b args τ) (evalBuiltin (plan := some points) G F (n + 1) b args τ)
  evalArgsRev : ∀ (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs),
    Below (evalArgsRev (plan := some points) G F n es) (evalArgsRev (plan := some points) G F (n + 1) es)
  pay : ∀ (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true)) (v : RExpr E Γ (.int IntTy.u256)),
    Below (pay (plan := some points) G F n a v) (pay (plan := some points) G F (n + 1) a v)
  execS : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ),
    Below (execS (plan := some points) G F n nps ph s l) (execS (plan := some points) G F (n + 1) nps ph s l)
  forIter : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool} {Γ₁ Γ₂ : RCtx}
    (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (l : Locals E.layout Γ₁),
    Below (forIter (plan := some points) G F n nps ph c post body l) (forIter (plan := some points) G F (n + 1) nps ph c post body l)
  execItems : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ),
    Below (execItems (plan := some points) G F n nps ph b l) (execItems (plan := some points) G F (n + 1) nps ph b l)
  runMods : ∀ (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals)) (l : Locals E.layout b.locals),
    Below (runMods (plan := some points) G F n b mods l) (runMods (plan := some points) G F (n + 1) b mods l)
  callInternal : ∀ (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps) (rs : List STy),
    Below (callInternal (plan := some points) G F n d vs rs) (callInternal (plan := some points) G F (n + 1) d vs rs)
  callAddr : ∀ (F : Fr) (a : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word) (input : Solidity.Roadmap.Bytes)
    (static : Bool), Below (callAddr (plan := some points) G F n a v input static) (callAddr (plan := some points) G F (n + 1) a v input static)
  enterInstance : ∀ (a sender : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word) (input : Solidity.Roadmap.Bytes)
    (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout),
    Below (enterInstance (plan := some points) G n a sender v input static c depth m)
      (enterInstance (plan := some points) G (n + 1) a sender v input static c depth m)
  envLoop : ∀ (depth : Nat) (pstatic : Bool), Below (envLoop (plan := some points) G n depth pstatic) (envLoop (plan := some points) G (n + 1) depth pstatic)
  dispatch : ∀ (F : Fr) (input : Solidity.Roadmap.Bytes), Below (dispatch (plan := some points) G F n input) (dispatch (plan := some points) G F (n + 1) input)

theorem belowAt_zero : BelowAt G points 0 where
  evalE _ _ _ _ := by rw [evalE.eq_1]; exact Below.timeout _
  evalPair _ _ _ _ _ _ := by rw [evalPair.eq_1]; exact Below.timeout _
  evalArgs _ _ _ _ := by rw [evalArgs.eq_1]; exact Below.timeout _
  evalConvArgs _ _ _ _ := by rw [evalConvArgs.eq_1]; exact Below.timeout _
  evalLoc _ _ _ _ := by rw [evalLoc.eq_1]; exact Below.timeout _
  evalBuiltin _ _ _ _ _ _ := by rw [evalBuiltin.eq_1]; exact Below.timeout _
  evalArgsRev _ _ _ _ := by rw [evalArgsRev.eq_1]; exact Below.timeout _
  pay _ _ _ _ := by rw [pay.eq_1]; exact Below.timeout _
  execS _ _ _ _ _ _ _ _ _ _ := by rw [execS.eq_1]; exact Below.timeout _
  forIter _ _ _ _ _ _ _ _ _ _ _ _ := by rw [forIter.eq_1]; exact Below.timeout _
  execItems _ _ _ _ _ _ _ _ _ _ := by rw [execItems.eq_1]; exact Below.timeout _
  runMods _ _ _ _ := by rw [runMods.eq_1]; exact Below.timeout _
  callInternal _ _ _ _ _ := by rw [callInternal.eq_1]; exact Below.timeout _
  callAddr _ _ _ _ _ := by rw [callAddr.eq_1]; exact Below.timeout _
  enterInstance _ _ _ _ _ _ _ _ := by rw [enterInstance.eq_1]; exact Below.timeout _
  envLoop _ _ := by rw [envLoop.eq_1]; exact Below.timeout _
  dispatch _ _ := by rw [dispatch.eq_1]; exact Below.timeout _

variable {G} {n : Nat}

theorem evalE_step (ih : BelowAt G points n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) :
    Below (evalE (plan := some points) G F (n + 1) e) (evalE (plan := some points) G F (n + 1 + 1) e) := by
  cases e <;> below_unfold evalE n <;> below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem evalPair_step (ih : BelowAt G points n) (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ) :
    Below (evalPair (plan := some points) G F (n + 1) a b) (evalPair (plan := some points) G F (n + 1 + 1) a b) := by
  below_unfold evalPair n
  below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem evalArgs_step (ih : BelowAt G points n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Below (evalArgs (plan := some points) G F (n + 1) es) (evalArgs (plan := some points) G F (n + 1 + 1) es) := by
  cases es <;> below_unfold evalArgs n <;> below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem evalConvArgs_step (ih : BelowAt G points n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs) :
    Below (evalConvArgs (plan := some points) G F (n + 1) es) (evalConvArgs (plan := some points) G F (n + 1 + 1) es) := by
  cases es <;> below_unfold evalConvArgs n <;> below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem evalLoc_step (ih : BelowAt G points n) (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ) :
    Below (evalLoc (plan := some points) G F (n + 1) l) (evalLoc (plan := some points) G F (n + 1 + 1) l) := by
  cases l <;> below_unfold evalLoc n <;> below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem evalBuiltin_step (ih : BelowAt G points n) (F : Fr) {Γ : RCtx} {σs : List STy} (b : Builtin)
    (args : RArgs E Γ σs) (τ : STy) :
    Below (evalBuiltin (plan := some points) G F (n + 1) b args τ) (evalBuiltin (plan := some points) G F (n + 1 + 1) b args τ) := by
  below_unfold evalBuiltin n
  below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem evalArgsRev_step (ih : BelowAt G points n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Below (evalArgsRev (plan := some points) G F (n + 1) es) (evalArgsRev (plan := some points) G F (n + 1 + 1) es) := by
  cases es <;> below_unfold evalArgsRev n <;> below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem pay_step (ih : BelowAt G points n) (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true))
    (v : RExpr E Γ (.int IntTy.u256)) : Below (pay (plan := some points) G F (n + 1) a v) (pay (plan := some points) G F (n + 1 + 1) a v) := by
  below_unfold pay n
  below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem execS_step (ih : BelowAt G points n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) :
    Below (execS (plan := some points) G F (n + 1) nps ph s l) (execS (plan := some points) G F (n + 1 + 1) nps ph s l) := by
  cases s <;> below_unfold execS n <;> below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem forIter_step (ih : BelowAt G points n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool}
    {Γ₁ Γ₂ : RCtx} (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂)
    (l : Locals E.layout Γ₁) :
    Below (forIter (plan := some points) G F (n + 1) nps ph c post body l) (forIter (plan := some points) G F (n + 1 + 1) nps ph c post body l) := by
  cases c <;> below_unfold forIter n <;> below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem execItems_step (ih : BelowAt G points n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) :
    Below (execItems (plan := some points) G F (n + 1) nps ph b l) (execItems (plan := some points) G F (n + 1 + 1) nps ph b l) := by
  cases b <;> below_unfold execItems n <;> below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem runMods_step (ih : BelowAt G points n) (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals))
    (l : Locals E.layout b.locals) : Below (runMods (plan := some points) G F (n + 1) b mods l) (runMods (plan := some points) G F (n + 1 + 1) b mods l) := by
  cases mods with
  | nil => below_unfold runMods n; below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
  | cons md rest =>
    below_unfold runMods n
    refine Below.bind (Below.sub _ (ih.evalConvArgs _ _)) fun p => ?_
    split
    · exact Below.refl _
    · split
      · refine Below.bind (Below.refl _) fun s => ?_
        refine Below.bind (Below.refl _) fun _ => ?_
        refine Below.attempt_bind (ih.execItems _ _ _ _ _) (fun r => ?_) (fun x => ?_)
        · below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
        · rfl
      · exact Below.refl _
theorem callInternal_step (ih : BelowAt G points n) (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps)
    (rs : List STy) : Below (callInternal (plan := some points) G F (n + 1) d vs rs) (callInternal (plan := some points) G F (n + 1 + 1) d vs rs) := by
  below_unfold callInternal n
  below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem callAddr_step (ih : BelowAt G points n) (F : Fr) (a : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) :
    Below (callAddr (plan := some points) G F (n + 1) a v input static) (callAddr (plan := some points) G F (n + 1 + 1) a v input static) := by
  below_unfold callAddr n
  below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem enterInstance_step (ih : BelowAt G points n) (a sender : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout) :
    Below (enterInstance (plan := some points) G (n + 1) a sender v input static c depth m)
      (enterInstance (plan := some points) G (n + 1 + 1) a sender v input static c depth m) := by
  below_unfold enterInstance n
  refine Below.bind (Below.refl _) fun _ => ?_
  refine Below.attempt_bind (frame_below _ (ih.dispatch _ _)) (fun r => ?_) (fun x => ?_)
  · exact Below.refl _
  · rfl
theorem envLoop_step (ih : BelowAt G points n) (depth : Nat) (pstatic : Bool) :
    Below (envLoop (plan := some points) G (n + 1) depth pstatic) (envLoop (plan := some points) G (n + 1 + 1) depth pstatic) := by
  below_unfold envLoop n
  below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem dispatch_step (ih : BelowAt G points n) (F : Fr) (input : Solidity.Roadmap.Bytes) :
    Below (dispatch (plan := some points) G F (n + 1) input) (dispatch (plan := some points) G F (n + 1 + 1) input) := by
  below_unfold dispatch n
  below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

/-- **Every interpreter function is monotone in its horizon.** -/
theorem belowAt (G : Glob E) : ∀ n, BelowAt G points n
  | 0 => belowAt_zero G
  | n + 1 =>
    have ih := belowAt G n
    ⟨evalE_step ih, evalPair_step ih, evalArgs_step ih, evalConvArgs_step ih, evalLoc_step ih,
      evalBuiltin_step ih, evalArgsRev_step ih, pay_step ih, execS_step ih, forIter_step ih,
      execItems_step ih, runMods_step ih, callInternal_step ih, callAddr_step ih, enterInstance_step ih,
      envLoop_step ih, dispatch_step ih⟩

end Solidity.Source.FailureExecution.PlannedBelow
