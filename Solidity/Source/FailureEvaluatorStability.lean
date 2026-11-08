import Solidity.Source.FailureScopeStability

/-! Closed equality-or-timeout induction for the actual enabled-plan
mutual evaluator. Full results include locals, state and cursor. No external
execution oracle, NoFail or fragment premise. This does not establish event
prefix approximation on timeout or fixed-plan session/P8 adequacy.
Both calldata modes instantiate the shared HorizonAt schema at the same fixed plan. -/
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

section
variable {G}

abbrev BelowAtKnown (G : Glob E) (points : Roadmap.Evm.FailurePoints) (n : Nat) : Prop :=
  HorizonAt (@Below E) G n (some points)

theorem callLibrary_step_known (ih : Solidity.Source.FailureExecution.PlannedBelow.BelowAtKnown G points n) (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps) (rs : List STy) :
    Below (callLibrary (plan := some points) G F (n + 1) d vs rs) (callLibrary (plan := some points) G F (n + 1 + 1) d vs rs) := by
  let capture (fuel : Nat) (input : Roadmap.Bytes) : EM E [] (Except Roadmap.Bytes (Vals E.layout rs)) := do
    let saved ← mark
    modSt fun state => { state with heap := Heap.empty }
    let result ← attempt (FailureExecution.frame (some points)
      (callInternal (plan := some points) (calldataKnown := ps.all STy.isValue) G
        { F with cd := input, depth := F.depth + 1 } fuel d vs rs))
    modSt fun state => { state with heap := saved.2.2 }
    match result with
    | .ok value => do
      let raw ← lift (unRet rs value)
      let values ← lift raw.toVals
      FailureExecution.preflight (some points) (pure (.ok values))
    | .error (.revert data) => do
      rollbackTo saved
      FailureExecution.preflight (some points) (pure (.error data))
    | .error other => halt other
  have captured (input : Roadmap.Bytes) : Below (capture n input) (capture (n + 1) input) := by
    dsimp only [capture]
    refine Below.bind (Below.refl _) (fun saved => ?_)
    refine Below.bind (Below.refl _) (fun _ => ?_)
    refine Below.attempt_bind (frame_below (some points) (ih.callInternal (ps.all STy.isValue) _ d vs rs)) (fun _ => Below.refl _) (fun _ => rfl)
  below_unfold callLibrary n
  simp only [FailureExecution.preflight]
  refine Below.bind (Below.refl (FailureExecution.check (some points) : EM E [] Unit)) (fun _ => ?_)
  split
  · exact Below.refl _
  · simp only [pure_bind]
    split
    · simp only [halt_bind]
      exact Below.refl _
    · split
      · change Below
          (encodeVals F n false vs.toR >>= fun encoded => capture n (G.selector (sigOf E.layout d.name ps) ++ encoded))
          (encodeVals F (n + 1) false vs.toR >>= fun encoded => capture (n + 1) (G.selector (sigOf E.layout d.name ps) ++ encoded))
        exact Below.bind (encodeVals_below F n false vs.toR)
          (fun encoded => captured (G.selector (sigOf E.layout d.name ps) ++ encoded))
      · exact captured []



theorem evalE_step_known (ih : BelowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) :
    Below (evalE (plan := some points) G F (n + 1) e (calldataKnown := known)) (evalE (plan := some points) G F (n + 1 + 1) e (calldataKnown := known)) := by
  cases e <;> below_unfold evalE n <;> apply Below.withLibraryCalldata <;> below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem evalPair_step_known (ih : BelowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ) :
    Below (evalPair (plan := some points) G F (n + 1) a b (calldataKnown := known)) (evalPair (plan := some points) G F (n + 1 + 1) a b (calldataKnown := known)) := by
  below_unfold evalPair n
  below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem evalArgs_step_known (ih : BelowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Below (evalArgs (plan := some points) G F (n + 1) es (calldataKnown := known)) (evalArgs (plan := some points) G F (n + 1 + 1) es (calldataKnown := known)) := by
  cases es <;> below_unfold evalArgs n <;> below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem evalConvArgs_step_known (ih : BelowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs) :
    Below (evalConvArgs (plan := some points) G F (n + 1) es (calldataKnown := known)) (evalConvArgs (plan := some points) G F (n + 1 + 1) es (calldataKnown := known)) := by
  cases es <;> below_unfold evalConvArgs n <;> below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem evalLoc_step_known (ih : BelowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ) :
    Below (evalLoc (plan := some points) G F (n + 1) l (calldataKnown := known)) (evalLoc (plan := some points) G F (n + 1 + 1) l (calldataKnown := known)) := by
  cases l <;> below_unfold evalLoc n <;> below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem evalBuiltin_step_known (ih : BelowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {σs : List STy} (b : Builtin)
    (args : RArgs E Γ σs) (τ : STy) :
    Below (evalBuiltin (plan := some points) G F (n + 1) b args τ (calldataKnown := known)) (evalBuiltin (plan := some points) G F (n + 1 + 1) b args τ (calldataKnown := known)) := by
  below_unfold evalBuiltin n
  below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem evalArgsRev_step_known (ih : BelowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Below (evalArgsRev (plan := some points) G F (n + 1) es (calldataKnown := known)) (evalArgsRev (plan := some points) G F (n + 1 + 1) es (calldataKnown := known)) := by
  cases es <;> below_unfold evalArgsRev n <;> below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem pay_step_known (ih : BelowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true))
    (v : RExpr E Γ (.int IntTy.u256)) : Below (pay (plan := some points) G F (n + 1) a v (calldataKnown := known)) (pay (plan := some points) G F (n + 1 + 1) a v (calldataKnown := known)) := by
  below_unfold pay n
  below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem execS_step_known (ih : BelowAtKnown G points n) (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) :
    Below (execS (plan := some points) G F (n + 1) nps ph s l (calldataKnown := known)) (execS (plan := some points) G F (n + 1 + 1) nps ph s l (calldataKnown := known)) := by
  cases s <;> below_unfold execS n <;> below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem forIter_step_known (ih : BelowAtKnown G points n) (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool}
    {Γ₁ Γ₂ : RCtx} (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂)
    (l : Locals E.layout Γ₁) :
    Below (forIter (plan := some points) G F (n + 1) nps ph c post body l (calldataKnown := known)) (forIter (plan := some points) G F (n + 1 + 1) nps ph c post body l (calldataKnown := known)) := by
  cases c <;> below_unfold forIter n <;> below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem execItems_step_known (ih : BelowAtKnown G points n) (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) :
    Below (execItems (plan := some points) G F (n + 1) nps ph b l (calldataKnown := known)) (execItems (plan := some points) G F (n + 1 + 1) nps ph b l (calldataKnown := known)) := by
  cases b <;> below_unfold execItems n <;> below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem runMods_step_known (ih : BelowAtKnown G points n) (known : Bool) (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals))
    (l : Locals E.layout b.locals) : Below (runMods (plan := some points) G F (n + 1) b mods l (calldataKnown := known)) (runMods (plan := some points) G F (n + 1 + 1) b mods l (calldataKnown := known)) := by
  cases mods with
  | nil => below_unfold runMods n; below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
  | cons md rest =>
    below_unfold runMods n
    refine Below.bind (Below.sub _ (ih.evalConvArgs known _ _)) fun p => ?_
    split
    · exact Below.refl _
    · split
      · refine Below.bind (Below.refl _) fun s => ?_
        refine Below.bind (Below.refl _) fun _ => ?_
        refine Below.attempt_bind (ih.execItems known _ _ _ _ _) (fun r => ?_) (fun x => ?_)
        · below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
        · rfl
      · exact Below.refl _

theorem callInternal_step_known (ih : BelowAtKnown G points n) (known : Bool) (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps)
    (rs : List STy) : Below (callInternal (plan := some points) G F (n + 1) d vs rs (calldataKnown := known)) (callInternal (plan := some points) G F (n + 1 + 1) d vs rs (calldataKnown := known)) := by
  below_unfold callInternal n
  below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem callAddr_step_known (ih : BelowAtKnown G points n) (F : Fr) (a : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) :
    Below (callAddr (plan := some points) G F (n + 1) a v input static) (callAddr (plan := some points) G F (n + 1 + 1) a v input static) := by
  below_unfold callAddr n
  below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem enterInstance_step_known (ih : BelowAtKnown G points n) (a sender : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout) :
    Below (enterInstance (plan := some points) G (n + 1) a sender v input static c depth m)
      (enterInstance (plan := some points) G (n + 1 + 1) a sender v input static c depth m) := by
  below_unfold enterInstance n
  refine Below.bind (Below.refl _) fun _ => ?_
  refine Below.attempt_bind (frame_below _ (ih.dispatch _ _)) (fun r => ?_) (fun x => ?_)
  · exact Below.refl _
  · rfl

theorem envLoop_step_known (ih : BelowAtKnown G points n) (depth : Nat) (pstatic : Bool) :
    Below (envLoop (plan := some points) G (n + 1) depth pstatic) (envLoop (plan := some points) G (n + 1 + 1) depth pstatic) := by
  below_unfold envLoop n
  below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem dispatch_step_known (ih : BelowAtKnown G points n) (F : Fr) (input : Solidity.Roadmap.Bytes) :
    Below (dispatch (plan := some points) G F (n + 1) input) (dispatch (plan := some points) G F (n + 1 + 1) input) := by
  below_unfold dispatch n
  below_go [frame_below, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

  /-- **Every interpreter function is monotone in its horizon.** -/

theorem belowAtKnown_zero (G : Glob E) (points : Roadmap.Evm.FailurePoints) : BelowAtKnown G points 0 := by
  exact {
    evalE := by intros; exact Below.timeout _,
    evalPair := by intros; exact Below.timeout _,
    evalArgs := by intros; exact Below.timeout _,
    evalConvArgs := by intros; exact Below.timeout _,
    evalLoc := by intros; exact Below.timeout _,
    evalBuiltin := by intros; exact Below.timeout _,
    evalArgsRev := by intros; exact Below.timeout _,
    pay := by intros; exact Below.timeout _,
    execS := by intros; exact Below.timeout _,
    forIter := by intros; exact Below.timeout _,
    execItems := by intros; exact Below.timeout _,
    runMods := by intros; exact Below.timeout _,
    callInternal := by intros; exact Below.timeout _,
    callLibrary := by intros; exact Below.timeout _,
    callAddr := by intros; exact Below.timeout _,
    enterInstance := by intros; exact Below.timeout _,
    envLoop := by intros; exact Below.timeout _,
    dispatch := by intros; exact Below.timeout _
  }

theorem belowAtKnown (G : Glob E) (points : Roadmap.Evm.FailurePoints) : ∀ n, BelowAtKnown G points n := by
  intro n
  induction n with
  | zero => exact belowAtKnown_zero G points
  | succ n ih => exact ⟨evalE_step_known ih, evalPair_step_known ih, evalArgs_step_known ih, evalConvArgs_step_known ih, evalLoc_step_known ih, evalBuiltin_step_known ih, evalArgsRev_step_known ih, pay_step_known ih, execS_step_known ih, forIter_step_known ih, execItems_step_known ih, runMods_step_known ih, callInternal_step_known ih, callLibrary_step_known ih, callAddr_step_known ih, enterInstance_step_known ih, envLoop_step_known ih, dispatch_step_known ih⟩

end

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
  exact (belowAtKnown G points (n + 1)).evalE true F e

theorem evalPair_step (ih : BelowAt G points n) (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ) :
    Below (evalPair (plan := some points) G F (n + 1) a b) (evalPair (plan := some points) G F (n + 1 + 1) a b) := by
  exact (belowAtKnown G points (n + 1)).evalPair true F a b

theorem evalArgs_step (ih : BelowAt G points n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Below (evalArgs (plan := some points) G F (n + 1) es) (evalArgs (plan := some points) G F (n + 1 + 1) es) := by
  exact (belowAtKnown G points (n + 1)).evalArgs true F es

theorem evalConvArgs_step (ih : BelowAt G points n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs) :
    Below (evalConvArgs (plan := some points) G F (n + 1) es) (evalConvArgs (plan := some points) G F (n + 1 + 1) es) := by
  exact (belowAtKnown G points (n + 1)).evalConvArgs true F es

theorem evalLoc_step (ih : BelowAt G points n) (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ) :
    Below (evalLoc (plan := some points) G F (n + 1) l) (evalLoc (plan := some points) G F (n + 1 + 1) l) := by
  exact (belowAtKnown G points (n + 1)).evalLoc true F l

theorem evalBuiltin_step (ih : BelowAt G points n) (F : Fr) {Γ : RCtx} {σs : List STy} (b : Builtin)
    (args : RArgs E Γ σs) (τ : STy) :
    Below (evalBuiltin (plan := some points) G F (n + 1) b args τ) (evalBuiltin (plan := some points) G F (n + 1 + 1) b args τ) := by
  exact (belowAtKnown G points (n + 1)).evalBuiltin true F b args τ

theorem evalArgsRev_step (ih : BelowAt G points n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Below (evalArgsRev (plan := some points) G F (n + 1) es) (evalArgsRev (plan := some points) G F (n + 1 + 1) es) := by
  exact (belowAtKnown G points (n + 1)).evalArgsRev true F es

theorem pay_step (ih : BelowAt G points n) (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true))
    (v : RExpr E Γ (.int IntTy.u256)) : Below (pay (plan := some points) G F (n + 1) a v) (pay (plan := some points) G F (n + 1 + 1) a v) := by
  exact (belowAtKnown G points (n + 1)).pay true F a v

theorem execS_step (ih : BelowAt G points n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) :
    Below (execS (plan := some points) G F (n + 1) nps ph s l) (execS (plan := some points) G F (n + 1 + 1) nps ph s l) := by
  exact (belowAtKnown G points (n + 1)).execS true F nps ph s l

theorem forIter_step (ih : BelowAt G points n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool}
    {Γ₁ Γ₂ : RCtx} (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂)
    (l : Locals E.layout Γ₁) :
    Below (forIter (plan := some points) G F (n + 1) nps ph c post body l) (forIter (plan := some points) G F (n + 1 + 1) nps ph c post body l) := by
  exact (belowAtKnown G points (n + 1)).forIter true F nps ph c post body l

theorem execItems_step (ih : BelowAt G points n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) :
    Below (execItems (plan := some points) G F (n + 1) nps ph b l) (execItems (plan := some points) G F (n + 1 + 1) nps ph b l) := by
  exact (belowAtKnown G points (n + 1)).execItems true F nps ph b l

theorem runMods_step (ih : BelowAt G points n) (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals))
    (l : Locals E.layout b.locals) : Below (runMods (plan := some points) G F (n + 1) b mods l) (runMods (plan := some points) G F (n + 1 + 1) b mods l) := by
  exact (belowAtKnown G points (n + 1)).runMods true F b mods l

theorem callInternal_step (ih : BelowAt G points n) (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps)
    (rs : List STy) : Below (callInternal (plan := some points) G F (n + 1) d vs rs) (callInternal (plan := some points) G F (n + 1 + 1) d vs rs) := by
  exact (belowAtKnown G points (n + 1)).callInternal true F d vs rs

theorem callAddr_step (ih : BelowAt G points n) (F : Fr) (a : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) :
    Below (callAddr (plan := some points) G F (n + 1) a v input static) (callAddr (plan := some points) G F (n + 1 + 1) a v input static) := by
  exact (belowAtKnown G points (n + 1)).callAddr F a v input static

theorem enterInstance_step (ih : BelowAt G points n) (a sender : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout) :
    Below (enterInstance (plan := some points) G (n + 1) a sender v input static c depth m)
      (enterInstance (plan := some points) G (n + 1 + 1) a sender v input static c depth m) := by
  exact (belowAtKnown G points (n + 1)).enterInstance a sender v input static c depth m

theorem envLoop_step (ih : BelowAt G points n) (depth : Nat) (pstatic : Bool) :
    Below (envLoop (plan := some points) G (n + 1) depth pstatic) (envLoop (plan := some points) G (n + 1 + 1) depth pstatic) := by
  exact (belowAtKnown G points (n + 1)).envLoop depth pstatic

theorem dispatch_step (ih : BelowAt G points n) (F : Fr) (input : Solidity.Roadmap.Bytes) :
    Below (dispatch (plan := some points) G F (n + 1) input) (dispatch (plan := some points) G F (n + 1 + 1) input) := by
  exact (belowAtKnown G points (n + 1)).dispatch F input

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
