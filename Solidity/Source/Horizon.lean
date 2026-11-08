import Solidity.Source.HorizonConst

/-!
# Horizons: timed-out runs show a prefix of the events

The last part of the horizon results (S05 item 2), whose overview is in
`Solidity/Source/HorizonFuel.lean`: fuel monotonicity and horizon
independence there, events only grow in `HorizonGrow`, helpers keep the
events in `HorizonConst`, and here `approxAt` and `runTx_events_mono`. The
module was split for checking cost; importers of `Solidity.Source.Horizon`
see every part.
-/

namespace Solidity.Source

open EM
open Solidity.Roadmap (Address Word Bytes Request Outcome Event)

variable {E : Env}

/-! ## Timed-out runs show a prefix of the events -/

theorem Approx.trans {Γ : RCtx} {α : Type} {a b c : EM E Γ α} (h₁ : Approx a b) (h₂ : Approx b c) :
    Approx a c := by
  refine ⟨h₁.1, h₂.2.1, fun x => ?_⟩
  rcases h₁.2.2 x with ⟨ht, he⟩ | he
  · rcases h₂.2.2 x with ⟨_, he'⟩ | he'
    · exact .inl ⟨ht, he.trans he'⟩
    · exact .inl ⟨ht, he'.symm ▸ he⟩
  · rw [he]; exact h₂.2.2 x

theorem Approx.sub {Γ Γ' : RCtx} {α : Type} (l' : Locals E.layout Γ') {m m' : EM E Γ' α}
    (h : Approx m m') : Approx (EM.sub (Γ := Γ) l' m) (EM.sub l' m') := by
  refine ⟨Grow.sub l' h.1, Grow.sub l' h.2.1, fun x => ?_⟩
  rcases x with ⟨l, s⟩
  rw [run_sub, run_sub]
  rcases h.2.2 (l', s) with ⟨ht, he⟩ | he
  · left
    rcases hr : m.run (l', s) with ⟨r, l₁, s₁⟩
    rw [hr] at ht he
    cases ht
    refine ⟨rfl, ?_⟩
    rcases hr' : m'.run (l', s) with ⟨r', l₂, s₂⟩
    rw [hr'] at he
    cases r' <;> exact he
  · right
    rw [he]

/-- A halt caught by `attempt`: the continuation re-raises a timeout
without adding events. -/
theorem Approx.attempt_bind {Γ : RCtx} {α β : Type} {m m' : EM E Γ α} {k k' : Except Halt α → EM E Γ β}
    (hm : Approx m m') (hk : ∀ r, Approx (k r) (k' r))
    (h0 : ∀ x, ((k (.error .timeout)).run x).1 = .error .timeout ∧
      ((k (.error .timeout)).run x).2.2.events = x.2.events) :
    Approx (EM.attempt m >>= k) (EM.attempt m' >>= k') := by
  refine ⟨Grow.bind (Grow.attempt hm.1) fun r => (hk r).1, Grow.bind (Grow.attempt hm.2.1) fun r => (hk r).2.1,
    fun x => ?_⟩
  rw [run_bind, run_bind, run_attempt, run_attempt]
  rcases hm.2.2 x with ⟨ht, he⟩ | he
  · left
    rw [ht]
    refine ⟨(h0 _).1, ?_⟩
    rw [(h0 _).2]
    exact he.trans ((hk _).2.1 _)
  · rw [he]
    exact (hk _).2.2 _

theorem Approx.forIn {Γ : RCtx} {α β : Type} (l : List α) (b : β) {f f' : α → β → EM E Γ (ForInStep β)}
    (h : ∀ a b, Approx (f a b) (f' a b)) : Approx (forIn l b f) (forIn l b f') := by
  induction l generalizing b with
  | nil => exact Approx.refl (Grow.pure _)
  | cons a as ih =>
    simp only [List.forIn_cons]
    refine Approx.bind (h a b) fun r => ?_
    cases r with
    | done _ => exact Approx.refl (Grow.pure _)
    | yield b' => exact ih b'

/-- Close `Approx (body at n) (body at n + 1)` as `below_go` does; where the
two sides agree, by `Grow` (`grow_go` with the second list). -/
syntax "approx_go" "[" ident,* "]" "[" ident,* "]" "[" ident,* "]" "[" ident,* "]" : tactic
macro_rules
  | `(tactic| approx_go [$ls,*] [$gs,*] [$bs,*] [$cs,*]) => `(tactic| repeat' (first
      | (with_reducible refine Approx.bind ?_ ?_)
      | (with_reducible exact Approx.refl (by grow_go [$gs,*]))
      | (first $[| with_reducible apply $ls:ident]*)
      | (with_reducible apply Approx.sub)
      | (refine Approx.attempt_bind ?_ ?_ ?_)
      | (with_reducible intro _)
      | (exact ⟨rfl, rfl⟩)
      | split
      | ((refine Approx.of_below ?_ ?_ ?_) <;> (first | (first $[| with_reducible apply $bs:ident]*) | (const_go [$cs,*])) <;> done)
      | (dsimp only)))

/-! Both calldata modes share the ordinary-plan event-prefix induction. -/
section
variable {G : Glob E} {n : Nat}

abbrev ApproxAtKnown (G : Glob E) (n : Nat) : Prop := HorizonAt (@Approx E) G n

theorem Approx.withLibraryCalldata {Γ : RCtx} {α : Type}
    (known : Bool) (ty : STy) {a b : EM E Γ α} (h : Approx a b) :
    Approx (Solidity.Source.withLibraryCalldata known ty a)
      (Solidity.Source.withLibraryCalldata known ty b) := by
  cases known <;> cases ht : ty.containsCalldata <;> simp only [Solidity.Source.withLibraryCalldata, ht, Bool.false_eq_true, if_false, if_true] <;> first | exact h | exact Approx.refl (Grow.halt _)


theorem approxAtKnown_zero (G : Glob E) : ApproxAtKnown G 0 := by
  exact { evalE := by intros; rw [evalE.eq_1]; apply Approx.timeout; apply (growAtKnown G 1).evalE, evalPair := by intros; rw [evalPair.eq_1]; apply Approx.timeout; apply (growAtKnown G 1).evalPair, evalArgs := by intros; rw [evalArgs.eq_1]; apply Approx.timeout; apply (growAtKnown G 1).evalArgs, evalConvArgs := by intros; rw [evalConvArgs.eq_1]; apply Approx.timeout; apply (growAtKnown G 1).evalConvArgs, evalLoc := by intros; rw [evalLoc.eq_1]; apply Approx.timeout; apply (growAtKnown G 1).evalLoc, evalBuiltin := by intros; rw [evalBuiltin.eq_1]; apply Approx.timeout; apply (growAtKnown G 1).evalBuiltin, evalArgsRev := by intros; rw [evalArgsRev.eq_1]; apply Approx.timeout; apply (growAtKnown G 1).evalArgsRev, pay := by intros; rw [pay.eq_1]; apply Approx.timeout; apply (growAtKnown G 1).pay, execS := by intros; rw [execS.eq_1]; apply Approx.timeout; apply (growAtKnown G 1).execS, forIter := by intros; rw [forIter.eq_1]; apply Approx.timeout; apply (growAtKnown G 1).forIter, execItems := by intros; rw [execItems.eq_1]; apply Approx.timeout; apply (growAtKnown G 1).execItems, runMods := by intros; rw [runMods.eq_1]; apply Approx.timeout; apply (growAtKnown G 1).runMods, callInternal := by intros; rw [callInternal.eq_1]; apply Approx.timeout; apply (growAtKnown G 1).callInternal, callLibrary := by intros; rw [callLibrary.eq_1]; apply Approx.timeout; apply (growAtKnown G 1).callLibrary, callAddr := by intros; rw [callAddr.eq_1]; apply Approx.timeout; apply (growAtKnown G 1).callAddr, enterInstance := by intros; rw [enterInstance.eq_1]; apply Approx.timeout; apply (growAtKnown G 1).enterInstance, envLoop := by intros; rw [envLoop.eq_1]; apply Approx.timeout; apply (growAtKnown G 1).envLoop, dispatch := by intros; rw [dispatch.eq_1]; apply Approx.timeout; apply (growAtKnown G 1).dispatch }


theorem callLibrary_astep_known (ih : ApproxAtKnown G n) (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps)
    (rs : List STy) : Approx (callLibrary G F (n + 1) d vs rs) (callLibrary G F (n + 1 + 1) d vs rs) := by
  let capture (fuel : Nat) (input : Bytes) : EM E [] (Except Bytes (Vals E.layout rs)) := do
    let saved ← mark
    modSt fun state => { state with heap := Heap.empty }
    let result ← attempt (callInternal (calldataKnown := ps.all STy.isValue) G
      { F with cd := input, depth := F.depth + 1 } fuel d vs rs)
    modSt fun state => { state with heap := saved.2.2 }
    match result with
    | .ok value => do
      let raw ← lift (unRet rs value)
      let values ← lift raw.toVals
      pure (.ok values)
    | .error (.revert data) => do
      rollbackTo saved
      pure (.error data)
    | .error other => halt other
  have captured (input : Bytes) : Approx (capture n input) (capture (n + 1) input) := by
    dsimp only [capture]
    refine Approx.bind (Approx.refl mark_grow) (fun saved => ?_)
    refine Approx.bind (Approx.refl (Grow.modSt _ (fun _ => List.prefix_refl _))) (fun _ => ?_)
    refine Approx.attempt_bind (ih.callInternal (ps.all STy.isValue) _ d vs rs) ?_ ?_
    · intro result
      apply Approx.refl
      grow_go [rollbackTo_grow]
    · intro x
      exact ⟨rfl, rfl⟩
  below_unfold callLibrary n
  simp only [FailureExecution.preflight]
  split
  · exact Approx.refl (Grow.pure _)
  · split
    · exact Approx.refl (Grow.halt _)
    · simp only [pure_bind]
      split
      · change Approx
          (encodeVals F n false vs.toR >>= fun encoded => capture n (G.selector (sigOf E.layout d.name ps) ++ encoded))
          (encodeVals F (n + 1) false vs.toR >>= fun encoded => capture (n + 1) (G.selector (sigOf E.layout d.name ps) ++ encoded))
        exact Approx.bind (Approx.of_below (encodeVals_below F n false vs.toR)
          (encodeVals_const F n false vs.toR) (encodeVals_const F (n + 1) false vs.toR))
          (fun encoded => captured (G.selector (sigOf E.layout d.name ps) ++ encoded))
      · exact captured []


theorem evalE_apart_0_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 0 ≤ e.ctorIdx ∧ e.ctorIdx < 12) : Approx (evalE G F (n + 1) e (calldataKnown := known)) (evalE G F (n + 1 + 1) e (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (below_unfold evalE n; apply Approx.withLibraryCalldata; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.pay, ih.callInternal, ih.callAddr, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.pay, gn.callInternal, gn.callAddr, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.pay, gs.callInternal, gs.callAddr] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])


theorem evalE_apart_1_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 12 ≤ e.ctorIdx ∧ e.ctorIdx < 24) : Approx (evalE G F (n + 1) e (calldataKnown := known)) (evalE G F (n + 1 + 1) e (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (below_unfold evalE n; apply Approx.withLibraryCalldata; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.pay, ih.callInternal, ih.callAddr, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.pay, gn.callInternal, gn.callAddr, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.pay, gs.callInternal, gs.callAddr] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])


theorem evalE_apart_2_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 24 ≤ e.ctorIdx ∧ e.ctorIdx < 28) : Approx (evalE G F (n + 1) e (calldataKnown := known)) (evalE G F (n + 1 + 1) e (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (below_unfold evalE n; apply Approx.withLibraryCalldata; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.pay, ih.callInternal, ih.callAddr, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.pay, gn.callInternal, gn.callAddr, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.pay, gs.callInternal, gs.callAddr] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])


theorem evalE_apart_3_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 28 ≤ e.ctorIdx ∧ e.ctorIdx < 32) : Approx (evalE G F (n + 1) e (calldataKnown := known)) (evalE G F (n + 1 + 1) e (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (below_unfold evalE n; apply Approx.withLibraryCalldata; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.pay, ih.callInternal, ih.callAddr, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.pay, gn.callInternal, gn.callAddr, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.pay, gs.callInternal, gs.callAddr] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])


theorem evalE_apart_4_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 32 ≤ e.ctorIdx ∧ e.ctorIdx < 33) : Approx (evalE G F (n + 1) e (calldataKnown := known)) (evalE G F (n + 1 + 1) e (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (below_unfold evalE n; apply Approx.withLibraryCalldata; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.pay, ih.callInternal, ih.callAddr, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.pay, gn.callInternal, gn.callAddr, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.pay, gs.callInternal, gs.callAddr] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])


theorem evalE_apart_5_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 33 ≤ e.ctorIdx ∧ e.ctorIdx < 34) : Approx (evalE G F (n + 1) e (calldataKnown := known)) (evalE G F (n + 1 + 1) e (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (below_unfold evalE n; apply Approx.withLibraryCalldata; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.pay, ih.callInternal, ih.callAddr, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.pay, gn.callInternal, gn.callAddr, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.pay, gs.callInternal, gs.callAddr] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])


theorem evalE_apart_6_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 34 ≤ e.ctorIdx ∧ e.ctorIdx < 35) : Approx (evalE G F (n + 1) e (calldataKnown := known)) (evalE G F (n + 1 + 1) e (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (below_unfold evalE n; apply Approx.withLibraryCalldata; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.pay, ih.callInternal, ih.callAddr, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.pay, gn.callInternal, gn.callAddr, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.pay, gs.callInternal, gs.callAddr] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])


theorem evalE_apart_7_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 35 ≤ e.ctorIdx ∧ e.ctorIdx < 36) : Approx (evalE G F (n + 1) e (calldataKnown := known)) (evalE G F (n + 1 + 1) e (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (below_unfold evalE n; apply Approx.withLibraryCalldata; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.pay, ih.callInternal, ih.callAddr, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.pay, gn.callInternal, gn.callAddr, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.pay, gs.callInternal, gs.callAddr] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])


theorem evalE_apart_8_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 36 ≤ e.ctorIdx ∧ e.ctorIdx < 60) : Approx (evalE G F (n + 1) e (calldataKnown := known)) (evalE G F (n + 1 + 1) e (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (below_unfold evalE n; apply Approx.withLibraryCalldata; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.pay, ih.callInternal, ih.callAddr, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.pay, gn.callInternal, gn.callAddr, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.pay, gs.callInternal, gs.callAddr] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])


theorem evalE_astep_known (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) :
    Approx (evalE G F (n + 1) e (calldataKnown := known)) (evalE G F (n + 1 + 1) e (calldataKnown := known)) := by
  by_cases h0 : e.ctorIdx < 12
  · exact evalE_apart_0_known ih known F e ⟨by omega, h0⟩
  by_cases h1 : e.ctorIdx < 24
  · exact evalE_apart_1_known ih known F e ⟨by omega, h1⟩
  by_cases h2 : e.ctorIdx < 28
  · exact evalE_apart_2_known ih known F e ⟨by omega, h2⟩
  by_cases h3 : e.ctorIdx < 32
  · exact evalE_apart_3_known ih known F e ⟨by omega, h3⟩
  by_cases h4 : e.ctorIdx < 33
  · exact evalE_apart_4_known ih known F e ⟨by omega, h4⟩
  by_cases h5 : e.ctorIdx < 34
  · exact evalE_apart_5_known ih known F e ⟨by omega, h5⟩
  by_cases h6 : e.ctorIdx < 35
  · exact evalE_apart_6_known ih known F e ⟨by omega, h6⟩
  by_cases h7 : e.ctorIdx < 36
  · exact evalE_apart_7_known ih known F e ⟨by omega, h7⟩
  have hl : e.ctorIdx < 60 := by cases e <;> simp only [RExpr.ctorIdx] <;> omega
  exact evalE_apart_8_known ih known F e ⟨by omega, hl⟩


theorem evalPair_astep_known (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ) :
    Approx (evalPair G F (n + 1) a b (calldataKnown := known)) (evalPair G F (n + 1 + 1) a b (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  below_unfold evalPair n
  approx_go [ih.evalE, ih.evalPair, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gs.evalE, gs.evalPair] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem evalArgs_astep_known (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Approx (evalArgs G F (n + 1) es (calldataKnown := known)) (evalArgs G F (n + 1 + 1) es (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases es <;> below_unfold evalArgs n <;> approx_go [ih.evalE, ih.evalArgs, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalArgs, gs.evalE, gs.evalArgs] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem evalConvArgs_astep_known (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs) :
    Approx (evalConvArgs G F (n + 1) es (calldataKnown := known)) (evalConvArgs G F (n + 1 + 1) es (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases es <;> below_unfold evalConvArgs n <;> approx_go [ih.evalE, ih.evalConvArgs, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalConvArgs, gs.evalE, gs.evalConvArgs] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem evalLoc_astep_known (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ) :
    Approx (evalLoc G F (n + 1) l (calldataKnown := known)) (evalLoc G F (n + 1 + 1) l (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases l <;> below_unfold evalLoc n <;> approx_go [ih.evalE, ih.evalLoc, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalLoc, gs.evalE, gs.evalLoc] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem evalBuiltin_apart_0_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .require ∨ b = .assert ∨ b = .revert) :
    Approx (evalBuiltin G F (n + 1) b args τ (calldataKnown := known)) (evalBuiltin G F (n + 1 + 1) b args τ (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  rcases hb with rfl | rfl | rfl <;> below_unfold evalBuiltin n <;> approx_go [ih.evalArgs, ih.evalBuiltin, ih.evalArgsRev, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalArgs, gn.evalBuiltin, gn.evalArgsRev, gs.evalArgs, gs.evalBuiltin, gs.evalArgsRev] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem evalBuiltin_apart_1_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .keccak256 ∨ b = .sha256 ∨ b = .ripemd160) :
    Approx (evalBuiltin G F (n + 1) b args τ (calldataKnown := known)) (evalBuiltin G F (n + 1 + 1) b args τ (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  rcases hb with rfl | rfl | rfl <;> below_unfold evalBuiltin n <;> approx_go [ih.evalArgs, ih.evalBuiltin, ih.evalArgsRev, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalArgs, gn.evalBuiltin, gn.evalArgsRev, gs.evalArgs, gs.evalBuiltin, gs.evalArgsRev] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem evalBuiltin_apart_2_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .addmod) :
    Approx (evalBuiltin G F (n + 1) b args τ (calldataKnown := known)) (evalBuiltin G F (n + 1 + 1) b args τ (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  rcases hb with rfl <;> below_unfold evalBuiltin n <;> approx_go [ih.evalArgs, ih.evalBuiltin, ih.evalArgsRev, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalArgs, gn.evalBuiltin, gn.evalArgsRev, gs.evalArgs, gs.evalBuiltin, gs.evalArgsRev] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem evalBuiltin_apart_3_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .mulmod) :
    Approx (evalBuiltin G F (n + 1) b args τ (calldataKnown := known)) (evalBuiltin G F (n + 1 + 1) b args τ (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  rcases hb with rfl <;> below_unfold evalBuiltin n <;> approx_go [ih.evalArgs, ih.evalBuiltin, ih.evalArgsRev, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalArgs, gn.evalBuiltin, gn.evalArgsRev, gs.evalArgs, gs.evalBuiltin, gs.evalArgsRev] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem evalBuiltin_apart_4_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .ecrecover) :
    Approx (evalBuiltin G F (n + 1) b args τ (calldataKnown := known)) (evalBuiltin G F (n + 1 + 1) b args τ (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  rcases hb with rfl <;> below_unfold evalBuiltin n <;> approx_go [ih.evalArgs, ih.evalBuiltin, ih.evalArgsRev, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalArgs, gn.evalBuiltin, gn.evalArgsRev, gs.evalArgs, gs.evalBuiltin, gs.evalArgsRev] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem evalBuiltin_astep_known (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {σs : List STy} (b : Builtin)
    (args : RArgs E Γ σs) (τ : STy) :
    Approx (evalBuiltin G F (n + 1) b args τ (calldataKnown := known)) (evalBuiltin G F (n + 1 + 1) b args τ (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases b
  all_goals first
    | exact evalBuiltin_apart_0_known ih known F _ args τ (by decide)
    | exact evalBuiltin_apart_1_known ih known F _ args τ (by decide)
    | exact evalBuiltin_apart_2_known ih known F _ args τ (by decide)
    | exact evalBuiltin_apart_3_known ih known F _ args τ (by decide)
    | exact evalBuiltin_apart_4_known ih known F _ args τ (by decide)
    | (below_unfold evalBuiltin n; approx_go [ih.evalArgs, ih.evalBuiltin, ih.evalArgsRev, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalArgs, gn.evalBuiltin, gn.evalArgsRev, gs.evalArgs, gs.evalBuiltin, gs.evalArgsRev] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])


theorem evalArgsRev_astep_known (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Approx (evalArgsRev G F (n + 1) es (calldataKnown := known)) (evalArgsRev G F (n + 1 + 1) es (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases es <;> below_unfold evalArgsRev n <;> approx_go [ih.evalE, ih.evalArgsRev, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalArgsRev, gs.evalE, gs.evalArgsRev] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem pay_astep_known (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true))
    (v : RExpr E Γ (.int IntTy.u256)) : Approx (pay G F (n + 1) a v (calldataKnown := known)) (pay G F (n + 1 + 1) a v (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  below_unfold pay n
  approx_go [ih.evalE, ih.pay, ih.callAddr, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.pay, gn.callAddr, gs.evalE, gs.pay, gs.callAddr] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem execS_apart_0_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ)
    (h : 0 ≤ s.ctorIdx ∧ s.ctorIdx < 8) :
    Approx (execS G F (n + 1) nps ph s l (calldataKnown := known)) (execS G F (n + 1 + 1) nps ph s l (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases s <;> first | (exfalso; simp only [RStmt.ctorIdx] at h; omega) | (below_unfold execS n; approx_go [ih.evalE, ih.evalConvArgs, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callLibrary, ih.callAddr, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalConvArgs, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callLibrary, gn.callAddr, gs.evalE, gs.evalConvArgs, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callLibrary, gs.callAddr] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])


theorem execS_apart_1_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ)
    (h : 8 ≤ s.ctorIdx ∧ s.ctorIdx < 16) :
    Approx (execS G F (n + 1) nps ph s l (calldataKnown := known)) (execS G F (n + 1 + 1) nps ph s l (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases s <;> first | (exfalso; simp only [RStmt.ctorIdx] at h; omega) | (below_unfold execS n; approx_go [ih.evalE, ih.evalConvArgs, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callLibrary, ih.callAddr, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalConvArgs, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callLibrary, gn.callAddr, gs.evalE, gs.evalConvArgs, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callLibrary, gs.callAddr] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])


theorem execS_apart_2_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ)
    (h : 16 ≤ s.ctorIdx ∧ s.ctorIdx < 40) :
    Approx (execS G F (n + 1) nps ph s l (calldataKnown := known)) (execS G F (n + 1 + 1) nps ph s l (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases s <;> first | (exfalso; simp only [RStmt.ctorIdx] at h; omega) | (below_unfold execS n; approx_go [ih.evalE, ih.evalConvArgs, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callLibrary, ih.callAddr, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalConvArgs, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callLibrary, gn.callAddr, gs.evalE, gs.evalConvArgs, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callLibrary, gs.callAddr] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])


theorem execS_astep_known (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) :
    Approx (execS G F (n + 1) nps ph s l (calldataKnown := known)) (execS G F (n + 1 + 1) nps ph s l (calldataKnown := known)) := by
  by_cases h0 : s.ctorIdx < 8
  · exact execS_apart_0_known ih known F nps ph s l ⟨Nat.zero_le _, h0⟩
  by_cases h1 : s.ctorIdx < 16
  · exact execS_apart_1_known ih known F nps ph s l ⟨by omega, h1⟩
  have h2 : s.ctorIdx < 40 := by cases s <;> simp only [RStmt.ctorIdx] <;> omega
  exact execS_apart_2_known ih known F nps ph s l ⟨by omega, h2⟩


theorem forIter_astep_known (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool}
    {Γ₁ Γ₂ : RCtx} (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂)
    (l : Locals E.layout Γ₁) :
    Approx (forIter G F (n + 1) nps ph c post body l (calldataKnown := known)) (forIter G F (n + 1 + 1) nps ph c post body l (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases c <;> below_unfold forIter n <;> approx_go [ih.evalE, ih.execS, ih.forIter, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.execS, gn.forIter, gs.evalE, gs.execS, gs.forIter] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem execItems_astep_known (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) :
    Approx (execItems G F (n + 1) nps ph b l (calldataKnown := known)) (execItems G F (n + 1 + 1) nps ph b l (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases b <;> below_unfold execItems n <;> approx_go [ih.execS, ih.execItems, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.execS, gn.execItems, gs.execS, gs.execItems] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem runMods_astep_known (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals))
    (l : Locals E.layout b.locals) : Approx (runMods G F (n + 1) b mods l (calldataKnown := known)) (runMods G F (n + 1 + 1) b mods l (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  cases mods with
  | nil => below_unfold runMods n; approx_go [ih.evalConvArgs, ih.execItems, ih.runMods, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalConvArgs, gn.execItems, gn.runMods, gn.dispatch, gs.evalConvArgs, gs.execItems, gs.runMods, gs.dispatch] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
  | cons md rest =>
    below_unfold runMods n
    refine Approx.bind (Approx.sub _ (ih.evalConvArgs known _ _)) fun p => ?_
    split
    · exact Approx.refl (by grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callLibrary, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callLibrary, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch])
    · split
      · refine Approx.bind (Approx.refl (by grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callLibrary, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callLibrary, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch])) fun s => ?_
        refine Approx.bind (Approx.refl (by grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callLibrary, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callLibrary, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch])) fun _ => ?_
        refine Approx.attempt_bind (ih.execItems known _ _ _ _ _) (fun r => ?_) (fun x => ?_)
        · approx_go [ih.evalConvArgs, ih.execItems, ih.runMods, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalConvArgs, gn.execItems, gn.runMods, gn.dispatch, gs.evalConvArgs, gs.execItems, gs.runMods, gs.dispatch] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
        · exact ⟨rfl, rfl⟩
      · exact Approx.refl (by grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callLibrary, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callLibrary, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch])


theorem callInternal_astep_known (ih : ApproxAtKnown G n) (known : Bool) (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps)
    (rs : List STy) : Approx (callInternal G F (n + 1) d vs rs (calldataKnown := known)) (callInternal G F (n + 1 + 1) d vs rs (calldataKnown := known)) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  below_unfold callInternal n
  approx_go [ih.runMods, ih.callInternal, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.runMods, gn.callInternal, gs.runMods, gs.callInternal] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem callAddr_astep_known (ih : ApproxAtKnown G n) (F : Fr) (a : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) :
    Approx (callAddr G F (n + 1) a v input static) (callAddr G F (n + 1 + 1) a v input static) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  below_unfold callAddr n
  approx_go [ih.callAddr, ih.enterInstance, ih.envLoop, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.callAddr, gn.enterInstance, gn.envLoop, gs.callAddr, gs.enterInstance, gs.envLoop] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem enterInstance_astep_known (ih : ApproxAtKnown G n) (a sender : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout) :
    Approx (enterInstance G (n + 1) a sender v input static c depth m)
      (enterInstance G (n + 1 + 1) a sender v input static c depth m) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  below_unfold enterInstance n
  refine Approx.bind (Approx.refl (by grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callLibrary, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callLibrary, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch])) fun _ => ?_
  refine Approx.attempt_bind (ih.dispatch _ _) (fun r => ?_) (fun x => ?_)
  · exact Approx.refl (by grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callLibrary, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callLibrary, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch])
  · exact ⟨rfl, rfl⟩


theorem envLoop_astep_known (ih : ApproxAtKnown G n) (depth : Nat) (pstatic : Bool) :
    Approx (envLoop G (n + 1) depth pstatic) (envLoop G (n + 1 + 1) depth pstatic) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  below_unfold envLoop n
  approx_go [ih.enterInstance, ih.envLoop, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.enterInstance, gn.envLoop, gs.enterInstance, gs.envLoop] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem dispatch_apart_fn_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (F : Fr) (input : Bytes) {d : Decl}
    (hp : G.pickFn F input = some d) (he : input.isEmpty = false) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  simp only [dispatch, hp, he]; approx_go [ih.evalE, ih.runMods, ih.callInternal, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.runMods, gn.callInternal, gn.dispatch, gs.evalE, gs.runMods, gs.callInternal, gs.dispatch] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem dispatch_apart_gn_c_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} {ri : RInit E}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = true) (hc : G.prog.consts d = some ri) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  simp only [dispatch, hp, hc, hg, hm, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]; approx_go [ih.evalE, ih.runMods, ih.callInternal, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.runMods, gn.callInternal, gn.dispatch, gs.evalE, gs.runMods, gs.callInternal, gs.dispatch] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem dispatch_apart_gn_v_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} {τ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = true) (hc : G.prog.consts d = none) (hv : d.varTy E = some τ) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  simp only [dispatch, hp, hc, hv, hg, hm, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]; approx_go [ih.evalE, ih.runMods, ih.callInternal, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.runMods, gn.callInternal, gn.dispatch, gs.evalE, gs.runMods, gs.callInternal, gs.dispatch] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem dispatch_apart_gn_x_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = true) (hc : G.prog.consts d = none) (hv : d.varTy E = none) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  simp only [dispatch, hp, hc, hv, hg, hm, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]; approx_go [ih.evalE, ih.runMods, ih.callInternal, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.runMods, gn.callInternal, gn.dispatch, gs.evalE, gs.runMods, gs.callInternal, gs.dispatch] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem dispatch_apart_gn_u_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = false) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  simp only [dispatch, hp, hg, hm, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, halt_bind]; approx_go [ih.evalE, ih.runMods, ih.callInternal, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.runMods, gn.callInternal, gn.dispatch, gs.evalE, gs.runMods, gs.callInternal, gs.dispatch] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem dispatch_apart_gn_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {r : Decl × List STy × STy} (hg : G.pickGetter F input = some r) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  obtain ⟨d, ps, ρ⟩ := r
  cases hm : (ρ :: ps).all STy.isValueTy with
  | false => exact dispatch_apart_gn_u_known ih F input hp hg hm
  | true =>
    cases hc : G.prog.consts d with
    | some ri => exact dispatch_apart_gn_c_known ih F input hp hg hm hc
    | none =>
      cases hv : d.varTy E with
      | some τ => exact dispatch_apart_gn_v_known ih F input hp hg hm hc hv
      | none => exact dispatch_apart_gn_x_known ih F input hp hg hm hc hv


theorem dispatch_apart_gs_c_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} {ri : RInit E}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = true) (hc : G.prog.consts d = some ri) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  simp only [dispatch, hp, he, hc, hg, hm, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]; approx_go [ih.evalE, ih.runMods, ih.callInternal, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.runMods, gn.callInternal, gn.dispatch, gs.evalE, gs.runMods, gs.callInternal, gs.dispatch] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem dispatch_apart_gs_v_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} {τ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = true) (hc : G.prog.consts d = none) (hv : d.varTy E = some τ) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  simp only [dispatch, hp, he, hc, hv, hg, hm, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]; approx_go [ih.evalE, ih.runMods, ih.callInternal, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.runMods, gn.callInternal, gn.dispatch, gs.evalE, gs.runMods, gs.callInternal, gs.dispatch] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem dispatch_apart_gs_x_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = true) (hc : G.prog.consts d = none) (hv : d.varTy E = none) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  simp only [dispatch, hp, he, hc, hv, hg, hm, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]; approx_go [ih.evalE, ih.runMods, ih.callInternal, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.runMods, gn.callInternal, gn.dispatch, gs.evalE, gs.runMods, gs.callInternal, gs.dispatch] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem dispatch_apart_gs_u_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = false) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  simp only [dispatch, hp, he, hg, hm, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, halt_bind]; approx_go [ih.evalE, ih.runMods, ih.callInternal, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.runMods, gn.callInternal, gn.dispatch, gs.evalE, gs.runMods, gs.callInternal, gs.dispatch] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem dispatch_apart_gs_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {r : Decl × List STy × STy} (hg : G.pickGetter F input = some r) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  obtain ⟨d, ps, ρ⟩ := r
  cases hm : (ρ :: ps).all STy.isValueTy with
  | false => exact dispatch_apart_gs_u_known ih F input hp he hg hm
  | true =>
    cases hc : G.prog.consts d with
    | some ri => exact dispatch_apart_gs_c_known ih F input hp he hg hm hc
    | none =>
      cases hv : d.varTy E with
      | some τ => exact dispatch_apart_gs_v_known ih F input hp he hg hm hc hv
      | none => exact dispatch_apart_gs_x_known ih F input hp he hg hm hc hv


theorem dispatch_apart_sn_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (F : Fr) (input : Bytes)
    (hp : G.pickFn F input = none) (hg : G.pickGetter F input = none) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  simp only [dispatch, hp, hg]; approx_go [ih.evalE, ih.runMods, ih.callInternal, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.runMods, gn.callInternal, gn.dispatch, gs.evalE, gs.runMods, gs.callInternal, gs.dispatch] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem dispatch_apart_ss_known {G : Glob E} {n : Nat} (ih : ApproxAtKnown G n) (F : Fr) (input : Bytes) {d : Decl}
    (hp : G.pickFn F input = some d) (he : input.isEmpty = true) (hg : G.pickGetter F input = none) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAtKnown G n
  have gs := growAtKnown G (n + 1)
  simp only [dispatch, hp, he, hg]; approx_go [ih.evalE, ih.runMods, ih.callInternal, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.runMods, gn.callInternal, gn.dispatch, gs.evalE, gs.runMods, gs.callInternal, gs.dispatch] [convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, pushVals_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]


theorem dispatch_astep_known (ih : ApproxAtKnown G n) (F : Fr) (input : Solidity.Roadmap.Bytes) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  cases hp : G.pickFn F input with
  | some d =>
    cases he : input.isEmpty with
    | false => exact dispatch_apart_fn_known ih F input hp he
    | true =>
      cases hg : G.pickGetter F input with
      | some r => exact dispatch_apart_gs_known ih F input hp he hg
      | none => exact dispatch_apart_ss_known ih F input hp he hg
  | none =>
    cases hg : G.pickGetter F input with
    | some r => exact dispatch_apart_gn_known ih F input hp hg
    | none => exact dispatch_apart_sn_known ih F input hp hg


theorem approxAtKnown (G : Glob E) : ∀ n, ApproxAtKnown G n := by
  intro n
  induction n with
  | zero => exact approxAtKnown_zero G
  | succ n ih => exact ⟨evalE_astep_known ih, evalPair_astep_known ih, evalArgs_astep_known ih, evalConvArgs_astep_known ih, evalLoc_astep_known ih, evalBuiltin_astep_known ih, evalArgsRev_astep_known ih, pay_astep_known ih, execS_astep_known ih, forIter_astep_known ih, execItems_astep_known ih, runMods_astep_known ih, callInternal_astep_known ih, callLibrary_astep_known ih, callAddr_astep_known ih, enterInstance_astep_known ih, envLoop_astep_known ih, dispatch_astep_known ih⟩

end

section
variable (G : Glob E)

/-- **The induction hypothesis**: every interpreter function at horizon `n`
approximates itself at `n + 1`. -/
structure ApproxAt (n : Nat) : Prop where
  evalE : ∀ (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ), Approx (evalE G F n e) (evalE G F (n + 1) e)
  evalPair : ∀ (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ),
    Approx (evalPair G F n a b) (evalPair G F (n + 1) a b)
  evalArgs : ∀ (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs),
    Approx (evalArgs G F n es) (evalArgs G F (n + 1) es)
  evalConvArgs : ∀ (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs),
    Approx (evalConvArgs G F n es) (evalConvArgs G F (n + 1) es)
  evalLoc : ∀ (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ), Approx (evalLoc G F n l) (evalLoc G F (n + 1) l)
  evalBuiltin : ∀ (F : Fr) {Γ : RCtx} {σs : List STy} (b : Builtin) (args : RArgs E Γ σs) (τ : STy),
    Approx (evalBuiltin G F n b args τ) (evalBuiltin G F (n + 1) b args τ)
  evalArgsRev : ∀ (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs),
    Approx (evalArgsRev G F n es) (evalArgsRev G F (n + 1) es)
  pay : ∀ (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true)) (v : RExpr E Γ (.int IntTy.u256)),
    Approx (pay G F n a v) (pay G F (n + 1) a v)
  execS : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ),
    Approx (execS G F n nps ph s l) (execS G F (n + 1) nps ph s l)
  forIter : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool} {Γ₁ Γ₂ : RCtx}
    (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (l : Locals E.layout Γ₁),
    Approx (forIter G F n nps ph c post body l) (forIter G F (n + 1) nps ph c post body l)
  execItems : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ),
    Approx (execItems G F n nps ph b l) (execItems G F (n + 1) nps ph b l)
  runMods : ∀ (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals)) (l : Locals E.layout b.locals),
    Approx (runMods G F n b mods l) (runMods G F (n + 1) b mods l)
  callInternal : ∀ (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps) (rs : List STy),
    Approx (callInternal G F n d vs rs) (callInternal G F (n + 1) d vs rs)
  callAddr : ∀ (F : Fr) (a : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word) (input : Solidity.Roadmap.Bytes)
    (static : Bool), Approx (callAddr G F n a v input static) (callAddr G F (n + 1) a v input static)
  enterInstance : ∀ (a sender : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word) (input : Solidity.Roadmap.Bytes)
    (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout),
    Approx (enterInstance G n a sender v input static c depth m)
      (enterInstance G (n + 1) a sender v input static c depth m)
  envLoop : ∀ (depth : Nat) (pstatic : Bool), Approx (envLoop G n depth pstatic) (envLoop G (n + 1) depth pstatic)
  dispatch : ∀ (F : Fr) (input : Solidity.Roadmap.Bytes), Approx (dispatch G F n input) (dispatch G F (n + 1) input)

theorem approxAt_zero : ApproxAt G 0 where
  evalE := by intros; rw [evalE.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalE
  evalPair := by intros; rw [evalPair.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalPair
  evalArgs := by intros; rw [evalArgs.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalArgs
  evalConvArgs := by intros; rw [evalConvArgs.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalConvArgs
  evalLoc := by intros; rw [evalLoc.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalLoc
  evalBuiltin := by intros; rw [evalBuiltin.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalBuiltin
  evalArgsRev := by intros; rw [evalArgsRev.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalArgsRev
  pay := by intros; rw [pay.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).pay
  execS := by intros; rw [execS.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).execS
  forIter := by intros; rw [forIter.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).forIter
  execItems := by intros; rw [execItems.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).execItems
  runMods := by intros; rw [runMods.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).runMods
  callInternal := by intros; rw [callInternal.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).callInternal
  callAddr := by intros; rw [callAddr.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).callAddr
  enterInstance := by intros; rw [enterInstance.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).enterInstance
  envLoop := by intros; rw [envLoop.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).envLoop
  dispatch := by intros; rw [dispatch.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).dispatch

variable {G} {n : Nat}

theorem evalE_apart_0 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 0 ≤ e.ctorIdx ∧ e.ctorIdx < 12) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalE_apart_1 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 12 ≤ e.ctorIdx ∧ e.ctorIdx < 24) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalE_apart_2 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 24 ≤ e.ctorIdx ∧ e.ctorIdx < 28) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalE_apart_3 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 28 ≤ e.ctorIdx ∧ e.ctorIdx < 32) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalE_apart_4 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 32 ≤ e.ctorIdx ∧ e.ctorIdx < 33) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalE_apart_5 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 33 ≤ e.ctorIdx ∧ e.ctorIdx < 34) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalE_apart_6 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 34 ≤ e.ctorIdx ∧ e.ctorIdx < 35) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalE_apart_7 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 35 ≤ e.ctorIdx ∧ e.ctorIdx < 36) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalE_apart_8 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 36 ≤ e.ctorIdx ∧ e.ctorIdx < 60) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalE_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) :
    Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalPair_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ) :
    Approx (evalPair G F (n + 1) a b) (evalPair G F (n + 1 + 1) a b) := by
  exact (approxAtKnown G (n + 1)).evalPair true F a b

theorem evalArgs_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Approx (evalArgs G F (n + 1) es) (evalArgs G F (n + 1 + 1) es) := by
  exact (approxAtKnown G (n + 1)).evalArgs true F es

theorem evalConvArgs_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs) :
    Approx (evalConvArgs G F (n + 1) es) (evalConvArgs G F (n + 1 + 1) es) := by
  exact (approxAtKnown G (n + 1)).evalConvArgs true F es

theorem evalLoc_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ) :
    Approx (evalLoc G F (n + 1) l) (evalLoc G F (n + 1 + 1) l) := by
  exact (approxAtKnown G (n + 1)).evalLoc true F l

theorem evalBuiltin_apart_0 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .require ∨ b = .assert ∨ b = .revert) :
    Approx (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  exact (approxAtKnown G (n + 1)).evalBuiltin true F b args τ

theorem evalBuiltin_apart_1 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .keccak256 ∨ b = .sha256 ∨ b = .ripemd160) :
    Approx (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  exact (approxAtKnown G (n + 1)).evalBuiltin true F b args τ

theorem evalBuiltin_apart_2 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .addmod) :
    Approx (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  exact (approxAtKnown G (n + 1)).evalBuiltin true F b args τ

theorem evalBuiltin_apart_3 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .mulmod) :
    Approx (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  exact (approxAtKnown G (n + 1)).evalBuiltin true F b args τ

theorem evalBuiltin_apart_4 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .ecrecover) :
    Approx (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  exact (approxAtKnown G (n + 1)).evalBuiltin true F b args τ

theorem evalBuiltin_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σs : List STy} (b : Builtin)
    (args : RArgs E Γ σs) (τ : STy) :
    Approx (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  exact (approxAtKnown G (n + 1)).evalBuiltin true F b args τ

theorem evalArgsRev_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Approx (evalArgsRev G F (n + 1) es) (evalArgsRev G F (n + 1 + 1) es) := by
  exact (approxAtKnown G (n + 1)).evalArgsRev true F es

theorem pay_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true))
    (v : RExpr E Γ (.int IntTy.u256)) : Approx (pay G F (n + 1) a v) (pay G F (n + 1 + 1) a v) := by
  exact (approxAtKnown G (n + 1)).pay true F a v

theorem execS_apart_0 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ)
    (h : 0 ≤ s.ctorIdx ∧ s.ctorIdx < 8) :
    Approx (execS G F (n + 1) nps ph s l) (execS G F (n + 1 + 1) nps ph s l) := by
  exact (approxAtKnown G (n + 1)).execS true F nps ph s l

theorem execS_apart_1 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ)
    (h : 8 ≤ s.ctorIdx ∧ s.ctorIdx < 16) :
    Approx (execS G F (n + 1) nps ph s l) (execS G F (n + 1 + 1) nps ph s l) := by
  exact (approxAtKnown G (n + 1)).execS true F nps ph s l

theorem execS_apart_2 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ)
    (h : 16 ≤ s.ctorIdx ∧ s.ctorIdx < 40) :
    Approx (execS G F (n + 1) nps ph s l) (execS G F (n + 1 + 1) nps ph s l) := by
  exact (approxAtKnown G (n + 1)).execS true F nps ph s l

theorem execS_astep (ih : ApproxAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) :
    Approx (execS G F (n + 1) nps ph s l) (execS G F (n + 1 + 1) nps ph s l) := by
  exact (approxAtKnown G (n + 1)).execS true F nps ph s l

theorem forIter_astep (ih : ApproxAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool}
    {Γ₁ Γ₂ : RCtx} (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂)
    (l : Locals E.layout Γ₁) :
    Approx (forIter G F (n + 1) nps ph c post body l) (forIter G F (n + 1 + 1) nps ph c post body l) := by
  exact (approxAtKnown G (n + 1)).forIter true F nps ph c post body l

theorem execItems_astep (ih : ApproxAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) :
    Approx (execItems G F (n + 1) nps ph b l) (execItems G F (n + 1 + 1) nps ph b l) := by
  exact (approxAtKnown G (n + 1)).execItems true F nps ph b l

theorem runMods_astep (ih : ApproxAt G n) (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals))
    (l : Locals E.layout b.locals) : Approx (runMods G F (n + 1) b mods l) (runMods G F (n + 1 + 1) b mods l) := by
  exact (approxAtKnown G (n + 1)).runMods true F b mods l

theorem callInternal_astep (ih : ApproxAt G n) (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps)
    (rs : List STy) : Approx (callInternal G F (n + 1) d vs rs) (callInternal G F (n + 1 + 1) d vs rs) := by
  exact (approxAtKnown G (n + 1)).callInternal true F d vs rs

theorem callAddr_astep (ih : ApproxAt G n) (F : Fr) (a : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) :
    Approx (callAddr G F (n + 1) a v input static) (callAddr G F (n + 1 + 1) a v input static) := by
  exact (approxAtKnown G (n + 1)).callAddr F a v input static

theorem enterInstance_astep (ih : ApproxAt G n) (a sender : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout) :
    Approx (enterInstance G (n + 1) a sender v input static c depth m)
      (enterInstance G (n + 1 + 1) a sender v input static c depth m) := by
  exact (approxAtKnown G (n + 1)).enterInstance a sender v input static c depth m

theorem envLoop_astep (ih : ApproxAt G n) (depth : Nat) (pstatic : Bool) :
    Approx (envLoop G (n + 1) depth pstatic) (envLoop G (n + 1 + 1) depth pstatic) := by
  exact (approxAtKnown G (n + 1)).envLoop depth pstatic

theorem dispatch_apart_fn {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d : Decl}
    (hp : G.pickFn F input = some d) (he : input.isEmpty = false) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gn_c {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} {ri : RInit E}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = true) (hc : G.prog.consts d = some ri) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gn_v {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} {τ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = true) (hc : G.prog.consts d = none) (hv : d.varTy E = some τ) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gn_x {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} 
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = true) (hc : G.prog.consts d = none) (hv : d.varTy E = none) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gn_u {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} 
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = false) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gn {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {r : Decl × List STy × STy} (hg : G.pickGetter F input = some r) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gs_c {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} {ri : RInit E}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = true) (hc : G.prog.consts d = some ri) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gs_v {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} {τ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = true) (hc : G.prog.consts d = none) (hv : d.varTy E = some τ) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gs_x {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} 
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = true) (hc : G.prog.consts d = none) (hv : d.varTy E = none) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gs_u {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} 
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = false) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gs {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {r : Decl × List STy × STy} (hg : G.pickGetter F input = some r) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_sn {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes)
    (hp : G.pickFn F input = none) (hg : G.pickGetter F input = none) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_ss {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d : Decl}
    (hp : G.pickFn F input = some d) (he : input.isEmpty = true) (hg : G.pickGetter F input = none) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_astep (ih : ApproxAt G n) (F : Fr) (input : Solidity.Roadmap.Bytes) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

/-- **Every interpreter function is monotone in its horizon.** -/
theorem approxAt (G : Glob E) : ∀ n, ApproxAt G n
  | 0 => approxAt_zero G
  | n + 1 =>
    have h : ApproxAtKnown G (n + 1) := approxAtKnown G (n + 1)
    ⟨h.evalE true, h.evalPair true, h.evalArgs true, h.evalConvArgs true,
      h.evalLoc true, h.evalBuiltin true, h.evalArgsRev true, h.pay true,
      h.execS true, h.forIter true, h.execItems true, h.runMods true,
      h.callInternal true, h.callAddr, h.enterInstance, h.envLoop,
      h.dispatch⟩

end

/-! ### Transactions show a prefix of their events -/

theorem runTx_grow (G : Glob E) (n : Nat) (q : Request) : Grow (runTx G n q) := by
  have gn := growAt { G with timestamp := q.timestamp } n
  unfold runTx
  dsimp only
  grow_go [gn.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow]

theorem runTx_approx (G : Glob E) (n : Nat) (q : Request) : Approx (runTx G n q) (runTx G (n + 1) q) := by
  have ih := approxAt { G with timestamp := q.timestamp } n
  unfold runTx
  dsimp only
  refine Approx.bind (Approx.refl (mark_grow)) fun m => ?_
  refine Approx.bind (Approx.refl (instanceAt_grow _ _)) fun oc => ?_
  split
  · exact Approx.refl (by grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow])
  · refine Approx.attempt_bind ?_ (fun _ => Approx.refl (by grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow])) (fun _ => ⟨rfl, rfl⟩)
    exact Approx.bind (Approx.refl (credit_grow _ _)) fun _ => ih.dispatch _ _

theorem Approx.mono {Γ : RCtx} {α : Type} {f : Nat → EM E Γ α} (h : ∀ n, Approx (f n) (f (n + 1)))
    (hg : ∀ n, Grow (f n)) {n m : Nat} (hnm : n ≤ m) : Approx (f n) (f m) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction d with
  | zero => exact Approx.refl (hg n)
  | succ d ih => exact (ih (by omega)).trans (h _)

/-- **A transaction's events grow with its horizon**: a run that has not
completed at horizon `k` shows a prefix of the events of the run at every
`k' ≥ k`. -/
theorem runTx_events_mono (G : Glob E) (q : Request) (s : St E) {k k' : Nat} (hk : k ≤ k')
    (hd : Done (runAt (fun f => runTx G f q) s k) = false) :
    (runAt (fun f => runTx G f q) s k).2.events <+: (runAt (fun f => runTx G f q) s k').2.events := by
  have ha := Approx.mono (f := fun f => runTx G f q) (fun n => runTx_approx G n q) (fun n => runTx_grow G n q) hk
  simp only [runAt]
  rcases ha.2.2 (L0 E, s) with ⟨_, he⟩ | he
  · exact he
  · rw [he]; exact List.prefix_refl _

/-- A transaction's events extend the events before it. -/
theorem runTx_extends (G : Glob E) (q : Request) (s : St E) (k : Nat) :
    s.events <+: (runAt (fun f => runTx G f q) s k).2.events := runTx_grow G k q (L0 E, s)

/-- info: 'Solidity.Source.belowAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms belowAt

/-- info: 'Solidity.Source.runTx_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runTx_stable

/-- info: 'Solidity.Source.deploy_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deploy_stable

/-- info: 'Solidity.Source.firstDone_runTx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms firstDone_runTx

/-- info: 'Solidity.Source.runTx_stuck_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runTx_stuck_stable

end Solidity.Source