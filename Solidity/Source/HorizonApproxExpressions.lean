import Solidity.Source.HorizonConst

/-! Event-prefix expression proofs. Guards the regression where one monolithic
Source horizon check exceeds the per-module limit. Declarations retain their
qualified names and are re-exported by Source.Horizon; no evaluator changes. -/

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
  exact { evalE := by intros; apply Approx.timeout; apply (growAtKnown G 1).evalE, evalPair := by intros; apply Approx.timeout; apply (growAtKnown G 1).evalPair, evalArgs := by intros; apply Approx.timeout; apply (growAtKnown G 1).evalArgs, evalConvArgs := by intros; apply Approx.timeout; apply (growAtKnown G 1).evalConvArgs, evalLoc := by intros; apply Approx.timeout; apply (growAtKnown G 1).evalLoc, evalBuiltin := by intros; apply Approx.timeout; apply (growAtKnown G 1).evalBuiltin, evalArgsRev := by intros; apply Approx.timeout; apply (growAtKnown G 1).evalArgsRev, pay := by intros; apply Approx.timeout; apply (growAtKnown G 1).pay, execS := by intros; apply Approx.timeout; apply (growAtKnown G 1).execS, forIter := by intros; apply Approx.timeout; apply (growAtKnown G 1).forIter, execItems := by intros; apply Approx.timeout; apply (growAtKnown G 1).execItems, runMods := by intros; apply Approx.timeout; apply (growAtKnown G 1).runMods, callInternal := by intros; apply Approx.timeout; apply (growAtKnown G 1).callInternal, callLibrary := by intros; apply Approx.timeout; apply (growAtKnown G 1).callLibrary, callAddr := by intros; apply Approx.timeout; apply (growAtKnown G 1).callAddr, enterInstance := by intros; apply Approx.timeout; apply (growAtKnown G 1).enterInstance, envLoop := by intros; apply Approx.timeout; apply (growAtKnown G 1).envLoop, dispatch := by intros; apply Approx.timeout; apply (growAtKnown G 1).dispatch }


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



end
end Solidity.Source
