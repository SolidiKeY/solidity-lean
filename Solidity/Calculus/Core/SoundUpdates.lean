import Solidity.Calculus.Core.SoundArms

/-!
# Soundness of the update arms: arrays, payments, memory

The rules of `Calculus/Core/Arms.lean` and `Step.lean` whose premise is an
update and that `Calculus/Core/SoundArms.lean` does not prove: a push, a pop,
a transfer and a send, a fresh memory object (a declaration, a deep copy, a
new array, a `delete`), and the alias bound to a pushed slot.  Each is
`Premise.Sound.update`: the update, read in the state before, ends as the
statement does.  The global operations are `Semantics.lean`'s, and their
frame lemmas (`pushAt_with`, `popAt_with`, `allocDefault_eq`,
`copyStToM_eq`) are `Calculus/SoundUpdate.lean`'s, read on `σ.glob`.
-/

namespace Solidity.Core

open Solidity (Modality Srt Op0 Op1 Op2 Op3 NoPanic)
open Semantics (Value SVal MVal Seg Halt Res)

variable {C : Contract}

section Updates

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

/-- **An update** is sound when it ends as the statement does up to the halt. -/
theorem Premise.Sound.updateSim {Γ' : Ctx} {U : Upd C Γ Γ'} {s : Stmt C Γ Γ'}
    (hs : Res.Sim (U.apply σ) (s.run σ)) : Premise.Sound m s (.update U) σ := by
  intro Γ₁ Γ₀ ω κ φ h
  have hU : NoPanic (U.apply σ) := Upd.apply_noPanic σ U
  refine holds_modal_intro fun hT => ?_
  have h' := (holds_upd U _ hT).1 h
  rw [run_cons_frames]
  revert hs hU h'
  cases U.apply σ with
  | ok τ =>
    cases s.run σ with
    | ok τ' =>
      intro hs _ h'
      cases (hs : τ = τ')
      exact (holds_modalK m ω κ φ τ (Modality.okP_ok h')).1
        ((Modality.okP_iff (Modality.okP_ok h')).1 h')
    | error => intro hs; exact hs.elim
  | error e =>
    cases s.run σ with
    | ok => intro hs; exact hs.elim
    | error e' =>
      intro hs hU h'
      refine ⟨h', fun hp => hU ?_⟩
      exact congrArg Except.error (hs.2 (Except.error.inj hp))

/-! ### Push and pop -/

theorem storage_push_glob (x : Res Semantics.State)
    (hx : (x >>= fun τ => pure { σ.glob with storage := τ.storage }) = x) :
    (x >>= fun st => pure (σ.withGlob { σ.glob with storage := st.storage })) = σ.withGlob <$> x :=
  storage_glob σ x hx

/-- `storagePushLengthSave`: `{storage := pushSlot(storage, b)}` for `b.push();`. -/
theorem sound_pushSlot {E : Ty} (b : SPath C Γ (.array E)) (hd : (none.isSome || E.defaultOkS) = true) :
    Premise.Sound m (.push b none hd) (.upd1 (.storage (.app2 (.pushSlot E) .storage b.lower))) σ :=
  Premise.Sound.update (by
    rw [upd1_apply]
    show (do
      let st ← Op2.eval σ.glob (.pushSlot E) (pure σ.glob) (b.lower.eval σ)
      pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.push b none σ
    simp only [Op2.eval, SPath.eval_lower, Run.push, bind_assoc, pure_bind]
    congr 1; funext q
    exact storage_glob σ _ (Solidity.pushAt_with _ _ _ _ _))

/-- `storagePushLengthSaveReferenceElement`: `{storage := extend(storage, b)}`. -/
theorem sound_extend {E : Ty} (b : SPath C Γ (.array E)) (hd : (none.isSome || E.defaultOkS) = true) :
    Premise.Sound m (.push b none hd) (.upd1 (.storage (.app2 (.extend E) .storage b.lower))) σ :=
  Premise.Sound.update (by
    rw [upd1_apply]
    show (do
      let st ← Op2.eval σ.glob (.extend E) (pure σ.glob) (b.lower.eval σ)
      pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.push b none σ
    simp only [Op2.eval, SPath.eval_lower, Run.push, pushPlaceAt, pushAt, Src.pushVal,
      SemanticsProperties.State.saveStorage_eq, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
    cases b.resolve σ with
    | error => rfl
    | ok q =>
      simp only
      cases σ.glob.findStorage q.1 q.2 with
      | error => rfl
      | ok v =>
        cases v with
        | array elems shadow fx =>
          simp only
          cases σ.glob.storeRes q.1 q.2 _ <;> rfl
        | _ => rfl)

/-- `storagePushValueSave`, `storagePushValueCopySource`: `{storage := push(storage, b, src)}`. -/
theorem sound_pushSome {E : Ty} (b : SPath C Γ (.array E)) (r : Src C Γ E)
    (hd : ((some r).isSome || E.defaultOkS) = true) :
    Premise.Sound m (.push b (some r) hd) (.upd1 (.storage (.app3 .push .storage b.lower r.lower))) σ :=
  Premise.Sound.update (by
    rw [upd1_apply]
    show (do
      let st ← Op3.eval σ.glob .push (pure σ.glob) (b.lower.eval σ) (r.lower.eval σ)
      pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.push b (some r) σ
    simp only [Op3.eval, SPath.eval_lower, Src.eval_lower, Run.push, bind_assoc, pure_bind]
    congr 1; funext q
    rw [show Src.pushVal σ (some r) = fun _ => (do pure (← r.value σ).strip) from rfl,
      Solidity.pushAt_const σ.glob E .uint]
    exact storage_glob σ _ (Solidity.pushAt_with _ _ _ _ _))

/-- `storagePopSave`, `storagePopSaveMappingElement`: `{storage := pop(storage, b)}`,
`{storage := shrink(storage, b)}` when the elements are mappings. -/
theorem sound_pop {E : Ty} (b : SPath C Γ (.array E)) :
    Premise.Sound m (.pop b) (.upd1 (.storage (.app2 (if E.isMapping then .shrink else .pop)
      .storage b.lower))) σ :=
  Premise.Sound.update (by
    rw [upd1_apply]
    cases hE : E.isMapping with
    | false =>
      show (do
        let st ← Op2.eval σ.glob .pop (pure σ.glob) (b.lower.eval σ)
        pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.pop b σ
      simp only [Op2.eval, SPath.eval_lower, Run.pop, hE, bind_assoc, pure_bind]
      congr 1; funext q
      exact storage_glob σ _ (Solidity.popAt_with _ _ _ _)
    | true =>
      show (do
        let st ← Op2.eval σ.glob .shrink (pure σ.glob) (b.lower.eval σ)
        pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.pop b σ
      simp only [Op2.eval, SPath.eval_lower, Run.pop, hE, bind_assoc, pure_bind]
      congr 1; funext q
      exact storage_glob σ _ (Solidity.popAt_with _ _ _ _))

/-- `storageLocalRootPushBind`, `storageLocalRootPushBindMappingElement`:
`{storage := extend(storage, b) ‖ lsv := next(b)}` for `lsv = b.push();`. -/
theorem sound_rebindPush {R : RefTy} (i : Idx Γ (.alias R)) (b : SPath C Γ (.array (.ref R)))
    (hd : (Ty.ref R).defaultOkS = true) :
    Premise.Sound m (.rebind i (.push b hd)) (.update ((Upd.nil.snoc
      (.storage (.app2 (.extend (.ref R)) .storage b.lower))).snoc
      (.local i (.path (.app1 .next rfl b.lower))))) σ :=
  Premise.Sound.update (by
    rw [upd2_apply]
    show _ = Run.rebind i (.push b hd) σ
    simp only [UpdElem.write, Rhs.eval, Tm.eval, Op2.eval, Op1.eval, Op0.eval, SPath.eval_lower,
      Run.rebind, ARhs.eval, pushPlaceAt, SemanticsProperties.State.saveStorage_eq, bind_assoc,
      pure_bind]
    simp only [bind, Except.bind, pure, Except.pure]
    cases b.resolve σ with
    | error => rfl
    | ok q =>
      simp only
      cases σ.glob.findStorage q.1 q.2 with
      | error => rfl
      | ok v =>
        cases v with
        | array elems shadow fx =>
          simp only
          cases σ.glob.storeRes q.1 q.2 _ <;> rfl
        | _ => rfl)

/-! ### Payments -/

/-- `transferNoCallbackBox`: `{net := …}` for `sadr.transfer(se);`. -/
theorem sound_transferBox (sadr se : Simple C Γ .uint) :
    Premise.Sound m (.transfer (.simple sadr) (.simple se)) (.upd1 (.payTo sadr se)) σ :=
  Premise.Sound.update (by
    rw [upd1_apply]
    obtain ⟨a, ha⟩ := Simple.eval_ok σ sadr
    obtain ⟨v, hv⟩ := Simple.eval_ok σ se
    show _ = Run.transfer (.simple sadr) (.simple se) σ
    simp only [UpdElem.write, Simple.eval_lower, ha, hv, Run.transfer, Val.eval, transferAt,
      Semantics.State.pay, Res.bind_ok]
    cases a.asInt with
    | error => rfl
    | ok n =>
      cases v.asInt with
      | error => rfl
      | ok k =>
        simp only [Res.bind_ok]
        by_cases hk : k < 0 <;> simp only [hk, ↓reduceIte] <;> rfl)

/-- `transferDiamond` (Lean): the goal fails. -/
theorem sound_done_false {Γ' : Ctx} (s : Stmt C Γ Γ') : Premise.Sound m s (.done false) σ :=
  fun ω κ φ h => Premise.sound_done σ false (fun h => nomatch h) ω κ φ h

/-! ### Several ways to end -/

theorem holds_conj {σ : State C Γ} : (l : List (Fml C Γ)) → (holds σ (Fml.conj l) ↔ ∀ ψ ∈ l, holds σ ψ)
  | [] => by simp only [Fml.conj, holds, List.not_mem_nil, false_implies, implies_true]
  | [φ] => by simp only [Fml.conj, List.mem_singleton, forall_eq]
  | φ :: ψ :: l => by
    show holds σ φ ∧ holds σ (Fml.conj (ψ :: l)) ↔ _
    rw [holds_conj (ψ :: l)]
    simp only [List.mem_cons, forall_eq_or_imp]

/-- **Labelled goals**: the formulas `fs` to prove, then the rest after each
update of `us`, give `⟨ s; ω κ ⟩ φ` when, the formulas holding, the statement
runs as one of the updates up to the halt. -/
theorem Premise.Sound.cases {fs : List (Fml C Γ)} {us : List (Upd C Γ Γ)} {s : Stmt C Γ Γ}
    (h : (∀ f ∈ fs, holds σ f) → ∃ U ∈ us, Res.Sim (U.apply σ) (s.run σ)) :
    Premise.Sound m s (.cases fs us) σ := by
  intro Γ₁ Γ₀ ω κ φ hp
  have hp' := (holds_conj _).1 hp
  obtain ⟨U, hU, hs⟩ := h fun f hf => hp' f (List.mem_append_left _ hf)
  exact Premise.Sound.updateSim σ hs ω κ φ
    (hp' _ (List.mem_append_right _ (List.mem_map_of_mem hU)))

/-- `sendNoCallbackBox`, `sendNoCallbackDiamond`: `pv = sadr.send(se);` runs as
the payment with `pv` true, or as `pv` false. -/
theorem sound_send (pv : Idx Γ (.val .bool)) (sadr se : Simple C Γ .uint) (fs : List (Fml C Γ)) :
    Premise.Sound m (.send pv (.simple sadr) (.simple se)) (.cases fs
      [(Upd.nil.snoc (.payTo sadr se)).snoc (.local pv (.val (Tm.lit (.bool true)))),
        Upd.nil.snoc (.local pv (.val (Tm.lit (.bool false))))]) σ := by
  refine Premise.Sound.cases σ fun _ => ?_
  obtain ⟨a, ha⟩ := Simple.eval_ok σ sadr
  obtain ⟨v, hv⟩ := Simple.eval_ok σ se
  have e₁ : ((Upd.nil.snoc (.payTo sadr se)).snoc
      (.local pv (.val (Tm.lit (.bool true))))).apply σ = (do
        let addr ← a.asInt
        let amt ← v.asInt
        if amt < 0 then .error .revert
        else pure ((σ.withGlob (σ.glob.pay addr amt)).setLocal pv (.bool true))) := by
    rw [upd2_apply]
    simp only [UpdElem.write, Rhs.eval, Tm.eval, Op0.eval, Simple.eval_lower, ha, hv, Res.bind_ok,
      bind_assoc]
    cases a.asInt with
    | error => rfl
    | ok n =>
      cases v.asInt with
      | error => rfl
      | ok k => by_cases hk : k < 0 <;> simp only [Res.bind_ok, hk, ↓reduceIte] <;> rfl
  have e₂ : (Upd.nil.snoc (.local pv (.val (Tm.lit (C := C) (Γ := Γ) (.bool false))))).apply σ =
      .ok (σ.setLocal pv (.bool false)) := rfl
  have hr : Stmt.run σ (.send pv (.simple sadr) (.simple se)) = (do
      let addr ← a.asInt
      let amt ← v.asInt
      sendAt σ pv addr amt) := by
    show Run.send pv _ _ σ = _
    simp only [Run.send, Val.eval, ha, hv, Res.bind_ok]
  rw [hr]
  cases ha' : a.asInt with
  | error e => exact ⟨_, List.mem_cons_self .., by rw [e₁, ha']; exact Res.Sim.refl _⟩
  | ok n =>
    cases hv' : v.asInt with
    | error e => exact ⟨_, List.mem_cons_self .., by rw [e₁, ha', hv']; exact Res.Sim.refl _⟩
    | ok k =>
      rw [ha', hv'] at e₁
      simp only [Res.bind_ok, sendAt] at e₁ ⊢
      by_cases hk : k < 0
      · exact ⟨_, List.mem_cons_self .., by rw [e₁]; simp only [hk, ↓reduceIte]; exact Res.Sim.refl _⟩
      · simp only [hk, ↓reduceIte] at e₁ ⊢
        cases hl : Semantics.lookupBy (sendKey n k) σ.tx.ext with
        | none => exact ⟨_, List.mem_cons_self .., by rw [e₁]; exact Res.Sim.refl _⟩
        | some r =>
          cases r with
          | ok => exact ⟨_, List.mem_cons_self .., by rw [e₁]; exact Res.Sim.refl _⟩
          | _ =>
            exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by rw [e₂]; exact Res.Sim.refl _⟩

/-! ### Fresh memory objects -/

/-- `memoryReferenceDeclFreshAlloc`: `{mv := alloc(memory, R) ‖ memory := addM(memory, R)}`
for `T memory mv;`. -/
theorem sound_declMemFresh (R : RefTy) (x : Var) (hd : (none.isSome || (Ty.ref R).defaultOkS) = true)
    (hm : (Ty.ref R).mapFree = true) :
    Premise.Sound m (.declMem R x none hd hm) (.update ((Upd.nil.decl x
      (.mref (.app1 (.alloc R) rfl .memory))).snoc (.memory (.app1 (.addM R) rfl .memory)))) σ :=
  Premise.Sound.update (by
    show (do
      let τ ← (Upd.nil.decl x (.mref (.app1 (.alloc R) rfl .memory))).apply σ
      UpdElem.write σ (.memory (.app1 (.addM R) rfl .memory)) τ) = Run.declMem R none σ
    simp only [Upd.apply, UpdElem.write, Rhs.eval, Tm.eval, Op1.eval, Op0.eval, Run.declMem,
      Solidity.allocDefault_eq, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure]
    cases Solidity.allocHN σ.glob R <;> rfl)

/-- `memoryRootDeleteFreshRebind`: `{mv := alloc(memory, R) ‖ memory := addM(memory, R)}`
for `delete mv;`. -/
theorem sound_deleteMemVar {R : RefTy} (i : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (hd : (Ty.ref R).defaultOkS = true) :
    Premise.Sound m (.deleteMem (.var i hm) hd) (.update ((Upd.nil.snoc
      (.local i (.mref (.app1 (.alloc R) rfl .memory)))).snoc
      (.memory (.app1 (.addM R) rfl .memory)))) σ :=
  Premise.Sound.update (by
    rw [upd2_apply]
    show _ = Run.deleteMem (.var i hm) σ
    simp only [UpdElem.write, Rhs.eval, Tm.eval, Op1.eval, Op0.eval, Run.deleteMem,
      Solidity.allocDefault_eq, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure]
    cases Solidity.allocHN σ.glob R <;> rfl)

/-- `memoryStorageCopy`, `memoryArrayFreshAlloc`:
`{mv := freshId(copySt(memory, v)) ‖ memory := copySt(memory, v)}`. -/
theorem sound_allocCopy {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) (v : Tm C Γ .sv)
    (hr : r.eval σ = (do
      let (τ, mv) ← Semantics.copyStToM σ.glob (← v.eval σ)
      pure (σ.withGlob τ, ← mv.asRef))) :
    Premise.Sound m (.rebindMem i r) (.allocCopy i v) σ :=
  Premise.Sound.update (by
    rw [upd2_apply]
    show _ = Run.rebindMem i r σ
    simp only [Run.rebindMem, hr, UpdElem.write, Rhs.eval, Tm.eval, Op2.eval, Op0.eval,
      Solidity.copyStToM_eq, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure]
    cases v.eval σ with
    | error => rfl
    | ok sv =>
      simp only
      cases Solidity.copyHN σ.glob sv with
      | error => rfl
      | ok q =>
        simp only
        cases q.2.2.asRef <;> rfl)

/-- `memoryFieldDeletePrimitive`, `memoryIndexDeletePrimitive`,
`memoryFieldDeleteReference`, `memoryIndexDeleteReference`: a slot reset to its
default, `{memory := write(memory, l, defVal)}`, or written a fresh default
object, `{memory := write(addM(memory), l, alloc(memory))}`. -/
theorem sound_clearMem {T : Ty} (l : MLoc C Γ T) (hd : T.defaultOkS = true) :
    Premise.Sound m (.deleteMem (.loc l) hd) (.clearMem l.lower T) σ := by
  cases T with
  | prim p =>
    refine Premise.Sound.update ?_
    rw [upd1_apply]
    show _ = Run.deleteMem (.loc l) σ
    simp only [UpdElem.write, Tm.eval, Op3.eval, Op1.eval, Op0.eval, MLoc.eval_lower_addr,
      Run.deleteMem, memClear, bind_assoc, pure_bind, writeAddr_glob]
  | ref R =>
    refine Premise.Sound.updateSim σ ?_
    rw [upd1_apply]
    show Res.Sim _ (Run.deleteMem (.loc l) σ)
    simp only [UpdElem.write, Tm.eval, Op3.eval, Op1.eval, Op0.eval, MLoc.eval_lower_addr,
      Run.deleteMem, memClear, Solidity.allocDefault_eq, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
    have ha : NoPanic (l.addr σ) := by
      have h := Tm.eval_noPanic σ l.lower
      rw [MLoc.eval_lower_addr] at h
      exact h
    have hal : NoPanic (Solidity.allocHN σ.glob R) := Solidity.allocHN_noPanic σ.glob R
    revert ha hal
    cases l.addr σ with
    | error e =>
      cases Solidity.allocHN σ.glob R with
      | error e' => exact fun ha hal => ⟨fun h => absurd (congrArg Except.error h) hal,
          fun h => absurd (congrArg Except.error h) ha⟩
      | ok q => intro _ _; exact Res.Sim.refl _
    | ok a =>
      cases Solidity.allocHN σ.glob R with
      | error e' => intro _ _; exact Res.Sim.refl _
      | ok q =>
        intro _ _
        simp only
        cases hw : writeAddr _ _ a with
        | error => exact Res.Sim.refl _
        | ok μ =>
          simp only [writeAddr_ok_with hw]
          exact Res.Sim.refl _

end Updates

end Solidity.Core
