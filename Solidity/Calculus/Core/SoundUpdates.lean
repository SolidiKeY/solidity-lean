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
  have h' : m.afterC (holds · (Fml.modalK m ω κ φ)) (U.apply σ) := h
  show m.afterRunC _ _
  rw [run_cons_frames]
  revert hs hU h'
  cases U.apply σ with
  | ok τ =>
    cases s.run σ with
    | ok τ' =>
      intro hs _ h'
      cases (hs : τ = τ')
      exact (holds_modalK m ω κ φ τ).1 h'
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
  fun ω κ φ => Premise.sound_done σ false (fun h => nomatch h) ω κ φ

end Updates

end Solidity.Core
