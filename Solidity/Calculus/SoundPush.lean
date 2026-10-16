import Solidity.Calculus.SoundCapture

/-!
# The two updates of primitive push suffixes

`sp.push() += se` first resets and appends a slot, then reads and modifies
that slot in the storage left by the first update. The agreement below is
against the actual typed run, on every typed state, including a recycled
primitive slot. It covers ordinary failure in either stage and preserves
the interpreter's exhaustion boundary. `++sp.push()` and `sp.push()++`
share the same state update when their expression value is discarded.

These agreements establish the sequential update case. Division and
remainder additionally need SolKey's outer zero-divisor branch when their
native taclets are registered.
-/

namespace Solidity.PushSuffix

variable {C : Contract} {Γ : Ctx}

/-- After `sp.push()`, the appended index is in bounds in the new storage. -/
theorem pushPlace_at {E : Ty} {st st' : Storage C}
    {r : SRef C (.ref (.array E))} {k : PrimTy.uint.Denote}
    (h : st.pushPlace r = some (st', k)) :
    st'.atT (.arr .dyn) r k = some (r.index (.arr .dyn) k) := by
  obtain ⟨n, e, sh, hn, hcap, rfl, hf⟩ := Storage.pushPlace_shape h
  simp only [Storage.atT, Storage.checkIndex, hf, Option.bind_eq_bind, Option.bind_some,
    Storage.inBounds, SVal.view_array, lenU, Int.toNat_natCast, List.length_append,
    List.length_singleton, SVec.length_toList, Nat.lt_add_one, if_true]

/-- The simple source `se` of `sp.push() += se` is stable across the append. -/
theorem simple_stable {p : PrimTy} (s : Simple C Γ p) (σ : State C Γ) (st : Storage C) :
    s.evalT (σ.withStorage st) = s.evalT σ := by
  cases s <;> rfl

/-- The simple receiver `sp` of `sp.push() += se` is stable across the append. -/
theorem receiver_stable {T : Ty} (b : SPath C Γ T) (hs : b.isSimple = true)
    (σ : State C Γ) (st : Storage C) : b.lower.eval (σ.withStorage st) = b.lower.eval σ := by
  cases b with
  | alias i => rfl
  | loc l => cases l <;> first | rfl | cases hs

/-- After `sp.push()`, subtracting one from the new length gives the appended index. -/
theorem sub_one (l k : PrimTy.uint.Denote) (h : l.1 = k.1 + 1) :
    binopT .sub rfl l (some ⟨1, rfl⟩) = some k := by
  change PrimTy.uint.ofInt? (l.1 - 1) = some k
  have he : l.1 - 1 = k.1 := by omega
  rw [he]
  simp only [PrimTy.ofInt?, dif_pos k.2]
  rfl

/-- The length term in `sp.push() += se` reads the current typed storage. -/
theorem eval_len (σ : State C Γ) {E : Ty} (b : Tm C Γ (.path (.array E))) :
    (Tm.app2 .len (.app0 .storage) b).eval σ = (b.eval σ).bind σ.storage.len := rfl

/-- The second update of `sp.push() += se` reads the index just appended. -/
theorem lastIndex_eval {E : Ty} (b : SPath C Γ (.array E)) (hs : b.isSimple = true)
    (σ : State C Γ) {r : SRef C (.ref (.array E))} {st' : Storage C} {k : PrimTy.uint.Denote}
    (hb : b.lower.eval σ = some r) (h : σ.storage.pushPlace r = some (st', k)) :
    (lastIndex b).eval (σ.withStorage st') = some k := by
  obtain ⟨l, hl, he⟩ := Storage.pushPlace_len h
  rw [lastIndex, Tm.eval_binop, eval_len,
    receiver_stable b hs σ st', hb, Option.bind_some]
  simp only [State.withStorage, hl, Tm.eval_lit, Option.bind_some]
  exact sub_one l k he

/-- The second update of `sp.push() += se` addresses the slot just appended. -/
theorem lastPath_eval {p : PrimTy} (b : SPath C Γ (.array (.prim p)))
    (hs : b.isSimple = true) (σ : State C Γ) {r : SRef C (.ref (.array (.prim p)))}
    {st' : Storage C} {k : PrimTy.uint.Denote} (hb : b.lower.eval σ = some r)
    (h : σ.storage.pushPlace r = some (st', k)) :
    (lastPath b).eval (σ.withStorage st') = some (r.index (.arr .dyn) k) := by
  rw [lastPath, Tm.eval_app2, Op2.eval_eq_evalM]
  show ((b.lower.eval (σ.withStorage st')).bind fun ref =>
    ((lastIndex b).eval (σ.withStorage st')).bind fun index => st'.atT (.arr .dyn) ref index) = _
  rw [receiver_stable b hs σ st', hb, lastIndex_eval b hs σ hb h, Option.bind_some,
    Option.bind_some]
  exact pushPlace_at h

/-- The save in `sp.push() += se` agrees with the checked arithmetic write. -/
theorem saveOp_agrees {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (b : SPath C Γ (.array (.prim p))) (se : Simple C Γ p)
    (σ : State C Γ) (r : SRef C (.prim p)) (y : p.Denote)
    (hq : (lastPath b).eval σ = some r) (hy : se.lower.eval σ = some y) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV))
      (opStoreT σ op r y) ((saveOp op hop hp b se).applyP σ) := by
  rw [saveOp, applyP_storage1, Tm.eval_save, Tm.eval_storage, Option.bind_some,
    Tm.eval_sval, Tm.eval_compound σ hop hp, hy, Tm.eval_find, Tm.eval_storage,
    Option.bind_some, hq]
  simp only [Option.bind_some, opStoreT]
  cases hf : σ.storage.find r with
  | none => rfl
  | some old =>
    simp only [Option.bind_some, TRes.ofOpt_some_bind]
    cases hc : compoundT op p (PrimTy.key (SVal.view old)) (PrimTy.key y) with
    | none => rfl
    | some value =>
      simp only [Option.map_some, Option.bind_some, TRes.ofOpt_some_bind]
      rw [Storage.write_prim]
      cases σ.storage.save r (.prim value) <;> rfl

/-- After `sp.push()`, its arithmetic save reads the updated storage. -/
theorem saveOp_afterPush {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (b : SPath C Γ (.array (.prim p))) (se : Simple C Γ p)
    (hs : b.isSimple = true) (σ : State C Γ) {r : SRef C (.array (.prim p))}
    {st' : Storage C} {k : PrimTy.uint.Denote} (hb : b.lower.eval σ = some r)
    (h : σ.storage.pushPlace r = some (st', k)) :
    TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV))
      (opStoreT (σ.withStorage st') op (r.index (.arr .dyn) k) (se.evalT σ))
      ((saveOp op hop hp b se).applyP (σ.withStorage st')) := by
  exact saveOp_agrees op hop hp b se (σ.withStorage st') _ _ (lastPath_eval b hs σ hb h)
    (by rw [Simple.lower_evalT, simple_stable])

/-- The first update of `sp.push() += se` lands in the appended typed storage. -/
theorem pushUpdate_applyP {E : Ty} (b : SPath C Γ (.array E)) (σ : State C Γ)
    {r : SRef C (.array E)} {st' : Storage C} {k : PrimTy.uint.Denote}
    (hb : b.lower.eval σ = some r) (h : σ.storage.pushPlace r = some (st', k)) :
    (Upd.nil.snoc (UpdElem.pushSlot b)).applyP σ =
      some ((σ.withStorage st').glob, (σ.withStorage st').locV) := by
  rw [UpdElem.pushSlot, applyP_storage1, Tm.eval_pushSlot, Tm.eval_storage,
    Option.bind_some, hb, Option.bind_some, ← Storage.pushPlace_fst, h]
  rfl

/-- An update stage of `sp.push() += se` that has no typed result has failed. -/
theorem applyV_none_of_applyP_none {Δ : Ctx} (U : Upd C Γ Δ) (σ : State C Γ)
    (h : U.applyP σ = none) : U.applyV σ = none := by
  unfold Upd.applyP at h
  cases he : U.applyV σ with
  | none => rfl
  | some q => rw [he] at h; cases h

/-- When `sp.push()` cannot produce storage, its first update fails too. -/
theorem pushUpdate_none {E : Ty} (b : SPath C Γ (.array E)) (σ : State C Γ)
    {r : SRef C (.array E)} (hb : b.lower.eval σ = some r)
    (h : σ.storage.pushPlace r = none) :
    (Upd.nil.snoc (UpdElem.pushSlot b)).applyV σ = none := by
  apply applyV_none_of_applyP_none
  rw [UpdElem.pushSlot, applyP_storage1, Tm.eval_pushSlot, Tm.eval_storage,
    Option.bind_some, hb, Option.bind_some, ← Storage.pushPlace_fst, h]
  rfl

/-- When `sp.push()` has capacity, its first update is not exhausted. -/
theorem pushUpdate_exh {E : Ty} (b : SPath C Γ (.array E)) (σ : State C Γ)
    {r : SRef C (.array E)} (hb : b.lower.eval σ = some r) (hf : σ.storage.full r = false) :
    (Upd.nil.snoc (UpdElem.pushSlot b)).exh σ = false := by
  refine Upd.exh_of_exhAny ?_
  show (false || (Tm.app2 .pushSlot (.app0 .storage) b.lower).exhB σ) = false
  rw [Tm.exhB_app2_pushFree σ _ _ _ rfl (SPath.lower_pushFree b)]
  show (false || Op2.exhB .pushSlot (some σ.storage) (b.lower.eval σ)) = false
  rw [hb]
  exact hf

/-- The arithmetic save of `sp.push() += se` performs no allocation. -/
theorem saveOp_exh {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (b : SPath C Γ (.array (.prim p))) (se : Simple C Γ p)
    (σ : State C Γ) : (saveOp op hop hp b se).exh σ = false := by
  apply Upd.exh_of_pushFree
  simp only [saveOp, Upd.pushFree, UpdElem.pushFree, Tm.pushFree, Op2.pushFree,
    Op3.pushFree, Tm.castV_pushFree, lastPath, lastIndex,
    SPath.lower_pushFree, Simple.lower_pushFree, Bool.and_true]

/-- The numeric source `1` used by `++sp.push()`. -/
def oneSimple (p : PrimTy) (hp : p.isNumeric = true) : Simple C Γ p :=
  .lit 1 (by cases p <;> first | rfl | exact absurd hp Bool.false_ne_true)

/-- The arithmetic of `++sp.push()` is compound addition of one. -/
theorem bumpT_compoundOne {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
    (σ : State C Γ) (x : Int) :
    bumpT op p x = compoundT op.binOp p x (PrimTy.key ((oneSimple p hp).evalT σ)) := by
  cases p with
  | bool => cases hp
  | uint | int => cases op <;> rfl

/-- Discarding the value of `sp.push()++` leaves compound addition of one. -/
theorem bumpStore_is_compound {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
    (σ : State C Γ) (r : SRef C (.prim p)) :
    (bumpStoreT σ op r).map Prod.fst =
      opStoreT σ op.binOp r ((oneSimple p hp).evalT σ) := by
  simp only [bumpStoreT, opStoreT, TRes.map_bind, bumpT_compoundOne op hp σ]
  rfl

/-- The statement `sp.push()++` has the state result of `sp.push() += 1`. -/
theorem bump_step_eq_compound {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
    (b : SPath C Γ (.array (.prim p))) (σ : State C Γ) :
    TRun.pushIncDec op b σ = TRun.pushOpAssign op.binOp b (.simple (oneSimple p hp)) σ := by
  simp only [TRun.pushIncDec, TRun.pushOpAssign, Val.evalT]
  cases hr : b.resolveT σ with
  | error e => rfl
  | ok r =>
    simp only [bind, Except.bind]
    split
    · rfl
    · cases hplace : σ.storage.pushPlace r with
      | none => rfl
      | some pair =>
        obtain ⟨st', k⟩ := pair
        simp only [TRes.ofOpt]
        exact (bumpStore_is_compound op hp (σ.withStorage st') (r.index (.arr .dyn) k)).trans
          (congrArg (opStoreT (σ.withStorage st') op.binOp (r.index (.arr .dyn) k))
            (simple_stable (oneSimple p hp) σ st'))

/-- On every typed state, the two updates of `sp.push() += se` agree with its run. -/
theorem compound_pair_agrees {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (b : SPath C Γ (.array (.prim p))) (se : Simple C Γ p)
    (hs : b.isSimple = true) (σ : State C Γ) :
    Upd.PairAgrees (Upd.nil.snoc (UpdElem.pushSlot b)) (saveOp op hop hp b se) σ
      (TRun.pushOpAssign op b (.simple se) σ) := by
  cases hr : b.resolveT σ with
  | error e =>
    have he : e = .revert := SPath.resolveT_revert σ b hr
    subst e
    have hpush : TRun.push b none σ = .error .revert := by
      simp only [TRun.push, hr, bind, Except.bind]
    have hu := pushSlot_agrees σ b
    rw [hpush] at hu
    simp only [TRun.pushOpAssign, Val.evalT, hr, bind, Except.bind]
    exact Or.inl ⟨applyV_none_of_applyP_none _ σ hu, pushSlot_exh σ b hpush⟩
  | ok r =>
    have hb : b.lower.eval σ = some r := by
      have h := SPath.lower_resolveT σ b
      rw [hr] at h
      exact h
    cases hf : σ.storage.full r with
    | true =>
      simp only [TRun.pushOpAssign, Val.evalT, hr, hf, if_true, bind, Except.bind]
      trivial
    | false =>
      cases hplace : σ.storage.pushPlace r with
      | none =>
        simp only [TRun.pushOpAssign, Val.evalT, hr, hf, Bool.false_eq_true, if_false, hplace,
          TRes.ofOpt, bind, Except.bind]
        exact Or.inl ⟨pushUpdate_none b σ hb hplace, pushUpdate_exh b σ hb hf⟩
      | some pair =>
        obtain ⟨st', k⟩ := pair
        have hu := pushUpdate_applyP b σ hb hplace
        have hv := saveOp_afterPush op hop hp b se hs σ hb hplace
        cases ht : opStoreT (σ.withStorage st') op (r.index (.arr .dyn) k) (se.evalT σ) with
        | ok o =>
          rw [ht] at hv
          simp only [TRun.pushOpAssign, Val.evalT, hr, hf, Bool.false_eq_true, if_false, hplace,
            TRes.ofOpt, bind, Except.bind, ht]
          exact ⟨σ.withStorage st', hu, hv⟩
        | error e =>
          cases e with
          | revert =>
            rw [ht] at hv
            simp only [TRun.pushOpAssign, Val.evalT, hr, hf, Bool.false_eq_true, if_false, hplace,
              TRes.ofOpt, bind, Except.bind, ht]
            exact Or.inr ⟨σ.withStorage st', hu, applyV_none_of_applyP_none _ _ hv,
              saveOp_exh op hop hp b se _⟩
          | panic => rw [ht] at hv; exact hv.elim
          | diverge => exact ((opStoreT_ends _ op _ _).1 ht).elim
          | exhausted => exact ((opStoreT_ends _ op _ _).2 ht).elim

/-- On every typed state, the two updates of `++sp.push();` agree with its run. -/
theorem bump_pair_agrees {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
    (b : SPath C Γ (.array (.prim p))) (hs : b.isSimple = true) (σ : State C Γ) :
    Upd.PairAgrees (Upd.nil.snoc (UpdElem.pushSlot b))
      (saveOp op.binOp op.binOp_compound hp b (oneSimple p hp)) σ
      (TRun.pushIncDec op b σ) := by
  rw [bump_step_eq_compound op hp b σ]
  exact compound_pair_agrees op.binOp op.binOp_compound hp b (oneSimple p hp) hs σ


/-- The successive updates of `sp.push() += se` agree with both modalities
on every typed state; `sp` is simple so the receiver remains stable. -/
theorem sound_pushOp {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (b : SPath C Γ (.array (.prim p))) (se : Simple C Γ p)
    (hs : b.isSimple = true) (σ : State C Γ) {m : Modality} :
    Premise.Runs m (.pushOpAssign op hop hp b (.simple se))
      (.updates (Upd.nil.snoc (UpdElem.pushSlot b)) (saveOp op hop hp b se)) σ :=
  Premise.updatesRuns_of_agrees σ (compound_pair_agrees op hop hp b se hs σ)

/-- The successive updates of `++sp.push();` and `sp.push()++;` agree with
both modalities. Only their state result is observed by a statement. -/
theorem sound_pushInc {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
    (b : SPath C Γ (.array (.prim p))) (hs : b.isSimple = true) (σ : State C Γ)
    {m : Modality} :
    Premise.Runs m (.pushIncDec op hp b)
      (.updates (Upd.nil.snoc (UpdElem.pushSlot b))
        (saveOp op.binOp op.binOp_compound hp b (oneSimple p hp))) σ :=
  Premise.updatesRuns_of_agrees σ (bump_pair_agrees op hp b hs σ)

/-- Capturing the receiver or source of `b.push() += rhs` preserves the
run once the fresh local is dropped. -/
theorem pushOpAssign_pushT {p : PrimTy} {t : LTy} (σ : State C Γ)
    (w : t.TDenote C σ.H) (op : BinOp)
    (b' : SPath C (t :: Γ) (.array (.prim p))) (b : SPath C Γ (.array (.prim p)))
    (r' : Val C (t :: Γ) p) (r : Val C Γ p)
    (hb : b'.resolveT (σ.push w) = b.resolveT σ)
    (hr : r'.evalT (σ.push w) = r.evalT σ) :
    TRun.pushOpAssign op b' r' (σ.push w) = pushedT σ w (TRun.pushOpAssign op b r σ) := by
  change TRun.pushOpAssign op b' r' (σ.lift up (w, σ.env)) = _
  change b'.resolveT (σ.lift up (w, σ.env)) = b.resolveT σ at hb
  change r'.evalT (σ.lift up (w, σ.env)) = r.evalT σ at hr
  simp only [TRun.pushOpAssign, hr, hb, liftedT_bind, liftedT_ite, liftedT_error,
    State.lift_storage, State.lift_withStorage, opStoreT_lift]

/-- `b.push() += rhs` captures `rhs` before the receiver is evaluated. -/
theorem sound_pushOpCapture {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (b : SPath C Γ (.array (.prim p))) (r : Val C Γ p)
    (x : Var) (σ : State C Γ) {m : Modality} :
    Premise.Runs m (.pushOpAssign op hop hp b r)
      (.capture p x r (.pushOpAssign op hop hp b.up (.simple (.local .here)))) σ := by
  refine Premise.sound_captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · exact runSt_pushed σ (t := .val p) v (pushOpAssign_pushT (t := .val p) σ v op b.up b (.simple (.local .here)) r
      (SPath.resolveT_up (t := .val p) σ v b) (by rw [hv]; rfl))
  · refine TRes.Sim.err_refl ?_
    show (TRun.pushOpAssign op b r σ).map _ = _
    simp only [TRun.pushOpAssign, hh]; rfl

/-- After its simple source, `b.push() += se` captures a complex receiver
once, before appending or reading the new slot. -/
theorem sound_pushOpRecv {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (b : SPath C Γ (.array (.prim p))) (se : Simple C Γ p)
    (x : Var) (σ : State C Γ) {m : Modality} :
    Premise.Runs m (.pushOpAssign op hop hp b (.simple se))
      (.captureSP x b (.pushOpAssign op hop hp (.alias .here) (.simple se.up))) σ := by
  refine Premise.sound_captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · exact runSt_pushed σ (t := .alias _) (some q)
      (pushOpAssign_pushT (t := .alias _) σ (some q) op (.alias .here) b (.simple se.up) (.simple se)
        (by rw [hq]; rfl) (by simp only [Val.evalT, Simple.evalT_up]))
  · refine TRes.Sim.err_refl ?_
    show (TRun.pushOpAssign op b (.simple se) σ).map _ = _
    simp only [TRun.pushOpAssign, Val.evalT, hh]; rfl

/-- Capturing a receiver of `++b.push();` preserves its state result. -/
theorem pushIncDec_pushT {p : PrimTy} {t : LTy} (σ : State C Γ)
    (w : t.TDenote C σ.H) (op : IncDec) (hp : p.isNumeric = true)
    (b' : SPath C (t :: Γ) (.array (.prim p))) (b : SPath C Γ (.array (.prim p)))
    (hb : b'.resolveT (σ.push w) = b.resolveT σ) :
    TRun.pushIncDec op b' (σ.push w) = pushedT σ w (TRun.pushIncDec op b σ) := by
  simp only [bump_step_eq_compound op hp]
  exact pushOpAssign_pushT σ w op.binOp b' b (.simple (oneSimple p hp))
    (.simple (oneSimple p hp)) hb (by cases p <;> first | rfl | cases hp)

/-- `++b.push();` captures a complex receiver once, before appending. -/
theorem sound_pushIncRecv {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
    (b : SPath C Γ (.array (.prim p))) (x : Var) (σ : State C Γ) {m : Modality} :
    Premise.Runs m (.pushIncDec op hp b)
      (.captureSP x b (.pushIncDec op hp (.alias .here))) σ := by
  refine Premise.sound_captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · exact runSt_pushed σ (t := .alias _) (some q)
      (pushIncDec_pushT (t := .alias _) σ (some q) op hp (.alias .here) b (by rw [hq]; rfl))
  · refine TRes.Sim.err_refl ?_
    show (TRun.pushIncDec op b σ).map _ = _
    simp only [TRun.pushIncDec, hh]; rfl

/-- The outer guard of `sp.push() /= se` holds exactly when its simple
source is nonzero at its Solidity type. -/
theorem holds_nonzero {p : PrimTy} (hp : p.isNumeric = true) (se : Simple C Γ p)
    (σ : State C Γ) : holds σ (nonzero hp se) ↔ se.evalT σ ≠ PrimTy.dflt p := by
  change ¬ (se.lower.denote σ = (Tm.zero p hp).denote σ) ↔ _
  rw [Simple.denote_lowerT]
  have hz : (Tm.zero p hp).denote σ = some (PrimTy.dflt p) := by
    have he : (Tm.zero p hp).eval σ = some (PrimTy.dflt p) := by
      cases p <;> first | rfl | cases hp
    exact Tm.denote_eval σ (Tm.zero p hp) _ he
  rw [hz, Option.some.injEq]

/-- A zero divisor in `sp.push() /= se` makes the checked arithmetic fail. -/
theorem compound_zero (op : BinOp) (hg : needsZeroGuard op = true) (p : PrimTy) (x : Int) :
    compoundT op p x 0 = none := by
  cases op <;> first | rfl | cases hg

/-- The arithmetic save of `sp.push() /= 0` reverts for every typed slot. -/
theorem opStore_zero {p : PrimTy} (op : BinOp) (hg : needsZeroGuard op = true)
    (σ : State C Γ) (r : SRef C (.prim p)) (v : p.Denote) (hv : PrimTy.key v = 0) :
    opStoreT σ op r v = .error .revert := by
  simp only [opStoreT]
  cases hf : σ.storage.find r with
  | none => rfl
  | some old =>
    simp only [TRes.ofOpt_some_bind, hv, compound_zero op hg, TRes.ofOpt_none_bind]

/-- Where `se` is zero, `sp.push() /= se` cannot succeed or panic. Capacity
exhaustion may precede arithmetic, as in the existing interpreter. -/
theorem pushOp_zero_sim {p : PrimTy} (op : BinOp) (hg : needsZeroGuard op = true)
    (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (b : SPath C Γ (.array (.prim p))) (se : Simple C Γ p) (σ : State C Γ)
    (hc : ¬ holds σ (nonzero hp se)) :
    TRes.Sim (.error .revert)
      (Stmt.runSt σ (.pushOpAssign op hop hp b (.simple se))) := by
  rw [holds_nonzero] at hc
  have hz : se.evalT σ = PrimTy.dflt p := Classical.not_not.mp hc
  have hk : PrimTy.key (se.evalT σ) = 0 := by
    rw [hz]
    cases p <;> first | rfl | cases hp
  change TRes.Sim (.error .revert) ((TRun.pushOpAssign op b (.simple se) σ).map (·.st))
  cases hr : b.resolveT σ with
  | error e =>
    have he : e = .revert := SPath.resolveT_revert σ b hr
    subst e
    simp only [TRun.pushOpAssign, Val.evalT, hr, ok_bind, error_bind]
    exact TRes.Sim.refl _
  | ok r =>
    cases hf : σ.storage.full r with
    | true =>
      simp only [TRun.pushOpAssign, Val.evalT, hr, hf, if_true, ok_bind]
      exact ⟨⟨nofun, nofun⟩, nofun⟩
    | false =>
      cases hp' : σ.storage.pushPlace r with
      | none =>
        simp only [TRun.pushOpAssign, Val.evalT, hr, hf, Bool.false_eq_true, if_false,
          hp', TRes.ofOpt_none_bind, ok_bind]
        exact TRes.Sim.refl _
      | some pair =>
        obtain ⟨st', k⟩ := pair
        simp only [TRun.pushOpAssign, Val.evalT, hr, hf, Bool.false_eq_true, if_false,
          hp', TRes.ofOpt_some_bind, ok_bind, opStore_zero op hg _ _ _ hk]
        exact TRes.Sim.refl _

/-- The guarded replacement of `sp.push() /= se` and `%= se` preserves
both modalities with the condition outside the append and arithmetic updates. -/
theorem sound_pushOpGuarded {p : PrimTy} (op : BinOp) (hg : needsZeroGuard op = true)
    (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (b : SPath C Γ (.array (.prim p))) (se : Simple C Γ p) (hs : b.isSimple = true)
    (σ : State C Γ) {m : Modality} :
    Premise.Runs m (.pushOpAssign op hop hp b (.simple se))
      (.guardedUpdates (nonzero hp se) (Upd.nil.snoc (UpdElem.pushSlot b))
        (saveOp op hop hp b se)) σ := by
  exact ⟨rfl, fun _ => sound_pushOp op hop hp b se hs σ,
    pushOp_zero_sim op hg hop hp b se σ⟩

/-- Every arm of `b.push() += rhs` preserves its typed run, including
source-first capture followed by receiver capture. -/
theorem pushOpStep_sound (k : Nat) {p : PrimTy} (op : BinOp)
    (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (b : SPath C Γ (.array (.prim p))) (r : Val C Γ p) (q : Premise C Γ Γ)
    (hs : pushOpStep k op hop hp b r = q) (σ : State C Γ) {m : Modality} :
    Premise.Runs m (.pushOpAssign op hop hp b r) q σ := by
  cases r with
  | simple se =>
    simp only [pushOpStep] at hs
    split at hs
    · rename_i hb
      split at hs
      · rename_i hg
        cases hs
        exact sound_pushOpGuarded op hg hop hp b se hb σ
      · cases hs
        exact sound_pushOp op hop hp b se hb σ
    · cases hs
      exact sound_pushOpRecv op hop hp b se (fsp k) σ
  | _ => cases hs; exact sound_pushOpCapture op hop hp b _ (fse k) σ

/-- Every arm of `++b.push();` or `b.push()++;` preserves its typed run. -/
theorem pushIncStep_sound (k : Nat) {p : PrimTy} (op : IncDec)
    (hp : p.isNumeric = true) (b : SPath C Γ (.array (.prim p)))
    (q : Premise C Γ Γ) (hs : pushIncStep k op hp b = q) (σ : State C Γ) {m : Modality} :
    Premise.Runs m (.pushIncDec op hp b) q σ := by
  simp only [pushIncStep] at hs
  split at hs
  · rename_i hb
    cases hs
    exact sound_pushInc op hp b hb σ
  · cases hs
    exact sound_pushIncRecv op hp b (fsp k) σ

end Solidity.PushSuffix
