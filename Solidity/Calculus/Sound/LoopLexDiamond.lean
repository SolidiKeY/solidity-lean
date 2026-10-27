import Solidity.Calculus.LexDiamond
import Solidity.Calculus.LexVariantSound
import Solidity.Calculus.SoundArms
import Solidity.Calculus.SoundCalls
import Solidity.Calculus.TermWk

/-!
# The ordinary lexicographic diamond bridge

The typed premise captures every old and new component. Successful bodies
strictly decrease the declared tuple. A body may also exhaust, exactly as
ordinary diamonds permit; this theorem is not a strict SourceCertificate and
does not establish callback-modality soundness.
-/
namespace Solidity.LoopLex

variable {C : Contract} {Γ Γ₁ : Ctx}

private theorem lower_ok {p : PrimTy} (v : Val C Γ p) (σ : State C Γ) {x : p.Denote}
    (h : v.evalT σ = .ok x) : v.lower.eval σ = some x := by
  have hv := Val.lower_evalT σ v
  rw [h] at hv
  exact hv

private theorem lower_error {p : PrimTy} (v : Val C Γ p) (σ : State C Γ) {e : THalt}
    (h : v.evalT σ = .error e) : v.lower.eval σ = none := by
  have he := Val.evalT_revertOnly σ v e h
  subst e
  have hv := Val.lower_evalT σ v
  rw [h] at hv
  exact hv

private theorem anon_head {σ τ : State C Γ} {xs : List ((t : LTy) × Idx Γ t)}
    {hv : Option (List Name)} {μ : Mutability} {W : List (LTy × Nat)}
    (hxs : ∀ t (i : Idx Γ t), (t, i.toNat) ∈ W → (⟨t, i⟩ : (t : LTy) × Idx Γ t) ∈ xs)
    (hg : TGFrame μ σ τ) (ha : TLocAgree 0 W σ.env τ.env) (hk : FrameKeeps hv σ τ)
    {ψ : Fml C Γ} (h : holds σ (Fml.anonHavoc xs hv ψ)) : holds τ ψ := by
  obtain ⟨b, hb⟩ := State.eq_anonHavoc hxs hg ha
  match hv, hk, h with
  | none, _, h => rw [hb]; exact h b τ.storage τ.net τ.selfBalance
  | some [], hk, h =>
    have hst : τ.storage = σ.storage := hk.1.symm
    have hτ : τ = σ.anon xs b := by rw [hb, hst, hk.2.1, hk.2.2]; rfl
    rw [hτ]
    exact h b
  | some (r :: L), hk, h =>
    have h₁ := Modality.forallB_all (h b) τ.storage
    have hτ : τ = (σ.anon xs b).withStorage
        (Storage.anon (r :: L) (σ.anon xs b).storage τ.storage) := by
      have hs : Storage.anon (r :: L) (σ.anon xs b).storage τ.storage = τ.storage := hk.1
      rw [hs, hb, hk.2.1, hk.2.2]
      rfl
    rw [hτ]
    exact Upd.afterT.of_lands h₁ (Upd.lands_anonSt (r :: L) (σ.anon xs b) τ.storage)

/-- A tuple decreases at every successful transition; allowed halts are
terminal outcomes, never an excuse to count an undefined metric as zero. -/
theorem run_lex_or {α : Type} {body : α → TRes α} {c : α → TRes Bool}
    {H G : α → Prop} {X : THalt → Prop} {n : Nat}
    (D : α → TRes (LoopMetrics.NatTuple n))
    (hstep : ∀ τ, H τ → ∃ before, D τ = .ok before ∧
      (c τ = .ok true ∨ c τ = .ok false) ∧
      (c τ = .ok false → G τ) ∧
      (c τ = .ok true → (∃ e, body τ = .error e ∧ X e) ∨
        ∃ next after, body τ = .ok next ∧ H next ∧ D next = .ok after ∧
          LoopMetrics.NatTuple.Lt after before))
    {σ : α} (h0 : H σ) :
    (∃ τ, TLoop.run body c σ = .ok τ ∧ G τ) ∨
      ∃ e, TLoop.run body c σ = .error e ∧ X e := by
  let rank := fun τ => match D τ with
    | .ok values => values
    | .error _ => LoopMetrics.NatTuple.zero n
  have rank_eq : ∀ τ values, D τ = .ok values → rank τ = values := by
    intro τ values h
    dsimp only [rank]
    rw [h]
  let Q := fun r : TRes α => (∃ τ, r = .ok τ ∧ G τ) ∨ ∃ e, r = .error e ∧ X e
  apply TLoop.run_wellFounded (Q := Q) (LoopMetrics.NatTuple.wellFounded n) rank
    (I := H) ?_ ?_ ?_ h0
  · intro τ next hH hs
    obtain ⟨before, hD, hcov, hexit, hbody⟩ := hstep τ hH
    rcases hcov with hc | hc
    · rcases hbody hc with ⟨e, hb, hX⟩ | ⟨next', after, hb, hH', hafter, hdec⟩
      · simp only [TLoop.step, hc, hb, reduceCtorEq] at hs
      · simp only [TLoop.step, hc, hb, Sum.inl.injEq] at hs
        cases hs
        exact hH'
    · simp only [TLoop.step, hc, reduceCtorEq] at hs
  · intro τ next hH hs
    obtain ⟨before, hD, hcov, hexit, hbody⟩ := hstep τ hH
    rcases hcov with hc | hc
    · rcases hbody hc with ⟨e, hb, hX⟩ | ⟨next', after, hb, hH', hafter, hdec⟩
      · simp only [TLoop.step, hc, hb, reduceCtorEq] at hs
      · simp only [TLoop.step, hc, hb, Sum.inl.injEq] at hs
        cases hs
        rw [rank_eq τ before hD, rank_eq next after hafter]
        exact hdec
    · simp only [TLoop.step, hc, reduceCtorEq] at hs
  · intro τ r hH hs
    obtain ⟨before, hD, hcov, hexit, hbody⟩ := hstep τ hH
    rcases hcov with hc | hc
    · rcases hbody hc with ⟨e, hb, hX⟩ | ⟨next, after, hb, hH', hafter, hdec⟩
      · simp only [TLoop.step, hc, hb, Sum.inr.injEq] at hs
        cases hs
        exact .inr ⟨e, rfl, hX⟩
      · simp only [TLoop.step, hc, hb, reduceCtorEq] at hs
    · simp only [TLoop.step, hc, Sum.inr.injEq] at hs
      cases hs
      exact .inl ⟨τ, rfl, hexit hc⟩

private theorem wk_extendEnv {H H' : HTy} (e : H <+: H') {n : Nat}
    (xs : UIntTuple n) (ρ : TEnv C H Γ) :
    TEnv.wk e (SavedCtx n Γ) (extendEnv xs ρ) = extendEnv xs (TEnv.wk e Γ ρ) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (Prod.mk xs.1) (ih xs.2)

private theorem put_extendEnv_any {H : HTy} {n : Nat} (xs : UIntTuple n)
    (ρ ρ' : TEnv C H Γ) :
    TEnv.put (.ofExt (savedExt Γ n)) ρ (extendEnv xs ρ') = extendEnv xs ρ := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (Prod.mk xs.1) (ih xs.2)

private theorem lift_saved_wk {H : HTy} (τ : State C Γ) (e : H <+: τ.H)
    {n : Nat} (xs : UIntTuple n) (ρ : TEnv C H Γ) :
    τ.lift (.ofExt (savedExt Γ n)) (TEnv.wk e _ (extendEnv xs ρ)) = saveState τ xs := by
  unfold State.lift State.withEnv saveState
  rw [wk_extendEnv, put_extendEnv_any]

private theorem invariant_saved (σ : State C Γ) {n : Nat} (xs : UIntTuple n)
    (I : Val C Γ .bool) :
    holds (saveState σ xs) (.isBool (I.wk (.ofExt (savedExt Γ n))).lower true) ↔
      holds σ (.isBool I.lower true) := by
  change (I.wk _).lower.denote _ = _ ↔ _
  rw [Val.lower_wk, Tm.denote_wk]
  have hs : (saveState σ xs).thin (.ofExt (savedExt Γ n)) = σ := by
    unfold State.thin State.withEnv saveState
    rw [TEnv.thin_ofExt, drop_extendEnv]
  rw [hs]
  rfl

private theorem pop_nil_run {H : HTy} {Δ Ε : Ctx} (b : BlockKind)
    (X : TRes (Out C H Δ)) (h : Ext Ε Δ) :
    (X.map (·.st)).bind (Frames.runSt · (.pop b h .nil)) =
      (X.map (Out.drop h)).map (·.st) := by
  cases X <;> rfl

/-- The prospective ordinary diamond premise is sound for the exact source
tuple. Every successful body must decrease, including its final turn; an
exhausted body remains an allowed ordinary-diamond terminal outcome. -/
theorem diamondPremise_sound (k : Nat) (I c : Val C Γ .bool) {n : Nat}
    (metrics : LoopMetrics C Γ (n + 2)) (body : Prog C Γ Γ₁)
    {xs : List ((t : LTy) × Idx Γ t)} {hv : Option (List Name)}
    (hf : body.frame = some (xs, hv)) (σ : State C Γ) :
    Premise.Runs .diamond (.loop (.invLex I metrics false []) c body)
      (diamondPremise k I c metrics body xs hv) σ := by
  intro _ _ ω κ φ hp
  obtain ⟨hI0, hA⟩ := hp
  obtain ⟨μ, hwμ⟩ := Prog.frame_within hf
  have hxs := (Prog.frame_some hf).2
  rw [holds_modal_iff, runSt_cons_frames]
  show Modality.afterRunTR .diamond _
    (((TLoop.run
      (fun o : Out C σ.H Γ => (Prog.run o.st body).map
        fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
      (fun o => c.evalT o.st) ⟨σ, List.prefix_refl _⟩).map (·.st)).bind
      fun τ => (Prog.runSt τ ω).bind (Frames.runSt · κ))
  suffices key : (∃ τ, TLoop.run
      (fun o : Out C σ.H Γ => (Prog.run o.st body).map
        fun o' => (⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩ : Out C σ.H Γ))
      (fun o => c.evalT o.st) ⟨σ, List.prefix_refl _⟩ = .ok τ ∧
        holds τ.st (Fml.modalK .diamond ω κ φ)) ∨ ∃ e, TLoop.run
      (fun o : Out C σ.H Γ => (Prog.run o.st body).map
        fun o' => (⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩ : Out C σ.H Γ))
      (fun o => c.evalT o.st) ⟨σ, List.prefix_refl _⟩ = .error e ∧ e = .exhausted by
    rcases key with ⟨τ, hrun, hG⟩ | ⟨e, hrun, rfl⟩
    · rw [hrun]
      exact (holds_modal_iff τ.st ω κ φ).1 (holds_modalK τ.st ω κ φ hG)
    · rw [hrun]
      exact ⟨rfl, nofun⟩
  refine run_lex_or (X := fun e => e = .exhausted)
    (H := fun a : Out C σ.H Γ => TGFrame μ σ a.st ∧ FrameKeeps hv σ a.st ∧
      TLocAgree 0 (Prog.writesAt 0 body) σ.env a.st.env ∧ holds a.st (.isBool I.lower true))
    (fun a => LoopMetrics.eval a.st metrics) ?_
    ⟨TGFrame.refl σ, FrameKeeps.refl _ σ, TLocAgree.refl _, hI0⟩
  rintro a ⟨hg, hk, hag, hI⟩
  have hY := anon_head hxs hg hag hk hA hI
  have hfree : ((snapshot k metrics).decl (fse (k + (n + 2))) (.val c.lower)).pushFree = true := by
    simp only [Upd.pushFree, snapshot_pushFree, Rhs.pushFree, Val.lower_pushFree, Bool.and_self]
  have hglob : ((snapshot k metrics).decl (fse (k + (n + 2))) (.val c.lower)).globT a.st =
      ((readMetrics a.st metrics).map (fun _ => a.st.globG)).bind
        fun g => (c.lower.eval a.st).bind fun _ => some g := by
    change ((snapshot k metrics).globT a.st).bind _ = _
    rw [snapshot_globT]
    rfl
  cases hd : readMetrics a.st metrics with
  | none =>
    rw [hd] at hglob
    exact (hY.of_noExh hglob (Upd.exh_of_pushFree hfree)).elim
  | some before =>
  cases hc : c.evalT a.st with
  | error e =>
    rw [lower_error c a.st hc] at hglob
    have hfail : ((snapshot k metrics).decl (fse (k + (n + 2))) (.val c.lower)).globT a.st = none := by
      rw [hglob, hd]
      rfl
    exact (hY.of_noExh hfail (Upd.exh_of_pushFree hfree)).elim
  | ok cv =>
  have hcl : (Rhs.val c.lower).eval a.st =
      some (LTy.VDen.ofT (H := a.st.H) (.val .bool) cv) := lower_ok c a.st hc
  obtain ⟨hT, hF⟩ := hY.of_lands
    (Upd.lands_decl (snapshot_lands a.st k metrics before hd) (fse (k + (n + 2))) hcl)
  refine ⟨before.toNat, eval_of_readMetrics a.st metrics before hd, ?_, fun hc' => ?_, fun hc' => ?_⟩
  · cases cv
    · exact .inr rfl
    · exact .inl rfl
  · have hcv : cv = false := Except.ok.inj hc'
    subst hcv
    have hG := Upd.afterT.of_lands (hF ((holds_eq_pvV_lit _ _ _).2 rfl))
      (Upd.lands_pop_nil _ _)
    change holds ((saveState a.st before).drop (savedExt Γ (n + 2))) _ at hG
    rw [saveState_drop] at hG
    exact hG
  · have hcv : cv = true := Except.ok.inj hc'
    subst hcv
    have hT' : holds (saveState a.st before) _ :=
      Upd.afterT.of_lands (hT ((holds_eq_pvV_lit _ _ _).2 rfl)) (Upd.lands_pop_nil _ _)
    have h' := (holds_modal_iff _ _ _ _).1 (holds_modalK _ _ _ _ hT')
    unfold Prog.runSt at h'
    rw [pop_nil_run, ← saveState_eq_lift,
      (TWkRel.drop (Prog.wk_over body (.ofExt (savedExt Γ (n + 2))))
        (Prog.run_wk body (.ofExt (savedExt Γ (n + 2))) a.st
          (extendEnv before a.st.env))).eq_lifted] at h'
    cases hb : Prog.run a.st body with
    | error e =>
      rw [hb] at h'
      exact .inl ⟨e, rfl, h'.1⟩
    | ok o =>
      rw [hb] at h'
      obtain ⟨hg', ha'⟩ := Prog.run_frame body hwμ 0 hb
      have hpost := h'.1
      have hstate := lift_saved_wk (o.st.drop body.ext) o.ext before a.st.env
      change holds ((o.st.drop body.ext).lift (.ofExt (savedExt Γ (n + 2)))
        (TEnv.wk o.ext _ (extendEnv before a.st.env))) (diamondPost k I metrics) at hpost
      rw [hstate] at hpost
      obtain ⟨hI₁, hdec⟩ := hpost
      let τ : State C Γ := o.st.drop body.ext
      have hIτ : holds τ (.isBool I.lower true) := (invariant_saved τ before I).1 hI₁
      have hgτ : TGFrame μ σ τ := hg.trans (hg'.withEnv _)
      have hkτ : FrameKeeps hv σ τ := hk.trans (Prog.frame_keeps hf hb)
      have hagτ : TLocAgree 0 (Prog.writesAt 0 body) σ.env τ.env := hag.trans ha'
      cases ha : readMetrics (saveState τ before) (metrics.wk (.ofExt (savedExt Γ (n + 2)))) with
      | none =>
        have hfail := snapshot_globT (saveState τ before) (k + (n + 2) + 1)
          (metrics.wk (.ofExt (savedExt Γ (n + 2))))
        rw [ha] at hfail
        exact (hdec.of_noExh hfail (snapshot_exh _ _ _)).elim
      | some after =>
        have hdecrease := hdec.of_lands (snapshot_lands (saveState τ before)
          (k + (n + 2) + 1) _ after ha)
        have hlt := (snapshotsDecrease_holds τ before after).1 hdecrease
        have heval := eval_of_readMetrics (saveState τ before) _ after ha
        rw [metrics_eval_saved] at heval
        exact .inr ⟨⟨τ, a.ext.trans o.ext⟩, after.toNat, rfl,
          ⟨hgτ, hkτ, hagτ, hIτ⟩, heval, hlt⟩

/-- Integration boundary for the conservative dispatch. Unsupported annotations
and missing frames remain `false`; this is solely the ordinary modality. -/
theorem diamondStep_sound (k : Nat) (I c : Val C Γ .bool) {n : Nat}
    (metrics : LoopMetrics C Γ (n + 2)) (brk : Bool) (qs : List (LoopQ C Γ))
    (body : Prog C Γ Γ₁) (σ : State C Γ) :
    Premise.Runs .diamond (.loop (.invLex I metrics brk qs) c body)
      (diamondStep k I c metrics brk qs body body.frame) σ := by
  cases brk with
  | true => exact Premise.sound_done σ false nofun
  | false =>
    cases qs with
    | cons q qs => exact Premise.sound_done σ false nofun
    | nil =>
      cases hf : body.frame with
      | none =>
        unfold diamondStep
        exact Premise.sound_done σ false nofun
      | some frame =>
        obtain ⟨xs, hv⟩ := frame
        unfold diamondStep
        exact diamondPremise_sound k I c metrics body hf σ

/-- info: 'Solidity.LoopLex.diamondPremise_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms diamondPremise_sound
/-- info: 'Solidity.LoopLex.diamondStep_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms diamondStep_sound

end Solidity.LoopLex
