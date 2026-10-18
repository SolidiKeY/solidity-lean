import Solidity.Calculus.SoundArms

/-!
# Exact update readings of ordinary statement runs

Agreement with an optional update is directional for divergence and
exhaustion. An ending run and a non-exhausted update remove precisely those
exceptions. A successful actual run supplies its own landing witness,
including any typed memory locals; no arbitrary identity is materialized.
-/

namespace Solidity

variable {C : Contract}

theorem Modality.afterRunTR_bind_iff {α β : Type} (m : Modality) (P : β → Prop)
    (r : TRes α) (f : α → TRes β) :
    m.afterRunTR P (r.bind f) ↔ m.afterRunTR (fun a => m.afterRunTR P (f a)) r := by
  cases r with
  | error e =>
    change (m.onTHalt e ∧ (Except.error e : TRes β) ≠ .error .panic) ↔
      m.onTHalt e ∧ (Except.error e : TRes α) ≠ .error .panic
    exact and_congr Iff.rfl (not_congr
      ⟨fun h => congrArg (fun e => (Except.error e : TRes α)) (Except.error.inj h),
        fun h => congrArg (fun e => (Except.error e : TRes β)) (Except.error.inj h)⟩)
  | ok _ => exact ⟨fun h => ⟨h, nofun⟩, And.left⟩

theorem Modality.afterRunTR_congr_iff {α : Type} (m : Modality) (P Q : α → Prop) (r : TRes α)
    (h : ∀ a, P a ↔ Q a) : m.afterRunTR P r ↔ m.afterRunTR Q r := by
  cases r with
  | error _ => rfl
  | ok a => exact and_congr (h a) Iff.rfl

theorem holds_modal_cons_iff {Γ Δ Γ₁ Γ₀ : Ctx} (σ : State C Γ) (m : Modality)
    (s : Stmt C Γ Δ) (ω : Prog C Δ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ (.modal m (.cons s ω) κ φ) ↔
      m.afterRunTR (fun τ => holds τ (.modal m ω κ φ)) (Stmt.runSt σ s) := by
  rw [holds_modal_iff, runSt_cons_frames, Modality.afterRunTR_bind_iff]
  exact Modality.afterRunTR_congr_iff m _ _ _ (fun τ => (holds_modal_iff τ ω κ φ).symm)

theorem Upd.afterT_lands_iff {Γ Δ : Ctx} {U : Upd C Γ Δ} {σ : State C Γ}
    {g : GlobT C σ.H} {τ : State C Δ} (hl : U.Lands σ g τ) (m : Modality)
    (P : State C Δ → Prop) : U.afterT m σ P ↔ P τ := by
  constructor
  · intro h
    exact h.of_lands hl
  · intro h
    refine Upd.afterT_intro (fun hn => ?_) (fun _ τ' hl' => ?_)
    · rw [hl.1] at hn
      cases hn
    · rw [Upd.Lands.eq hl' hl]
      exact h

theorem Upd.afterT_run_iff {Γ Δ : Ctx} (σ : State C Γ) (s : Stmt C Γ Δ) (U : Upd C Γ Δ)
    (ha : TRes.AgreesO (fun o : Out C σ.H Δ => (o.st.glob, o.st.locV)) (s.run σ) (U.applyP σ))
    (he : (s.run σ).Ends) (hx : U.exh σ = false) (m : Modality) (P : State C Δ → Prop) :
    U.afterT m σ P ↔ m.afterRunTR P (Stmt.runSt σ s) := by
  cases hs : s.run σ with
  | ok o =>
    rw [hs] at ha
    obtain ⟨g, hl⟩ := Upd.lands_of_applyP ha
    rw [Upd.afterT_lands_iff hl]
    simp only [Stmt.runSt, hs, Except.map, Modality.afterRunTR]
    exact ⟨fun h => ⟨h, nofun⟩, And.left⟩
  | error e =>
    rw [hs] at ha he
    cases e with
    | panic => cases ha
    | diverge => exact (he.1 rfl).elim
    | exhausted => exact (he.2 rfl).elim
    | revert =>
      have hu : U.applyV σ = none := Option.map_eq_none_iff.1 ha
      rw [Upd.afterT_applyV, hu]
      have hn : (Except.error THalt.revert : TRes (State C Δ)) ≠ .error .panic := by
        intro h
        cases h
      change _ ↔ m.afterRunTR P ((s.run σ).map (·.st))
      rw [hs]
      change (m.onHalt ∨ U.exh σ = true) ↔ m.onTHalt .revert ∧
        (Except.error THalt.revert : TRes (State C Δ)) ≠ .error .panic
      simp only [hx, Bool.false_eq_true, or_false]
      cases m with
      | box => exact ⟨fun _ => ⟨trivial, hn⟩, fun _ => trivial⟩
      | diamond => exact ⟨False.elim, fun h => THalt.noConfusion h.1⟩

structure ExactStatement {Γ Δ : Ctx} (s : Stmt C Γ Δ) where
  update : Upd C Γ Δ
  agree : ∀ σ : State C Γ,
    TRes.AgreesO (fun o : Out C σ.H Δ => (o.st.glob, o.st.locV)) (s.run σ) (update.applyP σ)
  ends : ∀ σ : State C Γ, (s.run σ).Ends
  pushFree : update.pushFree = true

namespace ExactStatement

theorem equivalent {Γ Δ Γ₁ Γ₀ : Ctx} {s : Stmt C Γ Δ} (r : ExactStatement s)
    (σ : State C Γ) (m : Modality) (ω : Prog C Δ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ (.upd m r.update (.modal m ω κ φ)) ↔ holds σ (.modal m (.cons s ω) κ φ) :=
  (Upd.afterT_run_iff σ s r.update (r.agree σ) (r.ends σ) (Upd.exh_of_pushFree r.pushFree) m _).trans
    (holds_modal_cons_iff σ m s ω κ φ).symm

def assignLocal {Γ : Ctx} {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    ExactStatement (.assignLocal (C := C) i v) :=
  ⟨Upd.nil.snoc (UpdElem.setLocal i v), fun σ => setLocal_agrees σ i v,
    fun σ => (Val.evalT_ends σ v).bind (fun _ => TRes.Ends.ok _), by
      simp only [Upd.pushFree, UpdElem.setLocal, UpdElem.pushFree, Rhs.pushFree,
        Val.lower_pushFree, Bool.and_self]⟩

def assign {Γ : Ctx} {T : Ty} (l : Loc C Γ T) (v : Src C Γ T) : ExactStatement (.assign l v) :=
  ⟨Upd.nil.snoc (UpdElem.save l v), fun σ => save_agrees σ l v,
    fun σ => (Src.valueT_ends σ v).bind (fun _ => (Loc.resolveT_ends σ l).bind
      (fun _ => (TRes.Ends.ofOpt _).bind (fun _ => TRes.Ends.ok _))), by
      simp only [Upd.pushFree, UpdElem.save, UpdElem.pushFree, Tm.pushFree, Op3.pushFree,
        Loc.lower_pushFree, Src.lower_pushFree, Bool.and_self]⟩

def delete {Γ : Ctx} {T : Ty} (l : Loc C Γ T) : ExactStatement (.delete l) :=
  ⟨Upd.nil.snoc (UpdElem.delAt l), fun σ => delAt_agrees σ l,
    fun σ => (Loc.resolveT_ends σ l).bind (fun _ => (TRes.Ends.ofOpt _).bind
      (fun _ => TRes.Ends.ok _)), by
      simp only [Upd.pushFree, UpdElem.delAt, UpdElem.pushFree, Tm.pushFree, Op2.pushFree,
        Loc.lower_pushFree, Bool.and_self]⟩

theorem declLocal_agree {Γ : Ctx} (σ : State C Γ) (p : PrimTy) (x : Var) (v : Val C Γ p) :
    TRes.AgreesO (fun o : Out C σ.H (.val p :: Γ) => (o.st.glob, o.st.locV))
      (TRun.declLocal p (some v) σ) ((Upd.nil.decl x (.val v.lower)).applyP σ) := by
  rw [applyP_decl1]
  change TRes.AgreesO (fun o : Out C σ.H (.val p :: Γ) => (o.st.glob, o.st.locV))
    ((v.evalT σ).bind fun value => .ok ⟨σ.push (t := .val p) value, List.prefix_refl _⟩)
    ((v.lower.eval σ).map fun value => (σ.glob, σ.locV.push (t := .val p) value))
  refine (Val.lower_evalT σ v).cases (fun value hv => ?_) (fun hv => by rw [hv]; rfl)
  refine TRes.AgreesO.ret ?_
  rw [hv, State.locV_push]
  rfl

def declLocal {Γ : Ctx} (p : PrimTy) (x : Var) (v : Option (Val C Γ p)) :
    ExactStatement (.declLocal (C := C) p x v) :=
  match v with
  | none =>
    ⟨Upd.nil.decl x (.val (.app0 (.lit (PrimTy.dflt p)))),
      fun σ => TRes.AgreesO.ret (by rw [applyP_decl1, State.locV_push]; rfl),
      fun _ => TRes.Ends.ok _, rfl⟩
  | some v =>
    ⟨Upd.nil.decl x (.val v.lower), fun σ => declLocal_agree σ p x v,
      fun σ => (Val.evalT_ends σ v).bind (fun _ => TRes.Ends.ok _), by
        simp only [Upd.pushFree, Rhs.pushFree, Val.lower_pushFree, Bool.and_self]⟩

def ofStatement? : {Γ Δ : Ctx} → (s : Stmt C Γ Δ) → Option (ExactStatement s)
  | _, _, .assignLocal i v => some (assignLocal i v)
  | _, _, .assign l v => some (assign l v)
  | _, _, .delete l => some (delete l)
  | _, _, .declLocal p x v => some (declLocal p x v)
  | _, _, _ => none

end ExactStatement

end Solidity
