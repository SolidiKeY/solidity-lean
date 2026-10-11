import Solidity.Calculus.DecideRel
import Solidity.Calculus.Graft
import Solidity.Calculus.SoundLoops
import Solidity.Calculus.ProvesSound

/-!
# The scoped reduction, sound over the typed state

`Fml.toLS` (`Calculus/DecideScoped.lean`) pushes a scoped leaf's updates in
by position.  Its soundness is proved here on the leaf itself, over the
typed state and its run (`holds`, `Calculus/Logic.lean`), not through the
leaf's erasure (decision 83's rest): `Fml.toLSM_sound` follows the leaf's
binders, updates and connectives as `holds` reads them, and
`Valid.of_reduceS` puts it together with the elimination (`LFml.elim_holds`).

What relates the reduction's state to the scoped state is `RelU σ ρ τ`
(`Calculus/DecideRel.lean`), and what a term or an update pushed in reads
is proved there, on the scoped terms (`RelU.val`, `RelU.one`, `RelU.two`,
`RelU.par`).

The binders: a quantifier is the reduction's `LFml.all` over its key, and
its local the atom `pos k`, which the state read binds at the key
(`RelU.pushQ`); a hidden binder pushes a position bound to nothing
(`RelU.pushFree`).  An equation `eqD a b` is read through the
constructors it is peeled of (`Fml.peelS`): its two readings, the same
term in one context with the same keys (`sameAt`), lower alike.

Polarity: the fragment takes updates, hidden binders and modalities only
in positive positions (`Fml.inLS true`), where the reduction need only
imply the formula; under a negation or on the left of an implication the
formula is first-order and the two agree both ways.

A leaf's premise `wt(storage)` under its parameters' quantifiers is set
aside (`Fml.dropWtS`) and read as the layout its roots hold
(`Fml.layoutS`, `holds_of_dropWtS`; proposal 100).
-/

namespace Solidity

namespace Decide

open Semantics SemanticsProperties

variable {C : Contract}

/-! ## Through the constructors the erasure drops -/

section Peel

variable {σ : Semantics.State}

/-- An update of pops and drops, on a typed state: it ends in the typed
state its pops and drops leave. -/
theorem zero_typed {Γ : Ctx} (aE : ∀ {Δ : Ctx}, UpdElem C Γ Δ → Act)
    (aR : ∀ {t : LTy}, Rhs C Γ t → Act) (τ : State C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → U.view = .zero →
      ∃ τ' : State C Δ, U.apply τ.erase = .ok τ'.erase ∧ τ'.H = τ.H
  | _, .nil, _ => ⟨τ, rfl, rfl⟩
  | _, .snoc U e, hv => absurd hv (UView.add_ne_zero U.view e.toElemS)
  | _, .decl U _ r, hv => absurd hv (UView.add_ne_zero U.view (.rhs r))
  | _, .pop U hx, hv => by
    obtain ⟨τ', hτ, hH⟩ := zero_typed aE aR τ U hv
    exact ⟨τ'.drop hx, by show (U.apply τ.erase).map _ = _; rw [hτ, State.drop_erase]; rfl, hH⟩
  | _, .drop U hx, hv => by
    obtain ⟨τ', hτ, hH⟩ := zero_typed aE aR τ U hv
    exact ⟨τ'.thin hx, by show (U.apply τ.erase).map _ = _; rw [hτ, State.thin_erase]; rfl, hH⟩

/-- **Peeling keeps the relation, the reduction's symbols and its shape.** -/
theorem peel_sym : ∀ {Γ : Ctx} (φ : Fml C Γ) {ρ : SymS} {Γ' : Ctx} {ρ' : SymS} {φ' : Fml C Γ'},
    φ.peelS ρ = ⟨Γ', ρ', φ'⟩ → ρ'.sym = ρ.sym := by
  intro Γ φ
  induction φ with
  | upd m U φ ih =>
    intro ρ Γ' ρ' φ' hp
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    split at hp
    · rw [← Fml.peelS_eq_peelSM] at hp
      have := ih (ρ := U.replayS noActE noActR ρ) hp
      rw [this]
      rename_i hv
      exact replayS_sym_zero noActE noActR ρ U hv
    · cases hp; rfl
  | bind m x t φ ih =>
    intro ρ Γ' ρ' φ' hp
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    rw [← Fml.peelS_eq_peelSM] at hp
    exact ih (ρ := ρ.push .keep) hp
  | _ => intro ρ Γ' ρ' φ' hp; cases hp; rfl

/-- **Peeling, read one way**: a formula holds where what it peels to holds
in every typed state the peeled constructors reach. -/
theorem peel_pos : ∀ {Γ : Ctx} (φ : Fml C Γ) {ρ : SymS} {Γ' : Ctx} {ρ' : SymS} {φ' : Fml C Γ'},
    φ.peelS ρ = ⟨Γ', ρ', φ'⟩ → ∀ τ : State C Γ, RelU σ ρ τ.erase →
      (∀ τ' : State C Γ', RelU σ ρ' τ'.erase → holds τ' φ') → holds τ φ := by
  intro Γ φ
  induction φ with
  | upd m U φ ih =>
    intro ρ Γ' ρ' φ' hp τ h hk
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    split at hp
    · rename_i hv
      rw [← Fml.peelS_eq_peelSM] at hp
      obtain ⟨τe, hτ, h', hs⟩ := RelU.zero noActE noActR h U hv
      show m.afterC (fun τ' => ∀ σ' : State C _, σ'.erase = τ' → τ.H <+: σ'.H → holds σ' φ)
        (U.apply τ.erase)
      rw [hτ]
      intro σ' he _
      refine ih (ρ := U.replayS noActE noActR ρ) hp σ' (he ▸ h') hk
    · cases hp; exact hk τ h
  | bind m x t φ ih =>
    intro ρ Γ' ρ' φ' hp τ h hk
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    rw [← Fml.peelS_eq_peelSM] at hp
    intro v
    refine ih (ρ := ρ.push .keep) hp (τ.push v) ?_ hk
    rw [State.push_erase]
    exact h.pushFree _
  | _ => intro ρ Γ' ρ' φ' hp τ h hk; cases hp; exact hk τ h

/-- **Peeling, read the other way**: where a formula holds, what it peels
to holds in a typed state the peeled constructors reach. -/
theorem peel_neg : ∀ {Γ : Ctx} (φ : Fml C Γ) {ρ : SymS} {Γ' : Ctx} {ρ' : SymS} {φ' : Fml C Γ'},
    φ.peelS ρ = ⟨Γ', ρ', φ'⟩ → ∀ τ : State C Γ, RelU σ ρ τ.erase → holds τ φ →
      ∃ τ' : State C Γ', RelU σ ρ' τ'.erase ∧ holds τ' φ' := by
  intro Γ φ
  induction φ with
  | upd m U φ ih =>
    intro ρ Γ' ρ' φ' hp τ h hφ
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    split at hp
    · rename_i hv
      rw [← Fml.peelS_eq_peelSM] at hp
      obtain ⟨τe, hτ, h', hs⟩ := RelU.zero noActE noActR h U hv
      obtain ⟨τ'', hτ'', hH⟩ := zero_typed noActE noActR τ U hv
      rw [hτ''] at hτ
      cases hτ
      change m.afterC (fun τ' => ∀ σ' : State C _, σ'.erase = τ' → τ.H <+: σ'.H → holds σ' φ)
        (U.apply τ.erase) at hφ
      rw [hτ''] at hφ
      exact ih (ρ := U.replayS noActE noActR ρ) hp τ'' h'
        (hφ τ'' rfl (hH ▸ List.prefix_refl _))
    · cases hp; exact ⟨τ, h, hφ⟩
  | bind m x t φ ih =>
    intro ρ Γ' ρ' φ' hp τ h hφ
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    rw [← Fml.peelS_eq_peelSM] at hp
    obtain ⟨v⟩ := LTy.tdenote_nonempty (C := C) (H := τ.H) t
    refine ih (ρ := ρ.push .keep) hp (τ.push v) ?_ (hφ v)
    rw [State.push_erase]
    exact h.pushFree _
  | _ => intro ρ Γ' ρ' φ' hp τ h hφ; cases hp; exact ⟨τ, h, hφ⟩

/-- Peeling reaches a typed state. -/
theorem peel_exists : ∀ {Γ : Ctx} (φ : Fml C Γ) {ρ : SymS} {Γ' : Ctx} {ρ' : SymS}
    {φ' : Fml C Γ'}, φ.peelS ρ = ⟨Γ', ρ', φ'⟩ → ∀ τ : State C Γ, RelU σ ρ τ.erase →
      ∃ τ' : State C Γ', RelU σ ρ' τ'.erase := by
  intro Γ φ
  induction φ with
  | upd m U φ ih =>
    intro ρ Γ' ρ' φ' hp τ h
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    split at hp
    · rename_i hv
      rw [← Fml.peelS_eq_peelSM] at hp
      obtain ⟨τe, hτ, h', hs⟩ := RelU.zero noActE noActR h U hv
      obtain ⟨τ'', hτ'', -⟩ := zero_typed noActE noActR τ U hv
      rw [hτ''] at hτ
      cases hτ
      exact ih (ρ := U.replayS noActE noActR ρ) hp τ'' h'
    · cases hp; exact ⟨τ, h⟩
  | bind m x t φ ih =>
    intro ρ Γ' ρ' φ' hp τ h
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    rw [← Fml.peelS_eq_peelSM] at hp
    obtain ⟨v⟩ := LTy.tdenote_nonempty (C := C) (H := τ.H) t
    refine ih (ρ := ρ.push .keep) hp (τ.push v) ?_
    rw [State.push_erase]
    exact h.pushFree _
  | _ => intro ρ Γ' ρ' φ' hp τ h; cases hp; exact ⟨τ, h⟩

theorem Fml.asDefinedS_some {Γ : Ctx} {φ : Fml C Γ} {a : Tm C Γ .val}
    (h : φ.asDefinedS = some a) : φ = .defined a := by
  cases φ <;> simp only [Fml.asDefinedS, reduceCtorEq, Option.some.injEq] at h
  rw [h]

theorem Fml.asAndS_some {Γ : Ctx} {φ ψ₁ ψ₂ : Fml C Γ} (h : φ.asAndS = some (ψ₁, ψ₂)) :
    φ = .and ψ₁ ψ₂ := by
  cases φ <;> simp only [Fml.asAndS, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  rw [h.1, h.2]

theorem Fml.asEqS_some {Γ : Ctx} {φ : Fml C Γ} {a b : Tm C Γ .val}
    (h : φ.asEqS = some (a, b)) : φ = .eq a b := by
  cases φ <;> simp only [Fml.asEqS, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  rw [h.1, h.2]

/-- A term lowers alike in two states with the same positions and symbols. -/
theorem _root_.Solidity.Tm.toLSM_congr {Γ : Ctx} {ρ ρ' : SymS} (hl : ρ.loc = ρ'.loc)
    (hs : ρ.sym = ρ'.sym) : {s : Srt} → (t : Tm C Γ s) → t.toLSM ρ = t.toLSM ρ' ∧
      t.inLSM ρ = t.inLSM ρ' := by
  obtain ⟨l, sy, n⟩ := ρ
  obtain ⟨l', sy', n'⟩ := ρ'
  simp only at hl hs
  subst hl hs
  intro s t
  induction t with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ | app0 _ => exact ⟨rfl, rfl⟩
  | app1 o _ x ih => refine ⟨?_, ?_⟩ <;> simp only [Tm.toLSM, Tm.inLSM, ih.1, ih.2] <;> rfl
  | app2 o x y ihx ihy =>
    refine ⟨?_, ?_⟩ <;> simp only [Tm.toLSM, Tm.inLSM, ihx.1, ihx.2, ihy.1, ihy.2] <;> rfl
  | app3 o x y z ihx ihy ihz =>
    refine ⟨?_, ?_⟩ <;>
      simp only [Tm.toLSM, Tm.inLSM, ihx.1, ihx.2, ihy.1, ihy.2, ihz.1, ihz.2] <;> rfl

/-- **An equation's two readings, the same** (`sameAt`): one term in one
context with the same keys, read with the same symbols, lowers alike. -/
theorem sameAt_toLS {Γ Δ : Ctx} {ρa ρb : SymS} {a : Tm C Γ .val} {b : Tm C Δ .val}
    (h : sameAt ρa a ρb b = true) (hs : ρa.sym = ρb.sym) (hoka : ρa.Ok ρa.names)
    (hokb : ρb.Ok ρb.names) : b.toLS ρb = a.toLS ρa ∧ b.inLS ρb = a.inLS ρa := by
  unfold sameAt at h
  split at h
  · rename_i e _
    subst e
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨-, hn⟩, hb⟩ := h
    have hab : a = b := Tm.eq_of_beqR hb
    subst hab
    have hl : ρb.loc = ρa.loc := by
      unfold SymS.Ok at hoka hokb
      rw [hokb, hoka, hn, hs]
    rw [Tm.toLS_eq_toLSM, Tm.toLS_eq_toLSM, Tm.inLS_eq_inLSM, Tm.inLS_eq_inLSM]
    exact Tm.toLSM_congr hl hs.symm a
  · cases h

/-- What `eqDViewS` recognises: `defined a ∧ (defined b ∧ a' = b')`
through peeled constructors, `a'` and `b'` the same terms as `a` and `b`. -/
theorem eqDViewS_spec {Γ : Ctx} {ρ : SymS} {φ ψ : Fml C Γ} {A B : (Γ' : Ctx) × SymS × Tm C Γ' .val}
    (h : eqDViewS ρ φ ψ = some (A, B)) :
    φ.peelS ρ = ⟨A.1, A.2.1, .defined A.2.2⟩ ∧
      ∃ (Γ' : Ctx) (ρ' : SymS) (ψ₁ ψ₂ : Fml C Γ'), ψ.peelS ρ = ⟨Γ', ρ', .and ψ₁ ψ₂⟩ ∧
        ψ₁.peelS ρ' = ⟨B.1, B.2.1, .defined B.2.2⟩ ∧
        ∃ (Γc : Ctx) (ρc : SymS) (a' b' : Tm C Γc .val), ψ₂.peelS ρ' = ⟨Γc, ρc, .eq a' b'⟩ ∧
          sameAt A.2.1 A.2.2 ρc a' = true ∧ sameAt B.2.1 B.2.2 ρc b' = true := by
  unfold eqDViewS at h
  dsimp only at h
  split at h
  · rename_i a₀ ψ₁ ψ₂ ha hb
    split at h
    · rename_i b₀ a' b' h₁ h₂
      split at h
      · rename_i hs
        simp only [Bool.and_eq_true] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, (ψ.peelS ρ).1, (ψ.peelS ρ).2.1, ψ₁, ψ₂, ?_, ?_,
          (ψ₂.peelS (ψ.peelS ρ).2.1).1, (ψ₂.peelS (ψ.peelS ρ).2.1).2.1, a', b', ?_, hs.1, hs.2⟩
        · rw [← Fml.asDefinedS_some ha]
        · rw [← Fml.asAndS_some hb]
        · rw [← Fml.asDefinedS_some h₁]
        · rw [← Fml.asEqS_some h₂]
      · cases h
    · cases h
  · cases h

end Peel

/-! ## The reduction is sound -/

section Sound

variable {Γ : Ctx}

/-- A literal, `msg.sender` or a local reads a value. -/
theorem Tm.eval_of_atomLike {t : Tm C Γ .val} (τ : EState C Γ)
    (h : t.isLitLikeS = true ∨ t.isAtomS = true) : ∃ x, t.eval τ = .ok x := by
  cases t with
  | app0 o => cases o <;> exact ⟨_, rfl⟩
  | pvV i => exact ⟨_, rfl⟩
  | _ => rcases h with h | h <;> simp only [Tm.isLitLikeS, Tm.isAtomS, Bool.false_eq_true] at h

/-- Between two terms that return, the equation is equality of the
values. -/
theorem holds_eq_of_eval {τ : State C Γ} {a b : Tm C Γ .val} {x y : Value}
    (ha : a.eval τ.erase = .ok x) (hb : b.eval τ.erase = .ok y) :
    holds τ (.eq a b) ↔ x = y := by
  show Theory.StValue.Equiv (a.denote τ.erase) (b.denote τ.erase) ↔ x = y
  rw [Tm.denote_eval τ.erase a x ha, Tm.denote_eval τ.erase b y hb,
    Theory.StValue.Equiv.prim_iff]
  exact ⟨fun h => by injection h, fun h => h ▸ rfl⟩

/-- **An equation through peeled constructors** (`eqDViewS`): both
readings return one value, read in every typed state the peels reach. -/
theorem eqD_sound {φ ψ : Fml C Γ} {σ : Semantics.State} {ρ : SymS}
    {τ : State C Γ} (h : RelU σ ρ τ.erase) {Γa Γb : Ctx} {ρa ρb : SymS} {a : Tm C Γa .val}
    {b : Tm C Γb .val} (hv : eqDViewS ρ φ ψ = some (⟨Γa, ρa, a⟩, ⟨Γb, ρb, b⟩))
    (ha : a.inLS ρa = true) (hb : b.inLS ρb = true) :
    holds τ (.and φ ψ) ↔ (LFml.eq (a.toLS ρa) (b.toLS ρb)).holds σ := by
  obtain ⟨hpa, Γ', ρ', ψ₁, ψ₂, hpb, hp₁, Γc, ρc, a', b', hp₂, hsa, hsb⟩ := eqDViewS_spec hv
  have sa := peel_sym φ hpa
  have s' := peel_sym ψ hpb
  have sb := peel_sym ψ₁ hp₁
  have sc := peel_sym ψ₂ hp₂
  obtain ⟨τa, hra⟩ := peel_exists φ hpa τ h
  obtain ⟨τ₁, hr₁⟩ := peel_exists ψ hpb τ h
  obtain ⟨τb, hrb⟩ := peel_exists ψ₁ hp₁ τ₁ hr₁
  obtain ⟨τc, hrc⟩ := peel_exists ψ₂ hp₂ τ₁ hr₁
  -- the equation's readings lower as the definedness conjuncts' do
  have ea := sameAt_toLS hsa (by rw [sa, sc, s']) hra.ok hrc.ok
  have eb := sameAt_toLS hsb (by rw [sb, sc]) hrb.ok hrc.ok
  have A2 : ∀ τa' : State C Γa, RelU σ ρa τa'.erase →
      Sim ((a.toLS ρa).eval σ) (a.eval τa'.erase) := fun _ hr => hr.val ha
  have B2 : ∀ τb' : State C Γb, RelU σ ρb τb'.erase →
      Sim ((b.toLS ρb).eval σ) (b.eval τb'.erase) := fun _ hr => hr.val hb
  have A3 : ∀ τc' : State C Γc, RelU σ ρc τc'.erase →
      Sim ((a.toLS ρa).eval σ) (a'.eval τc'.erase) := by
    intro τc' hr
    rw [← ea.1]
    exact hr.val (by rw [ea.2]; exact ha)
  have B3 : ∀ τc' : State C Γc, RelU σ ρc τc'.erase →
      Sim ((b.toLS ρb).eval σ) (b'.eval τc'.erase) := by
    intro τc' hr
    rw [← eb.1]
    exact hr.val (by rw [eb.2]; exact hb)
  rw [LFml.holds_eq_iff]
  constructor
  · rintro ⟨hφ, hψ⟩
    obtain ⟨τa', hra', ⟨x, hx⟩⟩ := peel_neg φ hpa τ h hφ
    obtain ⟨τ₂, hr₂, hψ₁, hψ₂⟩ := peel_neg ψ hpb τ h hψ
    obtain ⟨τb', hrb', ⟨y, hy⟩⟩ := peel_neg ψ₁ hp₁ τ₂ hr₂ hψ₁
    obtain ⟨τc', hrc', hc⟩ := peel_neg ψ₂ hp₂ τ₂ hr₂ hψ₂
    have hx' := (A2 τa' hra' x).2 hx
    have hy' := (B2 τb' hrb' y).2 hy
    have hxy := (holds_eq_of_eval ((A3 τc' hrc' x).1 hx') ((B3 τc' hrc' y).1 hy')).1 hc
    subst hxy
    exact ⟨x, hx', hy'⟩
  · rintro ⟨x, hx, hy⟩
    refine ⟨peel_pos φ hpa τ h fun τa' hra' => ⟨x, (A2 τa' hra' x).1 hx⟩,
      peel_pos ψ hpb τ h fun τ₂ hr₂ => ⟨peel_pos ψ₁ hp₁ τ₂ hr₂ fun τb' hrb' =>
        ⟨x, (B2 τb' hrb' x).1 hy⟩, peel_pos ψ₂ hp₂ τ₂ hr₂ fun τc' hrc' =>
        (holds_eq_of_eval ((A3 τc' hrc' x).1 hx) ((B3 τc' hrc' x).1 hy)).2 rfl⟩⟩

/-- **The scoped reduction is sound**, over the typed state, at the
polarity `pos`: where the fragment takes a formula, its reduction read in
`σ` gives the formula in every typed state `ρ` stands for (positive), and
the formula gives its reduction (negative, where it is first-order). -/
theorem _root_.Solidity.Fml.toLSM_sound : ∀ {Γ : Ctx} (φ : Fml C Γ) (pos : Bool)
    {σ : Semantics.State} {ρ : SymS} (τ : State C Γ),
    RelU σ ρ τ.erase → φ.inLSM pos ρ = true →
    (pos = true → (φ.toLSM ρ).holds σ → holds τ φ) ∧
      (pos = false → holds τ φ → (φ.toLSM ρ).holds σ) := by
  intro Γ φ
  induction φ with
  | tt => intro pos σ ρ τ h hf; exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  | eq a b =>
    intro pos σ ρ τ h hf
    simp only [Fml.inLSM, Bool.and_eq_true] at hf
    obtain ⟨⟨hl, ha⟩, hb⟩ := hf
    have key : holds τ (.eq a b) ↔ (Fml.toLSM ρ (.eq a b)).holds σ := by
      have hab : (a.isLitLikeS = true ∨ a.isAtomS = true) ∧
          (b.isLitLikeS = true ∨ b.isAtomS = true) := by
        simp only [Tm.eqLitS, Bool.or_eq_true, Bool.and_eq_true] at hl
        rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨.inl h1, .inr h2⟩
        · exact ⟨.inr h2, .inl h1⟩
      obtain ⟨x, hx⟩ := Tm.eval_of_atomLike τ.erase hab.1
      obtain ⟨y, hy⟩ := Tm.eval_of_atomLike τ.erase hab.2
      rw [holds_eq_of_eval hx hy]
      simp only [Fml.toLSM]
      rw [LFml.holds_eq_iff]
      have sa := h.val ha
      have sb := h.val hb
      constructor
      · rintro rfl; exact ⟨x, (sa x).2 hx, (sb x).2 hy⟩
      · rintro ⟨z, hz₁, hz₂⟩
        have e1 := (sa z).1 hz₁
        have e2 := (sb z).1 hz₂
        rw [hx] at e1; rw [hy] at e2
        cases e1; cases e2; rfl
    exact ⟨fun _ hL => key.2 hL, fun _ hφ => key.1 hφ⟩
  | defined t =>
    intro pos σ ρ τ h hf
    simp only [Fml.inLSM] at hf
    have st := h.val hf
    have key : holds τ (.defined t) ↔ (Fml.toLSM ρ (.defined t)).holds σ := by
      simp only [Fml.toLSM]
      rw [holds_eq_self]
      show (∃ x, t.eval τ.erase = .ok x) ↔ _
      exact ⟨fun ⟨x, hx⟩ => ⟨x, (st x).2 hx⟩, fun ⟨x, hx⟩ => ⟨x, (st x).1 hx⟩⟩
    exact ⟨fun _ hL => key.2 hL, fun _ hφ => key.1 hφ⟩
  | not φ ih =>
    intro pos σ ρ τ h hf
    simp only [Fml.inLSM] at hf
    have hi := ih (!pos) τ h hf
    simp only [Fml.toLSM, LFml.holds]
    refine ⟨fun hp hL hφ => ?_, fun hp hφ hL => ?_⟩
    · subst hp; exact hL (hi.2 rfl hφ)
    · subst hp; exact hφ (hi.1 rfl hL)
  | and φ ψ ihφ ihψ =>
    intro pos σ ρ τ h hf
    cases hv : eqDViewS ρ φ ψ with
    | none =>
      simp only [Fml.inLSM, hv, Bool.and_eq_true] at hf
      have h1 := ihφ pos τ h hf.1
      have h2 := ihψ pos τ h hf.2
      simp only [Fml.toLSM, hv, LFml.holds]
      exact ⟨fun hp hL => ⟨h1.1 hp hL.1, h2.1 hp hL.2⟩,
        fun hp hφ => ⟨h1.2 hp hφ.1, h2.2 hp hφ.2⟩⟩
    | some AB =>
      obtain ⟨⟨Γa, ρa, a⟩, ⟨Γb, ρb, b⟩⟩ := AB
      simp only [Fml.inLSM, hv, Bool.and_eq_true] at hf
      have key := eqD_sound h hv hf.1 hf.2
      simp only [Fml.toLSM, hv]
      exact ⟨fun _ hL => key.2 hL, fun _ hφ => key.1 hφ⟩
  | imp φ ψ ihφ ihψ =>
    intro pos σ ρ τ h hf
    simp only [Fml.inLSM, Bool.and_eq_true] at hf
    have h1 := ihφ (!pos) τ h hf.1
    have h2 := ihψ pos τ h hf.2
    simp only [Fml.toLSM, LFml.holds]
    refine ⟨fun hp hL hφ => h2.1 hp (hL (h1.2 (by rw [hp]; rfl) hφ)),
      fun hp hφψ hL => h2.2 hp (hφψ (h1.1 (by rw [hp]; rfl) hL))⟩
  | upd m U φ ih =>
    intro pos σ ρ τ h hf
    simp only [Fml.inLSM, Bool.and_eq_true] at hf
    obtain ⟨rfl, hf⟩ := hf
    refine ⟨fun _ hL => ?_, fun hp => Bool.noConfusion hp⟩
    show m.afterC (fun τ' => ∀ σ' : State C _, σ'.erase = τ' → τ.H <+: σ'.H → holds σ' φ)
      (U.apply τ.erase)
    cases hv : U.view with
    | zero =>
      simp only [Fml.toLSM, hv] at hL
      simp only [hv] at hf
      obtain ⟨τe, hτ, h', -⟩ := RelU.zero noActE noActR h U hv
      rw [hτ]
      intro σ' he _
      exact (ih true σ' (by rw [he]; exact h') hf).1 rfl hL
    | one a =>
      simp only [Fml.toLSM, hv] at hL
      simp only [hv, Bool.and_eq_true] at hf
      obtain ⟨hg, hr⟩ := RelU.one h U hv hf.1
      cases hap : U.apply τ.erase with
      | error e =>
        cases m with
        | box => trivial
        | diamond =>
          rw [guardM_diamond] at hL
          obtain ⟨τ', h'⟩ := hg.1 hL.1
          rw [hap] at h'; cases h'
      | ok τe =>
        intro σ' he _
        have hgret : ∃ v, (a.guard ρ).eval σ = .ok v := hg.2 ⟨τe, hap⟩
        have hL' : (φ.toLSM (U.replayS (UpdElem.actS ρ) (fun r => .ofOpt (r.actS ρ)) ρ)).holds σ := by
          cases m with
          | box => exact (guardM_box σ _ _).1 hL hgret
          | diamond => exact ((guardM_diamond σ _ _).1 hL).2
        exact (ih true σ' (by rw [he]; exact hr τe hap) hf.2).1 rfl hL'
    | two a b =>
      simp only [Fml.toLSM, hv] at hL
      simp only [hv] at hf
      cases hp : pairViewS a b with
      | none =>
        simp only [hp, Bool.and_eq_true] at hf hL
        obtain ⟨hg, hr⟩ := RelU.par h U hv hf.1
        cases hap : U.apply τ.erase with
        | error e =>
          cases m with
          | box => trivial
          | diamond =>
            rw [guardM_diamond] at hL
            obtain ⟨τ', h'⟩ := hg.1 hL.1
            rw [hap] at h'; cases h'
        | ok τe =>
          intro σ' he _
          have hgret : ∃ v, (seqL (a.guard ρ) (b.guard ρ)).eval σ = .ok v := hg.2 ⟨τe, hap⟩
          have hL' : (φ.toLSM (U.replayS (UpdElem.actS ρ) (fun r => .ofOpt (r.actS ρ)) ρ)).holds
              σ := by
            cases m with
            | box => exact (guardM_box σ _ _).1 hL hgret
            | diamond => exact ((guardM_diamond σ _ _).1 hL).2
          exact (ih true σ' (by rw [he]; exact hr τe hap) hf.2).1 rfl hL'
      | some p =>
        obtain ⟨i, mm⟩ := p
        cases hq : pairLS ρ i mm with
        | none => simp only [hp, hq, Bool.false_eq_true] at hf
        | some q =>
          obtain ⟨g, M⟩ := q
          simp only [hp, hq, Bool.and_eq_true] at hf hL
          obtain ⟨hg, hr⟩ := RelU.two h hq hf.1.1 U hv hp
          cases hap : U.apply τ.erase with
          | error e =>
            cases m with
            | box => trivial
            | diamond =>
              rw [guardM_diamond] at hL
              obtain ⟨τ', h'⟩ := hg.1 hL.1
              rw [hap] at h'; cases h'
          | ok τe =>
            intro σ' he _
            have hgret : ∃ v, g.eval σ = .ok v := hg.2 ⟨τe, hap⟩
            have hL' : (φ.toLSM (U.replayS (pairActE ρ M) (pairActR ρ) ρ)).holds σ := by
              cases m with
              | box => exact (guardM_box σ _ _).1 hL hgret
              | diamond => exact ((guardM_diamond σ _ _).1 hL).2
            exact (ih true σ' (by rw [he]; exact hr τe hap) hf.2).1 rfl hL'
    | many => simp only [hv, Bool.false_eq_true] at hf
  | modal m P κ φ ih =>
    intro pos σ ρ τ h hf
    simp only [Fml.inLSM] at hf
    subst hf
    refine ⟨fun _ hL => ?_, fun hp => Bool.noConfusion hp⟩
    simp only [Fml.toLSM, LFml.holds] at hL
    exact absurd trivial hL
  | havoc φ ih =>
    intro pos σ ρ τ h hf
    simp only [Fml.inLSM, Bool.false_eq_true] at hf
  | anon xs φ ih =>
    intro pos σ ρ τ h hf
    simp only [Fml.inLSM, Bool.false_eq_true] at hf
  | all x p φ ih =>
    intro pos σ ρ τ h hf
    simp only [Fml.inLSM, Bool.and_eq_true, Bool.not_eq_true'] at hf
    obtain ⟨hx, hf⟩ := hf
    simp only [Fml.toLSM, LFml.holds]
    refine ⟨fun hp hL v => ?_, fun hp hφ w hw => ?_⟩
    · exact (ih pos (τ.push v) (by rw [State.push_erase]; exact h.pushQ hx (PrimTy.erase v))
        hf).1 hp (hL _ (PrimTy.admits_erase v))
    · obtain ⟨v, rfl⟩ := PrimTy.exists_of_admits hw
      exact (ih pos (τ.push v) (by rw [State.push_erase]; exact h.pushQ hx (PrimTy.erase v))
        hf).2 hp (hφ v)
  | bind m x t φ ih =>
    intro pos σ ρ τ h hf
    simp only [Fml.inLSM, Bool.and_eq_true] at hf
    obtain ⟨rfl, hf⟩ := hf
    refine ⟨fun _ hL => ?_, fun hp => Bool.noConfusion hp⟩
    simp only [Fml.toLSM] at hL
    intro v
    exact (ih true (τ.push v) (by rw [State.push_erase]; exact h.pushFree _) hf).1 rfl hL

/-- The state a typed state's reduction is read in: its global part, no
local. -/
def _root_.Solidity.State.redState {Γ : Ctx} (τ : State C Γ) : Semantics.State :=
  withLocals τ.erase.glob []

/-- The reduction's start: no update, no local. -/
theorem RelU.empty (τ : State C []) : RelU τ.redState SymS.empty τ.erase :=
  { ok := rfl, len := rfl, nodup := List.nodup_nil,
    fresh := fun _ _ => ⟨List.not_mem_nil, rfl⟩, stor := rfl,
    env := fun _ hm => (nomatch hm), tx := fun k => by cases k <;> rfl,
    mem := ⟨memBase _, [], rfl, rfl, rfl⟩ }

/-- A leaf holds in a typed state where its reduction holds in the state
the reduction reads (`Fml.toLSM_sound` at the start). -/
theorem holds_of_reduceS {φ : Fml C []} (hf : φ.inLS true SymS.empty = true) (τ : State C [])
    (h : φ.reduceS.holds τ.redState) : holds τ φ := by
  have hL : (φ.toLSM SymS.empty).holds τ.redState := by
    rw [← Fml.toLS_eq_toLSM]
    exact (LFml.elim_holds _ _).1 h
  exact (Fml.toLSM_sound φ true τ (RelU.empty τ)
    (by rw [← Fml.inLS_eq_inLSM]; exact hf)).1 rfl hL

/-- **The boundary, scoped**: a leaf is valid where its reduction, computed
on the leaf itself, holds in every state; the fragment is checked on the
leaf (`Fml.inLS`).  Proved over the typed state (`Fml.toLSM_sound`), not
through the leaf's erasure. -/
theorem _root_.Solidity.Valid.of_reduceS {φ : Fml C []} (hf : φ.inLS true SymS.empty = true)
    (h : ∀ σ, φ.reduceS.holds σ) : Valid φ :=
  fun τ => holds_of_reduceS hf τ (h _)

end Sound

end Decide

end Solidity
