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

What relates the reduction's state to the scoped state is `RelU σ ρ g ℓ`,
on a global part and the locals' values (`RelT σ ρ τ` on a typed state, its
`τ.globE` and `τ.loc`; `Calculus/DecideRel.lean`), and what a term or an update pushed in reads
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

/-! ## A primitive value and the values its type admits -/

section
open Semantics (Value Seg Halt Res Binding lookupBy setBy)
open Solidity (Srt Op0 Op1 Op2 Op3 Modality)
variable {C : Contract}

theorem _root_.Solidity.PrimTy.admits_erase : {p : PrimTy} → (v : p.Denote) → p.admits (PrimTy.erase v)
  | .bool, _ => trivial
  | .uint, ⟨_, h⟩ => by
    simp only [PrimTy.inRange, decide_eq_true_eq] at h
    exact h
  | .int, ⟨_, h⟩ => by
    simp only [PrimTy.inRange, decide_eq_true_eq] at h
    exact h

theorem _root_.Solidity.PrimTy.exists_of_admits :
    {p : PrimTy} → {v : Semantics.Value} → p.admits v → ∃ w : p.Denote, PrimTy.erase w = v
  | .bool, .bool b, _ => ⟨b, rfl⟩
  | .uint, .int n, h =>
    ⟨(⟨n, by simp only [PrimTy.inRange, decide_eq_true_eq]; exact h⟩ :
      {n : Int // PrimTy.uint.inRange n = true}), rfl⟩
  | .int, .int n, h =>
    ⟨(⟨n, by
        simp only [PrimTy.inRange, decide_eq_true_eq]
        exact h⟩ :
      {n : Int // PrimTy.int.inRange n = true}), rfl⟩
  | .bool, .int _, h | .uint, .bool _, h | .int, .bool _, h => h.elim

end



namespace Decide

open Semantics SemanticsProperties

variable {C : Contract}

/-! ## Through the constructors the erasure drops -/

section Peel

variable {σ : Semantics.State}

/-- An update of pops and drops, on a typed state: it ends in the typed
state its pops and drops leave. -/
theorem zero_typed {Γ : Ctx} (τ : State C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → U.view = .zero →
      ∃ (τ' : State C Δ) (hp : τ.H <+: τ'.glob.H), U.applyV τ = some (⟨τ'.glob, hp⟩, τ'.locV)
  | _, .nil, _ => ⟨τ, List.prefix_refl _, rfl⟩
  | _, .snoc U e, hv => absurd hv (UView.add_ne_zero U.view e.toElemS)
  | _, .decl U _ r, hv => absurd hv (UView.add_ne_zero U.view (.rhs r))
  | _, .pop U hx, hv => by
    obtain ⟨τ', hp, hτ⟩ := zero_typed τ U hv
    refine ⟨τ'.drop hx, hp, ?_⟩
    show (U.applyV τ).bind (fun p => some (p.1, p.2.drop hx)) = _
    rw [hτ, Option.bind_some, State.locV_drop]
    rfl
  | _, .drop U hx, hv => by
    obtain ⟨τ', hp, hτ⟩ := zero_typed τ U hv
    refine ⟨τ'.thin hx, hp, ?_⟩
    show (U.applyV τ).bind (fun p => some (p.1, p.2.thin hx)) = _
    rw [hτ, Option.bind_some, State.locV_thin]
    rfl

/-- A typed state with the global part and the locals an update leaves
stands where the update's erased result does. -/
theorem RelT.of_lands {Δ : Ctx} {ρ : SymS} {H : HTy} {q : GlobT C H × LocsV C Δ}
    (h : RelU σ ρ (eraseQ q).1 (eraseQ q).2) {σ' : State C Δ} (hg : σ'.glob = q.1.1)
    (hl : ∀ {t : LTy} (i : Idx Δ t), σ'.getV i = q.2 t i) : RelT σ ρ σ' := by
  have hl' : σ'.loc = q.2.erase := by
    rw [← State.locV_erase]
    funext t i
    show LTy.VDen.erase t (σ'.getV i) = LTy.VDen.erase t (q.2 t i)
    rw [hl i]
  have hg' : σ'.globE = q.1.1.globE := by rw [← State.glob_globE, hg]
  show RelU σ ρ σ'.globE σ'.loc
  rw [hg', hl']
  exact h

/-- A pushed typed state stands where the pushed locals do. -/
theorem RelT.push {Γ : Ctx} {ρ : SymS} {τ : State C Γ} {t : LTy} {v : t.TDenote C τ.H}
    (h : RelU σ ρ τ.globE (τ.loc.push (LTy.TDenote.erase t v))) : RelT σ ρ (τ.push v) := by
  have hl : (τ.push v).loc = τ.loc.push (LTy.TDenote.erase t v) := by
    funext u j
    cases j <;> rfl
  show RelU σ ρ (τ.push v).globE (τ.push v).loc
  rw [hl]
  exact h

/-- The erased application of an update that returns: the typed one
erased. -/
theorem applyVE_ok {Γ Δ : Ctx} {τ : State C Γ} {U : Upd C Γ Δ} {τe : Semantics.State × Locs C Δ}
    (h : U.applyVE τ = .ok τe) : ∃ q, U.applyV τ = some q ∧ τe = eraseQ q := by
  rw [Upd.applyVE_eq] at h
  cases hq : U.applyV τ with
  | none => rw [hq] at h; cases h
  | some q =>
    rw [hq] at h
    cases h
    exact ⟨q, rfl, rfl⟩

theorem applyVE_none {Γ Δ : Ctx} {τ : State C Γ} {U : Upd C Γ Δ} (h : U.applyV τ = none) :
    ∀ τe, U.applyVE τ ≠ .ok τe := by
  intro τe he
  rw [Upd.applyVE_eq, h] at he
  cases he

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
    φ.peelS ρ = ⟨Γ', ρ', φ'⟩ → ∀ τ : State C Γ, RelT σ ρ τ →
      (∀ τ' : State C Γ', RelT σ ρ' τ' → holds τ' φ') → holds τ φ := by
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
      obtain ⟨q, hq, rfl⟩ := applyVE_ok hτ
      show U.afterT m τ (holds · φ)
      rw [Upd.afterT_applyV, hq]
      intro σ' hg hl
      exact ih (ρ := U.replayS noActE noActR ρ) hp σ' (RelT.of_lands h' hg hl) hk
    · cases hp; exact hk τ h
  | bind m x t φ ih =>
    intro ρ Γ' ρ' φ' hp τ h hk
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    rw [← Fml.peelS_eq_peelSM] at hp
    intro v
    exact ih (ρ := ρ.push .keep) hp (τ.push v) (RelT.push (h.pushFree _)) hk
  | _ => intro ρ Γ' ρ' φ' hp τ h hk; cases hp; exact hk τ h

/-- **Peeling, read the other way**: where a formula holds, what it peels
to holds in a typed state the peeled constructors reach. -/
theorem peel_neg : ∀ {Γ : Ctx} (φ : Fml C Γ) {ρ : SymS} {Γ' : Ctx} {ρ' : SymS} {φ' : Fml C Γ'},
    φ.peelS ρ = ⟨Γ', ρ', φ'⟩ → ∀ τ : State C Γ, RelT σ ρ τ → holds τ φ →
      ∃ τ' : State C Γ', RelT σ ρ' τ' ∧ holds τ' φ' := by
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
      obtain ⟨τ'', hp', hτ''⟩ := zero_typed τ U hv
      obtain ⟨q, hq, rfl⟩ := applyVE_ok hτ
      have hφ' : U.afterT m τ (holds · φ) := hφ
      rw [Upd.afterT_applyV, hτ''] at hφ'
      rw [hτ''] at hq
      cases hq
      exact ih (ρ := U.replayS noActE noActR ρ) hp τ'' (RelT.of_lands h' rfl fun _ => rfl)
        (hφ' τ'' rfl (fun _ => rfl))
    · cases hp; exact ⟨τ, h, hφ⟩
  | bind m x t φ ih =>
    intro ρ Γ' ρ' φ' hp τ h hφ
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    rw [← Fml.peelS_eq_peelSM] at hp
    obtain ⟨v⟩ := LTy.tdenote_nonempty (C := C) (H := τ.H) t
    exact ih (ρ := ρ.push .keep) hp (τ.push v) (RelT.push (h.pushFree _)) (hφ v)
  | _ => intro ρ Γ' ρ' φ' hp τ h hφ; cases hp; exact ⟨τ, h, hφ⟩

/-- Peeling reaches a typed state. -/
theorem peel_exists : ∀ {Γ : Ctx} (φ : Fml C Γ) {ρ : SymS} {Γ' : Ctx} {ρ' : SymS}
    {φ' : Fml C Γ'}, φ.peelS ρ = ⟨Γ', ρ', φ'⟩ → ∀ τ : State C Γ, RelT σ ρ τ →
      ∃ τ' : State C Γ', RelT σ ρ' τ' := by
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
      obtain ⟨τ'', hp', hτ''⟩ := zero_typed τ U hv
      obtain ⟨q, hq, rfl⟩ := applyVE_ok hτ
      rw [hτ''] at hq
      cases hq
      exact ih (ρ := U.replayS noActE noActR ρ) hp τ'' (RelT.of_lands h' rfl fun _ => rfl)
    · cases hp; exact ⟨τ, h⟩
  | bind m x t φ ih =>
    intro ρ Γ' ρ' φ' hp τ h
    rw [Fml.peelS_eq_peelSM] at hp
    simp only [Fml.peelSM] at hp
    rw [← Fml.peelS_eq_peelSM] at hp
    obtain ⟨v⟩ := LTy.tdenote_nonempty (C := C) (H := τ.H) t
    exact ih (ρ := ρ.push .keep) hp (τ.push v) (RelT.push (h.pushFree _))
  | _ => intro ρ Γ' ρ' φ' hp τ h; cases hp; exact ⟨τ, h⟩

theorem Fml.asDefinedS_some {Γ : Ctx} {φ : Fml C Γ} {p : PrimTy} {a : Tm C Γ (.val p)}
    (h : φ.asDefinedS = some ⟨p, a⟩) : φ = .defined a := by
  cases φ <;> simp only [Fml.asDefinedS, reduceCtorEq, Option.some.injEq, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  cases h
  rfl

theorem Fml.asAndS_some {Γ : Ctx} {φ ψ₁ ψ₂ : Fml C Γ} (h : φ.asAndS = some (ψ₁, ψ₂)) :
    φ = .and ψ₁ ψ₂ := by
  cases φ <;> simp only [Fml.asAndS, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  rw [h.1, h.2]

theorem Fml.asEqS_some {Γ : Ctx} {φ : Fml C Γ} {p : PrimTy} {a b : Tm C Γ (.val p)}
    (h : φ.asEqS = some ⟨p, a, b⟩) : φ = .eq a b := by
  cases φ <;> simp only [Fml.asEqS, reduceCtorEq, Option.some.injEq, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

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
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ | app0 _ | pvZ _ => exact ⟨rfl, rfl⟩
  | app1 o x ih => refine ⟨?_, ?_⟩ <;> simp only [Tm.toLSM, Tm.inLSM, ih.1, ih.2] <;> rfl
  | app2 o x y ihx ihy =>
    refine ⟨?_, ?_⟩ <;> simp only [Tm.toLSM, Tm.inLSM, ihx.1, ihx.2, ihy.1, ihy.2] <;> rfl
  | app3 o x y z ihx ihy ihz =>
    refine ⟨?_, ?_⟩ <;>
      simp only [Tm.toLSM, Tm.inLSM, ihx.1, ihx.2, ihy.1, ihy.2, ihz.1, ihz.2] <;> rfl

/-- **An equation's two readings, the same** (`sameAt`): one term in one
context with the same keys, read with the same symbols, lowers alike. -/
theorem sameAt_toLS {Γ Δ : Ctx} {ρa ρb : SymS} {p q : PrimTy} {a : Tm C Γ (.val p)}
    {b : Tm C Δ (.val q)}
    (h : sameAt ρa a ρb b = true) (hs : ρa.sym = ρb.sym) (hoka : ρa.Ok ρa.names)
    (hokb : ρb.Ok ρb.names) : b.toLS ρb = a.toLS ρa ∧ b.inLS ρb = a.inLS ρa := by
  unfold sameAt at h
  split at h
  · rename_i e _
    subst e
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨-, hn⟩, hb⟩ := h
    have hab := Tm.sigma_eq_of_beqR hb
    simp only [Sigma.mk.injEq, Srt.val.injEq] at hab
    obtain ⟨rfl, hab⟩ := hab
    cases hab
    have hl : ρb.loc = ρa.loc := by
      unfold SymS.Ok at hoka hokb
      rw [hokb, hoka, hn, hs]
    rw [Tm.toLS_eq_toLSM, Tm.toLS_eq_toLSM, Tm.inLS_eq_inLSM, Tm.inLS_eq_inLSM]
    exact Tm.toLSM_congr hl hs.symm a
  · cases h

/-- What `eqDViewS` recognises: `defined a ∧ (defined b ∧ a' = b')`
through peeled constructors, `a'` and `b'` the same terms as `a` and `b`. -/
theorem eqDViewS_spec {Γ : Ctx} {ρ : SymS} {φ ψ : Fml C Γ}
    {A B : (Γ' : Ctx) × SymS × (p : PrimTy) × Tm C Γ' (.val p)}
    (h : eqDViewS ρ φ ψ = some (A, B)) :
    φ.peelS ρ = ⟨A.1, A.2.1, .defined A.2.2.2⟩ ∧
      ∃ (Γ' : Ctx) (ρ' : SymS) (ψ₁ ψ₂ : Fml C Γ'), ψ.peelS ρ = ⟨Γ', ρ', .and ψ₁ ψ₂⟩ ∧
        ψ₁.peelS ρ' = ⟨B.1, B.2.1, .defined B.2.2.2⟩ ∧
        ∃ (Γc : Ctx) (ρc : SymS) (pc : PrimTy) (a' b' : Tm C Γc (.val pc)),
          ψ₂.peelS ρ' = ⟨Γc, ρc, .eq a' b'⟩ ∧
          sameAt A.2.1 A.2.2.2 ρc a' = true ∧ sameAt B.2.1 B.2.2.2 ρc b' = true := by
  unfold eqDViewS at h
  dsimp only at h
  split at h
  · rename_i pa a₀ ψ₁ ψ₂ ha hb
    split at h
    · rename_i pb b₀ pc a' b' h₁ h₂
      split at h
      · rename_i hs
        simp only [Bool.and_eq_true] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, (ψ.peelS ρ).1, (ψ.peelS ρ).2.1, ψ₁, ψ₂, ?_, ?_,
          (ψ₂.peelS (ψ.peelS ρ).2.1).1, (ψ₂.peelS (ψ.peelS ρ).2.1).2.1, _, a', b', ?_, hs.1, hs.2⟩
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

/-- `defined t` holds where the erased reading returns. -/
theorem Tm.evalE_defined_iff {p : PrimTy} (τ : State C Γ) (t : Tm C Γ (.val p)) :
    holds τ (.defined t) ↔ ∃ x, t.evalE τ = .ok x := by
  show t.eval τ ≠ none ↔ _
  rw [Tm.evalE_def]
  cases t.eval τ with
  | none => simp only [ne_eq, not_true_eq_false, toRes, reduceCtorEq, exists_false]
  | some v => simp only [ne_eq, reduceCtorEq, not_false_eq_true, toRes, Except.ok.injEq,
      exists_eq']

/-- A literal, `msg.sender` or a local reads a value. -/
theorem Tm.eval_of_atomLike {p : PrimTy} {t : Tm C Γ (.val p)} (τ : State C Γ)
    (h : t.isLitLikeS = true ∨ t.isAtomS = true) : ∃ x, t.evalE τ = .ok x := by
  cases t with
  | app0 o => cases o <;> exact ⟨_, rfl⟩
  | pvV i => exact ⟨_, rfl⟩
  | _ => rcases h with h | h <;> simp only [Tm.isLitLikeS, Tm.isAtomS, Bool.false_eq_true] at h

/-- Between two terms that return, the equation is equality of the
values. -/
theorem holds_eq_of_eval {τ : State C Γ} {p : PrimTy} {a b : Tm C Γ (.val p)} {x y : Value}
    (ha : a.evalE τ = .ok x) (hb : b.evalE τ = .ok y) :
    holds τ (.eq a b) ↔ x = y := by
  rw [Tm.evalE_def] at ha hb
  cases ha' : a.eval τ with
  | none => rw [ha'] at ha; cases ha
  | some x' =>
    cases hb' : b.eval τ with
    | none => rw [hb'] at hb; cases hb
    | some y' =>
      rw [ha'] at ha
      rw [hb'] at hb
      cases ha
      cases hb
      show a.denote τ = b.denote τ ↔ _
      rw [Tm.denote_eval τ a x' ha', Tm.denote_eval τ b y' hb', Option.some.injEq]
      exact ⟨fun h => h ▸ rfl, fun h => PrimTy.erase_injective h⟩

/-- **An equation through peeled constructors** (`eqDViewS`): both
readings return one value, read in every typed state the peels reach. -/
theorem eqD_sound {φ ψ : Fml C Γ} {σ : Semantics.State} {ρ : SymS}
    {τ : State C Γ} (h : RelT σ ρ τ) {Γa Γb : Ctx} {ρa ρb : SymS} {pa pb : PrimTy}
    {a : Tm C Γa (.val pa)} {b : Tm C Γb (.val pb)}
    (hv : eqDViewS ρ φ ψ = some (⟨Γa, ρa, pa, a⟩, ⟨Γb, ρb, pb, b⟩))
    (ha : a.inLS ρa = true) (hb : b.inLS ρb = true) :
    holds τ (.and φ ψ) ↔ (LFml.eq (a.toLS ρa) (b.toLS ρb)).holds σ := by
  obtain ⟨hpa, Γ', ρ', ψ₁, ψ₂, hpb, hp₁, Γc, ρc, pc, a', b', hp₂, hsa, hsb⟩ := eqDViewS_spec hv
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
  have A2 : ∀ τa' : State C Γa, RelT σ ρa τa' →
      Sim ((a.toLS ρa).eval σ) (a.evalE τa') := fun _ hr => hr.val ha
  have B2 : ∀ τb' : State C Γb, RelT σ ρb τb' →
      Sim ((b.toLS ρb).eval σ) (b.evalE τb') := fun _ hr => hr.val hb
  have A3 : ∀ τc' : State C Γc, RelT σ ρc τc' →
      Sim ((a.toLS ρa).eval σ) (a'.evalE τc') := by
    intro τc' hr
    rw [← ea.1]
    exact hr.val (by rw [ea.2]; exact ha)
  have B3 : ∀ τc' : State C Γc, RelT σ ρc τc' →
      Sim ((b.toLS ρb).eval σ) (b'.evalE τc') := by
    intro τc' hr
    rw [← eb.1]
    exact hr.val (by rw [eb.2]; exact hb)
  rw [LFml.holds_eq_iff]
  constructor
  · rintro ⟨hφ, hψ⟩
    obtain ⟨τa', hra', hda⟩ := peel_neg φ hpa τ h hφ
    obtain ⟨τ₂, hr₂, hψ₁, hψ₂⟩ := peel_neg ψ hpb τ h hψ
    obtain ⟨τb', hrb', hdb⟩ := peel_neg ψ₁ hp₁ τ₂ hr₂ hψ₁
    obtain ⟨τc', hrc', hc⟩ := peel_neg ψ₂ hp₂ τ₂ hr₂ hψ₂
    obtain ⟨x, hx⟩ := (Tm.evalE_defined_iff τa' a).1 hda
    obtain ⟨y, hy⟩ := (Tm.evalE_defined_iff τb' b).1 hdb
    have hx' := (A2 τa' hra' x).2 hx
    have hy' := (B2 τb' hrb' y).2 hy
    have hxy := (holds_eq_of_eval ((A3 τc' hrc' x).1 hx') ((B3 τc' hrc' y).1 hy')).1 hc
    subst hxy
    exact ⟨x, hx', hy'⟩
  · rintro ⟨x, hx, hy⟩
    refine ⟨peel_pos φ hpa τ h fun τa' hra' => (Tm.evalE_defined_iff τa' a).2 ⟨x, (A2 τa' hra' x).1 hx⟩,
      peel_pos ψ hpb τ h fun τ₂ hr₂ => ⟨peel_pos ψ₁ hp₁ τ₂ hr₂ fun τb' hrb' =>
        (Tm.evalE_defined_iff τb' b).2 ⟨x, (B2 τb' hrb' x).1 hy⟩, peel_pos ψ₂ hp₂ τ₂ hr₂ fun τc' hrc' =>
        (holds_eq_of_eval ((A3 τc' hrc' x).1 hx) ((B3 τc' hrc' x).1 hy)).2 rfl⟩⟩

/-- An element's terms return, read in the typed state. -/
def ElemS.okT (τ : State C Γ) : ElemS C Γ → Bool
  | .rhs r => (r.eval τ).isSome
  | .glob e => e.okB τ

/-- An element out of gas, read in the typed state (`UpdElem.exhB`). -/
def ElemS.exhT (τ : State C Γ) : ElemS C Γ → Bool
  | .rhs r => r.exhB τ
  | .glob e => e.exhB τ

theorem toElemS_okT {Δ : Ctx} (τ : State C Γ) (e : UpdElem C Γ Δ) :
    e.toElemS.okT τ = e.okB τ := by
  cases e <;> rfl

theorem toElemS_exhT {Δ : Ctx} (τ : State C Γ) (e : UpdElem C Γ Δ) :
    e.toElemS.exhT τ = e.exhB τ := by
  cases e <;> rfl

theorem toElemS_guard {Δ : Ctx} (ρ : SymS) (e : UpdElem C Γ Δ) :
    e.toElemS.guard ρ = (ElemS.glob e).guard ρ := by
  cases e <;> rfl

theorem toElemS_inLS {Δ : Ctx} (ρ : SymS) (e : UpdElem C Γ Δ) :
    e.toElemS.inLS ρ = (ElemS.glob e).inLS ρ := by
  cases e <;> rfl

/-- An update with no element is never out of gas. -/
theorem Upd.exh_view_zero (τ : State C Γ) : {Δ : Ctx} → (U : Upd C Γ Δ) → U.view = .zero →
    U.exhAny τ = false ∧ U.exhOk τ = true
  | _, .nil, _ => ⟨rfl, rfl⟩
  | _, .snoc U e, hv => by
    change U.view.add e.toElemS = .zero at hv
    generalize U.view = w at hv
    cases w <;> simp only [UView.add, reduceCtorEq] at hv
  | _, .decl U _ r, hv => by
    change U.view.add (.rhs r) = .zero at hv
    generalize U.view = w at hv
    cases w <;> simp only [UView.add, reduceCtorEq] at hv
  | _, .pop U _, hv => Upd.exh_view_zero τ U hv
  | _, .drop U _, hv => Upd.exh_view_zero τ U hv

/-- An update of one element is out of gas where the element is. -/
theorem Upd.exh_view_one (τ : State C Γ) {a : ElemS C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) →
    U.view = .one a → U.exhAny τ = a.exhT τ ∧ U.exhOk τ = (a.okT τ || a.exhT τ)
  | _, .nil, hv => UView.noConfusion hv
  | _, .snoc U e, hv => by
    obtain ⟨hz, rfl⟩ := UView.add_eq_one hv
    obtain ⟨h₁, h₂⟩ := Upd.exh_view_zero τ U hz
    simp only [Upd.exhAny, Upd.exhOk, h₁, h₂, toElemS_okT, toElemS_exhT, Bool.false_or,
      Bool.true_and, and_self]
  | _, .decl U _ r, hv => by
    obtain ⟨hz, rfl⟩ := UView.add_eq_one hv
    obtain ⟨h₁, h₂⟩ := Upd.exh_view_zero τ U hz
    simp only [Upd.exhAny, Upd.exhOk, h₁, h₂, ElemS.okT, ElemS.exhT, Bool.false_or,
      Bool.true_and, and_self]
  | _, .pop U _, hv => Upd.exh_view_one τ U hv
  | _, .drop U _, hv => Upd.exh_view_one τ U hv

/-- An update of two elements is out of gas where one is and the other
returns or is out of gas. -/
theorem Upd.exh_view_two (τ : State C Γ) {a b : ElemS C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) →
    U.view = .two a b → U.exhAny τ = (a.exhT τ || b.exhT τ) ∧
      U.exhOk τ = ((a.okT τ || a.exhT τ) && (b.okT τ || b.exhT τ))
  | _, .nil, hv => UView.noConfusion hv
  | _, .snoc U e, hv => by
    obtain ⟨hz, rfl⟩ := UView.add_eq_two hv
    obtain ⟨h₁, h₂⟩ := Upd.exh_view_one τ U hz
    simp only [Upd.exhAny, Upd.exhOk, h₁, h₂, toElemS_okT, toElemS_exhT, and_self]
  | _, .decl U _ r, hv => by
    obtain ⟨hz, rfl⟩ := UView.add_eq_two hv
    obtain ⟨h₁, h₂⟩ := Upd.exh_view_one τ U hz
    simp only [Upd.exhAny, Upd.exhOk, h₁, h₂, ElemS.okT, ElemS.exhT, and_self]
  | _, .pop U _, hv => Upd.exh_view_two τ U hv
  | _, .drop U _, hv => Upd.exh_view_two τ U hv

/-- An element at the update's own scope whose guard returns returns. -/
theorem guard_okT_at {σ : Semantics.State} {ρ : SymS} {τ : State C Γ} (h : RelT σ ρ τ)
    (e : UpdElem C Γ Γ) (ha : e.toElemS.inLS ρ = true) (hg : Rets ((e.toElemS.guard ρ).eval σ))
    (hR : e.toElemS.RoomE τ) : e.okB τ = true := by
  obtain ⟨τ', h'⟩ := ((RelU.one h ((Upd.nil (C := C) (Γ := Γ)).snoc e) rfl ha).1.1 ⟨hg, hR⟩)
  obtain ⟨q, hq, -⟩ := applyVE_ok h'
  have hg' := (Upd.applyV_ok _ hq).1
  change (some τ.globG).bind (e.globT τ) = _ at hg'
  rw [Option.bind_some] at hg'
  rw [← UpdElem.globT_isSome τ e τ.globG, hg']
  rfl

/-- **An element whose guard returns returns** in every typed state the
symbolic one stands for. -/
theorem guard_okT {σ : Semantics.State} {ρ : SymS} {τ : State C Γ} (h : RelT σ ρ τ)
    (a : ElemS C Γ) (ha : a.inLS ρ = true) (hg : Rets ((a.guard ρ).eval σ)) (hR : a.RoomE τ) :
    a.okT τ = true := by
  have hrhs : ∀ {t : LTy} (r : Rhs C Γ t), r.inLS ρ = true → Rets ((r.guardS ρ).eval σ) →
      r.RoomR τ → (r.eval τ).isSome = true := fun r ha hg hR => by
    obtain ⟨τ', h'⟩ :=
      ((RelU.one h ((Upd.nil (C := C) (Γ := Γ)).decl (.user "_") r) rfl ha).1.1 ⟨hg, hR⟩)
    obtain ⟨q, hq, -⟩ := applyVE_ok h'
    have hg' := (Upd.applyV_ok _ hq).1
    change (some τ.globG).bind (fun g => (r.eval τ).bind fun _ => some g) = _ at hg'
    simp only [Option.bind_some] at hg'
    cases hr : r.eval τ with
    | none => rw [hr] at hg'; cases hg'
    | some _ => rfl
  cases a with
  | rhs r => exact hrhs r ha hg hR
  | glob e =>
    cases e with
    | «local» _ r => exact hrhs r ha hg hR
    | storage x => exact guard_okT_at h (.storage x) ha hg hR
    | memory x => exact guard_okT_at h (.memory x) ha hg hR
    | selfBalance op x => exact guard_okT_at h (.selfBalance op x) ha hg hR
    | net r op x => exact guard_okT_at h (.net r op x) ha hg hR
    | pay r x => exact guard_okT_at h (.pay r x) ha hg hR
    | netMt r x => exact guard_okT_at h (.netMt r x) ha hg hR
    | setBalance x => exact guard_okT_at h (.setBalance x) ha hg hR

theorem sok_rets {σ : Semantics.State} {X : LStor} (h : Rets ((LTerm.sok X).eval σ)) :
    ∃ a, X.eval σ = .ok a := by
  obtain ⟨v, hv⟩ := h
  simp only [LTerm.eval] at hv
  obtain ⟨a, ha, -⟩ := Res.bind_eq_ok.1 hv
  exact ⟨a, ha⟩

/-- **An element whose terms return returns, or is out of gas**: where its
push has no room (`ElemS.RoomE`), the push is at a full array. -/
theorem guard_cases {σ : Semantics.State} {ρ : SymS} {τ : State C Γ} (h : RelT σ ρ τ)
    (a : ElemS C Γ) (ha : a.inLS ρ = true) (hg : Rets ((a.guard ρ).eval σ)) :
    (Rets ((a.guard ρ).eval σ) ∧ a.RoomE τ) ∨ a.exhT τ = true := by
  by_cases hR : a.RoomE τ
  · exact .inl ⟨hg, hR⟩
  · refine .inr ?_
    have hrhs : ∀ {t : LTy} (r : Rhs C Γ t), r.inLS ρ = true → Rets ((r.guardS ρ).eval σ) →
        ¬ r.RoomR τ → r.exhB τ = true := fun r hr hg hR => by
      cases r with
      | store s =>
        obtain ⟨x, hx⟩ := sok_rets hg
        rw [Tm.toLS_eq_toLSM] at hx
        exact h.stor_exh s (by rw [← Tm.inLS_eq_inLSM]; exact hr) ⟨x, hx⟩ hR
      | _ => exact absurd trivial hR
    cases a with
    | rhs r => exact hrhs r ha hg hR
    | glob e =>
      cases e with
      | «local» _ r => exact hrhs r ha hg hR
      | storage s => exact h.storT_exh s ha hg hR
      | _ => exact absurd trivial hR

/-- **An element that returns has the room its pushes read** (`ElemS.bound`). -/
theorem bound_true {σ : Semantics.State} {ρ : SymS} {τ : State C Γ} (h : RelT σ ρ τ)
    (a : ElemS C Γ) (ha : a.inLS ρ = true) (hok : a.okT τ = true) :
    (a.bound ρ).eval σ = .ok (.bool true) := by
  have hrhs : ∀ {t : LTy} (r : Rhs C Γ t), r.inLS ρ = true → (r.eval τ).isSome = true →
      (r.boundR ρ).eval σ = .ok (.bool true) := fun r hr hok => by
    cases r with
    | store s =>
      rw [CloseS.rhs_store] at hok
      exact h.bound_of_ok s (by rw [← Tm.inLS_eq_inLSM]; exact hr) hok
    | _ => rfl
  cases a with
  | rhs r => exact hrhs r ha hok
  | glob e =>
    cases e with
    | «local» _ r => exact hrhs r ha hok
    | storage s => exact h.boundSt_of_ok s ha hok
    | _ => rfl

/-- What follows an update, read past the room its pushes have. -/
theorem roomM_holds {σ : Semantics.State} (m : Modality) {b : LTerm} {φ : LFml}
    (h : (roomM m b φ).holds σ) (hb : b.eval σ = .ok (.bool true)) : φ.holds σ := by
  cases m with
  | box => exact h
  | diamond =>
    cases b with
    | lit _ => exact h
    | _ => exact h ((LFml.holds_eq_iff _ _ _).2 ⟨_, hb, rfl⟩)

/-- An update of one element that returns: the element returns. -/
theorem okT_of_view_one {τ : State C Γ} {a : ElemS C Γ} {Δ : Ctx} {U : Upd C Γ Δ}
    (hv : U.view = .one a) {q : GlobT C τ.H × LocsV C Δ} (hap : U.applyV τ = some q) :
    a.okT τ = true := by
  have hg := (Upd.applyV_ok U hap).1
  have h₁ := Upd.exhAny_of_globT hg
  have h₂ := Upd.exhOk_of_globT U hg
  obtain ⟨e₁, e₂⟩ := Upd.exh_view_one τ U hv
  rw [e₁] at h₁
  rw [e₂, h₁, Bool.or_false] at h₂
  exact h₂

/-- An update of two elements that returns: each returns. -/
theorem okT_of_view_two {τ : State C Γ} {a b : ElemS C Γ} {Δ : Ctx} {U : Upd C Γ Δ}
    (hv : U.view = .two a b) {q : GlobT C τ.H × LocsV C Δ} (hap : U.applyV τ = some q) :
    a.okT τ = true ∧ b.okT τ = true := by
  have hg := (Upd.applyV_ok U hap).1
  have h₁ := Upd.exhAny_of_globT hg
  have h₂ := Upd.exhOk_of_globT U hg
  obtain ⟨e₁, e₂⟩ := Upd.exh_view_two τ U hv
  rw [e₁, Bool.or_eq_false_iff] at h₁
  rw [e₂, h₁.1, h₁.2, Bool.or_false, Bool.or_false, Bool.and_eq_true] at h₂
  exact h₂

/-- **The scoped reduction is sound**, over the typed state, at the
polarity `pos`: where the fragment takes a formula, its reduction read in
`σ` gives the formula in every typed state `ρ` stands for (positive), and
the formula gives its reduction (negative, where it is first-order). -/
theorem _root_.Solidity.Fml.toLSM_sound : ∀ {Γ : Ctx} (φ : Fml C Γ) (pos : Bool)
    {σ : Semantics.State} {ρ : SymS} (τ : State C Γ),
    RelT σ ρ τ → φ.inLSM pos ρ = true →
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
      obtain ⟨x, hx⟩ := Tm.eval_of_atomLike τ hab.1
      obtain ⟨y, hy⟩ := Tm.eval_of_atomLike τ hab.2
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
      rw [holds_eq_self, Tm.evalE_defined_iff]
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
      obtain ⟨⟨Γa, ρa, pa, a⟩, ⟨Γb, ρb, pb, b⟩⟩ := AB
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
    show U.afterT m τ (holds · φ)
    rw [Upd.afterT_applyV]
    cases hv : U.view with
    | zero =>
      simp only [Fml.toLSM, hv] at hL
      simp only [hv] at hf
      obtain ⟨τe, hτ, h', -⟩ := RelU.zero noActE noActR h U hv
      obtain ⟨q, hq, rfl⟩ := applyVE_ok hτ
      rw [hq]
      intro σ' hg hl
      exact (ih true σ' (RelT.of_lands h' hg hl) hf).1 rfl hL
    | one a =>
      simp only [Fml.toLSM, hv] at hL
      simp only [hv, Bool.and_eq_true] at hf
      obtain ⟨hg, hr⟩ := RelU.one h U hv hf.1
      cases hap : U.applyV τ with
      | none =>
        cases m with
        | box => exact .inl trivial
        | diamond =>
          rw [guardM_diamond] at hL
          rcases guard_cases h a hf.1 hL.1 with hgr | hx
          · obtain ⟨τ', h'⟩ := hg.1 hgr
            exact absurd h' (applyVE_none hap τ')
          · refine .inr ?_
            obtain ⟨h₁, h₂⟩ := Upd.exh_view_one τ U hv
            simp only [Upd.exh, h₁, h₂, hx, Bool.or_true, Bool.and_self]
      | some q =>
        intro σ' hg' hl
        have hap' : U.applyVE τ = .ok (eraseQ q) := by rw [Upd.applyVE_eq, hap]; rfl
        have hgret := hg.2 ⟨_, hap'⟩
        have hL' : (φ.toLSM (U.replayS (UpdElem.actS ρ) (fun r => .ofOpt (r.actS ρ)) ρ)).holds σ := by
          have hb := bound_true h a hf.1 (okT_of_view_one hv hap)
          cases m with
          | box => exact (guardM_box σ _ _).1 hL hgret.1
          | diamond => exact roomM_holds .diamond ((guardM_diamond σ _ _).1 hL).2 hb
        exact (ih true σ' (RelT.of_lands (hr _ hap') hg' hl) hf.2).1 rfl hL'
    | two a b =>
      simp only [Fml.toLSM, hv] at hL
      simp only [hv] at hf
      cases hp : pairViewS a b with
      | none =>
        simp only [hp, Bool.and_eq_true] at hf hL
        obtain ⟨hg, hr⟩ := RelU.par h U hv hf.1
        cases hap : U.applyV τ with
        | none =>
          cases m with
          | box => exact .inl trivial
          | diamond =>
            rw [guardM_diamond] at hL
            obtain ⟨hga, hgb⟩ := (seqL_rets σ _ _).1 hL.1
            have hpo := hf.1
            simp only [ElemS.parOk, Bool.and_eq_true] at hpo
            have hia : a.inLS ρ = true := hpo.1.1.1
            have hib : b.inLS ρ = true := hpo.1.1.2
            have hca := guard_cases h a hia hga
            have hcb := guard_cases h b hib hgb
            by_cases hboth : (Rets ((a.guard ρ).eval σ) ∧ a.RoomE τ) ∧
                (Rets ((b.guard ρ).eval σ) ∧ b.RoomE τ)
            · obtain ⟨τ', h'⟩ := hg.1 ⟨(seqL_rets σ _ _).2 ⟨hboth.1.1, hboth.2.1⟩, hboth.1.2,
                hboth.2.2⟩
              exact absurd h' (applyVE_none hap τ')
            · refine .inr ?_
              have hoka : (a.okT τ || a.exhT τ) = true := by
                rcases hca with hx | hx
                · rw [guard_okT h a hia hx.1 hx.2, Bool.true_or]
                · rw [hx, Bool.or_true]
              have hokb : (b.okT τ || b.exhT τ) = true := by
                rcases hcb with hx | hx
                · rw [guard_okT h b hib hx.1 hx.2, Bool.true_or]
                · rw [hx, Bool.or_true]
              have hany : (a.exhT τ || b.exhT τ) = true := by
                rcases hca with hca | hca
                · rcases hcb with hcb | hcb
                  · exact absurd ⟨hca, hcb⟩ hboth
                  · rw [hcb, Bool.or_true]
                · rw [hca, Bool.true_or]
              obtain ⟨h₁, h₂⟩ := Upd.exh_view_two τ U hv
              simp only [Upd.exh, h₁, h₂, hany, hoka, hokb, Bool.and_self]
        | some q =>
          intro σ' hg' hl
          have hap' : U.applyVE τ = .ok (eraseQ q) := by rw [Upd.applyVE_eq, hap]; rfl
          have hgret := hg.2 ⟨_, hap'⟩
          have hL' : (φ.toLSM (U.replayS (UpdElem.actS ρ) (fun r => .ofOpt (r.actS ρ)) ρ)).holds
              σ := by
            have hpo := hf.1
            simp only [ElemS.parOk, Bool.and_eq_true] at hpo
            obtain ⟨hoa, hob⟩ := okT_of_view_two hv hap
            cases m with
            | box => exact (guardM_box σ _ _).1 hL hgret.1
            | diamond =>
              exact roomM_holds .diamond (roomM_holds .diamond ((guardM_diamond σ _ _).1 hL).2
                (bound_true h a hpo.1.1.1 hoa)) (bound_true h b hpo.1.1.2 hob)
          exact (ih true σ' (RelT.of_lands (hr _ hap') hg' hl) hf.2).1 rfl hL'
      | some p =>
        obtain ⟨R, i, mm⟩ := p
        cases hq : pairLS ρ i mm with
        | none => simp only [hp, hq, Bool.false_eq_true] at hf
        | some q =>
          obtain ⟨g, M⟩ := q
          simp only [hp, hq, Bool.and_eq_true] at hf hL
          obtain ⟨hg, hr⟩ := RelU.two h hq hf.1.1 U hv hp
          cases hap : U.applyV τ with
          | none =>
            cases m with
            | box => exact .inl trivial
            | diamond =>
              rw [guardM_diamond] at hL
              obtain ⟨τ', h'⟩ := hg.1 hL.1
              exact absurd h' (applyVE_none hap τ')
          | some q =>
            intro σ' hg' hl
            have hap' : U.applyVE τ = .ok (eraseQ q) := by rw [Upd.applyVE_eq, hap]; rfl
            have hgret : ∃ v, g.eval σ = .ok v := hg.2 ⟨_, hap'⟩
            have hL' : (φ.toLSM (U.replayS (pairActE ρ M) (pairActR ρ) ρ)).holds σ := by
              cases m with
              | box => exact (guardM_box σ _ _).1 hL hgret
              | diamond => exact ((guardM_diamond σ _ _).1 hL).2
            exact (ih true σ' (RelT.of_lands (hr _ hap') hg' hl) hf.2).1 rfl hL'
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
    · exact (ih pos (τ.push v) (RelT.push (h.pushQ hx (PrimTy.erase v)))
        hf).1 hp (hL _ (PrimTy.admits_erase v))
    · obtain ⟨v, rfl⟩ := PrimTy.exists_of_admits hw
      exact (ih pos (τ.push v) (RelT.push (h.pushQ hx (PrimTy.erase v)))
        hf).2 hp (hφ v)
  | bind m x t φ ih =>
    intro pos σ ρ τ h hf
    simp only [Fml.inLSM, Bool.and_eq_true] at hf
    obtain ⟨rfl, hf⟩ := hf
    refine ⟨fun _ hL => ?_, fun hp => Bool.noConfusion hp⟩
    simp only [Fml.toLSM] at hL
    intro v
    exact (ih true (τ.push v) (RelT.push (h.pushFree _)) hf).1 rfl hL

/-- The state a typed state's reduction is read in: its global part, no
local. -/
def _root_.Solidity.State.redState {Γ : Ctx} (τ : State C Γ) : Semantics.State :=
  withLocals τ.globE []

/-- The reduction's start: no update, no local. -/
theorem RelU.empty (τ : State C []) : RelT τ.redState SymS.empty τ :=
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
