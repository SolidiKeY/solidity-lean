import Solidity.Calculus.UpdateRules

/-!
# Update simplification on scoped formulas

`Calculus/NFmlUpdateRules.lean`'s rules (`updateRules.key`) on `Fml C Γ`
and its updates `Upd C Γ Δ`, read over the typed state (`holds`):

| KeY taclet | here | erased form |
|---|---|---|
| `sequentialToParallel1/2/3`: `{u}{u2}φ ⇝ {u ‖ {u}u2}φ` | `UpdRuleS.sequentialToParallel` (`Upd.seqPar`, `Calculus/Graft.lean`) | `UpdRule.sequentialToParallel` |
| `simplifyUpdate1/2/3` (`\dropEffectlessElementaries`) | `UpdRuleS.simplifyUpdate` (`Upd.simp`, `Calculus/UpdateRules.lean`), under the box | `UpdRule.simplifyUpdate` |
| `applySkip1/2/3`: `{skip}φ ⇝ φ` | `UpdRuleS.applySkip` | `UpdRule.applySkip` |
| `applyOnRigidFormula`, `applyOnPV`, `applyOnDifferentPV` | `UpdRuleS.applyOnRigid` (`Fml.substU`) | `UpdRule.applyOnRigid` |

**One way.**  Each rule rewrites `φ` to a `ψ` that gives it
(`UpdRuleS.sound`: `holds σ ψ → holds σ φ`), the direction a derivation
uses.  The erased rules are equivalences; here the converse fails, because
`{U} φ` reads `φ` in every *typed* state the update's result erases to
(`holds`), and a merged update may reach a typed state the two updates in
turn do not: `{x := 300}{x := 1} φ` for a `uint8` local `x` holds
vacuously (no typed state holds `300` in `x`), its merge
`{x := 300 ‖ x := 1} φ` only where `φ` does.  So a rule applies at the
positive positions of a formula only (`Fml.updAtS`, `Fml.simpUpdsS`): under
an update, a conjunction, the right of an implication, a binder, `{havoc}`,
`{anon}` and a modality's postcondition, not under a negation or on the
left of an implication, where the erased form also rewrites.

**What the scope changes.**  An update's locals are positions, so what
the erased `dropEffectless` drops by name splits in two: an element that
sets a local the same update pops later (a capture's `se1`, `sp1`) goes
(`Upd.simp`, under the box, as `Proves.simplify`); an element that sets a
local still in scope that `φ` does not read stays (the erased form drops
it).  `applySkip` asks a formula with no modality (`Fml.modalFree`): such a
formula holds in a typed state by its erasure and its heap typing alone
(`holds_congr_erase`), and the states `{}` reads `φ` in are those.
`applyOnRigid` under the diamond asks an update that cannot halt
(`Upd.totalB`), as the erased form asks `Upd.total`; under the box any
update applies, as `Proves.applyOnRigidBox`.

`elimSelfUpdate` (commented out in solkey; theorems only in the erased
form) is not ported.

The functions use `match` on the indexed families, against Gate G0's first
condition: an exemption, as `Calculus/Graft.lean`'s and
`Calculus/UpdateRules.lean`'s (`docs/intrinsic.md`, W3b, W3c), since they
run once a rule and not once a step.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)

variable {C : Contract}

/-! ## Reading a formula by its erasure -/

/-- **A formula with no modality reads the typed state by its erasure and
its heap typing alone.**  Its atoms read the erasure (`Tm.eval`,
`Tm.denote`), an update the erasure of the state it is applied in, and its
binders push, havoc and anonymise erasure-wise. -/
theorem holds_congr_erase : {Γ : Ctx} → (φ : Fml C Γ) → φ.modalFree = true →
    (σ σ' : State C Γ) → σ.H = σ'.H → σ.erase = σ'.erase → (holds σ φ ↔ holds σ' φ)
  | _, .tt, _, _, _, _, _ => Iff.rfl
  | _, .eq a b, _, σ, σ', _, he => by
    show Theory.StValue.Equiv (a.denote σ.erase) (b.denote σ.erase) ↔
      Theory.StValue.Equiv (a.denote σ'.erase) (b.denote σ'.erase)
    rw [he]
  | _, .defined t, _, σ, σ', _, he => by
    show (∃ x, t.eval σ.erase = .ok x) ↔ (∃ x, t.eval σ'.erase = .ok x)
    rw [he]
  | _, .not φ, hm, σ, σ', hH, he => not_congr (holds_congr_erase φ hm σ σ' hH he)
  | _, .and φ ψ, hm, σ, σ', hH, he => by
    have hm : φ.modalFree = true ∧ ψ.modalFree = true := Bool.and_eq_true_iff.mp hm
    exact and_congr (holds_congr_erase φ hm.1 σ σ' hH he) (holds_congr_erase ψ hm.2 σ σ' hH he)
  | _, .imp φ ψ, hm, σ, σ', hH, he => by
    have hm : φ.modalFree = true ∧ ψ.modalFree = true := Bool.and_eq_true_iff.mp hm
    exact imp_congr (holds_congr_erase φ hm.1 σ σ' hH he) (holds_congr_erase ψ hm.2 σ σ' hH he)
  | _, .upd m U φ, _, σ, σ', hH, he => by
    show m.afterC (fun τ => ∀ σ'' : State C _, σ''.erase = τ → σ.H <+: σ''.H → holds σ'' φ)
        (U.apply σ.erase) ↔
      m.afterC (fun τ => ∀ σ'' : State C _, σ''.erase = τ → σ'.H <+: σ''.H → holds σ'' φ)
        (U.apply σ'.erase)
    rw [he, hH]
  | _, .modal .., hm, _, _, _, _ => absurd hm Bool.false_ne_true
  | _, .havoc φ, hm, σ, σ', hH, he => by
    show (∀ st nt, holds (σ.havoc st nt) φ) ↔ (∀ st nt, holds (σ'.havoc st nt) φ)
    refine forall_congr' fun st => forall_congr' fun nt => holds_congr_erase φ hm _ _ hH ?_
    rw [State.havoc_erase, State.havoc_erase, he]
  | _, .all _ p φ, hm, σ, σ', hH, he => by
    show (∀ v : p.Denote, holds (σ.push (t := .val p) v) φ) ↔
      (∀ v : p.Denote, holds (σ'.push (t := .val p) v) φ)
    refine forall_congr' fun v => holds_congr_erase φ hm _ _ hH ?_
    rw [State.push_erase, State.push_erase, he]; rfl
  | _, .bind m _ t φ, hm, σ, σ', hH, he => by
    obtain ⟨st, H, hp, env, nt, sb, tx⟩ := σ
    obtain ⟨st', H', hp', env', nt', sb', tx'⟩ := σ'
    cases hH
    refine forall_congr' fun v => holds_congr_erase φ hm _ _ rfl ?_
    rw [State.push_erase, State.push_erase, he]
  | _, .anon xs φ, hm, σ, σ', hH, he => by
    obtain ⟨st, H, hp, env, nt, sb, tx⟩ := σ
    obtain ⟨st', H', hp', env', nt', sb', tx'⟩ := σ'
    cases hH
    refine forall_congr' fun b => holds_congr_erase φ hm _ _ rfl ?_
    rw [State.anon_erase, State.anon_erase, he]

/-- Two typed states of one erasure, the heap typing of one a prefix of the
other's, have one heap typing: the erasure's next identity is its length. -/
theorem State.H_eq_of_erase {Γ : Ctx} {σ σ' : State C Γ} (he : σ'.erase = σ.erase)
    (hp : σ.H <+: σ'.H) : σ.H = σ'.H := by
  have hl : σ'.H.length = σ.H.length := congrArg EState.nextId he
  exact hp.sublist.eq_of_length hl.symm

/-- `{} φ` holds where `φ` does, for `φ` with no modality. -/
theorem holds_upd_nil {Γ : Ctx} (m : Modality) {φ : Fml C Γ} (hm : φ.modalFree = true)
    (σ : State C Γ) : holds σ (.upd m .nil φ) ↔ holds σ φ := by
  show m.afterC (fun τ => ∀ σ' : State C Γ, σ'.erase = τ → σ.H <+: σ'.H → holds σ' φ)
    (pure σ.erase) ↔ holds σ φ
  refine ⟨fun h => h σ rfl (List.prefix_refl _), fun h σ' he hp => ?_⟩
  exact (holds_congr_erase φ hm σ σ' (State.H_eq_of_erase he hp) he.symm).1 h

/-! ## Updates read one way -/

/-- What gives `φ` after an update gives it after the update. -/
theorem holds_upd_mono {Γ Δ : Ctx} {m : Modality} {U : Upd C Γ Δ} {φ ψ : Fml C Δ}
    (hφ : ∀ τ, holds τ ψ → holds τ φ) (σ : State C Γ) (h : holds σ (.upd m U ψ)) :
    holds σ (.upd m U φ) :=
  Modality.afterC_imp (p := fun τ => ∀ σ' : State C Δ, σ'.erase = τ → σ.H <+: σ'.H → holds σ' ψ)
    h fun _ h' σ' he hp => hφ σ' (h' σ' he hp)

/-- What gives `φ` after a run gives it after the run. -/
theorem _root_.Solidity.Modality.afterRunTR_imp {α : Type} {m : Modality} {p q : α → Prop}
    {r : TRes α} (h : m.afterRunTR p r) (hpq : ∀ a, p a → q a) : m.afterRunTR q r := by
  cases r with
  | ok a => exact ⟨hpq a h.1, h.2⟩
  | error _ => exact h

/-- **An update that runs as two in turn gives the two**: `{W} φ` gives
`{U}{V} φ` under the modality of both.  `Calculus/Graft.lean`'s
`holds_upd_graft`, for any `W` whose run is `U`'s then `V`'s. -/
theorem holds_upd_of_apply {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} {φ : Fml C Δ₂} (σ : State C Γ)
    (hg : W.apply σ.erase = (U.apply σ.erase >>= V.apply))
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) := by
  show m.afterC
    (fun τ => ∀ σ' : State C _, σ'.erase = τ → σ.H <+: σ'.H → holds σ' (.upd m V φ))
    (U.apply σ.erase)
  have h : m.afterC (fun τ => ∀ σ' : State C _, σ'.erase = τ → σ.H <+: σ'.H → holds σ' φ)
    (W.apply σ.erase) := h
  rw [hg] at h
  cases hU : U.apply σ.erase with
  | error e => rw [hU] at h; exact h
  | ok σ₁ =>
    rw [hU] at h
    intro σ' he hext
    show m.afterC _ (V.apply σ'.erase)
    rw [he]
    exact Modality.afterC_imp h fun τ h σ'' e₂ hext₂ => h σ'' e₂ (hext.trans hext₂)

/-! ## Updates that cannot halt -/

/-- A value that cannot halt: a local, a literal. -/
def Tm.totalB {Γ : Ctx} : Tm C Γ .val → Bool
  | .pvV _ => true
  | .app0 (.lit _) => true
  | _ => false

/-- A right-hand side that cannot halt. -/
def Rhs.totalB {Γ : Ctx} : {t : LTy} → Rhs C Γ t → Bool
  | _, .val t => t.totalB
  | _, .unset | _, .saveNet | _, .saveNetMt => true
  | _, _ => false

/-- An update that cannot halt: it sets and declares locals to what cannot
halt, and pops (the erased form's `Upd.total`). -/
def Upd.totalB {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => true
  | _, .snoc U (.local _ r) => Upd.totalB U && r.totalB
  | _, .snoc _ _ => false
  | _, .decl U _ r => Upd.totalB U && r.totalB
  | _, .pop U _ | _, .drop U _ => Upd.totalB U

theorem Tm.totalB_eval {Γ : Ctx} (σ : EState C Γ) :
    (t : Tm C Γ .val) → t.totalB = true → ∃ v, t.eval σ = .ok v
  | .pvV _, _ => ⟨_, rfl⟩
  | .app0 (.lit v), _ => ⟨v, rfl⟩

theorem Rhs.totalB_eval {Γ : Ctx} (σ : EState C Γ) :
    {t : LTy} → (r : Rhs C Γ t) → r.totalB = true → ∃ v, r.eval σ = .ok v
  | _, .val t, h => Tm.totalB_eval σ t h
  | _, .unset, _ => ⟨_, rfl⟩
  | _, .saveNet, _ => ⟨_, rfl⟩
  | _, .saveNetMt, _ => ⟨_, rfl⟩

/-- An update that cannot halt runs. -/
theorem Upd.totalB_apply {Γ : Ctx} (σ₀ : EState C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → U.totalB = true → ∃ σ₁, U.apply σ₀ = .ok σ₁
  | _, .nil, _ => ⟨σ₀, rfl⟩
  | _, .snoc U (.local i r), h => by
    have h : U.totalB = true ∧ r.totalB = true := Bool.and_eq_true_iff.mp h
    obtain ⟨τ, hτ⟩ := Upd.totalB_apply σ₀ U h.1
    obtain ⟨v, hv⟩ := Rhs.totalB_eval σ₀ r h.2
    exact ⟨τ.setLocal i v, by
      change (do UpdElem.write σ₀ (.local i r) (← U.apply σ₀)) = _
      rw [hτ]
      change (do pure (τ.setLocal i (← r.eval σ₀))) = _
      rw [hv]; rfl⟩
  | _, .snoc _ (.storage _), h | _, .snoc _ (.memory _), h | _, .snoc _ (.selfBalance ..), h
  | _, .snoc _ (.net ..), h | _, .snoc _ (.pay ..), h | _, .snoc _ (.netMt ..), h
  | _, .snoc _ (.setBalance _), h => absurd h Bool.false_ne_true
  | _, .decl U _ r, h => by
    have h : U.totalB = true ∧ r.totalB = true := Bool.and_eq_true_iff.mp h
    obtain ⟨τ, hτ⟩ := Upd.totalB_apply σ₀ U h.1
    obtain ⟨v, hv⟩ := Rhs.totalB_eval σ₀ r h.2
    exact ⟨τ.push v, by
      change (do let τ ← U.apply σ₀; pure (τ.push (← r.eval σ₀))) = _
      rw [hτ, hv]; rfl⟩
  | _, .pop U e, h => by
    obtain ⟨τ, hτ⟩ := Upd.totalB_apply σ₀ U h
    exact ⟨τ.drop e, by change (U.apply σ₀).map (EState.drop e) = _; rw [hτ]; rfl⟩
  | _, .drop U e, h => by
    obtain ⟨τ, hτ⟩ := Upd.totalB_apply σ₀ U h
    exact ⟨τ.thin e, by change (U.apply σ₀).map (EState.thin e) = _; rw [hτ]; rfl⟩

/-- **`applyOnRigidFormula`**: a first-order goal read before the update
(`Fml.substU`) gives the update in front of it, under the box for any
update, under the diamond for one that cannot halt. -/
theorem holds_upd_of_substU' {m : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ}
    {φ' : Fml C Γ} (hs : Fml.substU U φ = some φ') (ht : m = .box ∨ U.totalB = true)
    (σ : State C Γ) (h : holds σ φ') : holds σ (.upd m U φ) := by
  show Modality.afterC m _ (U.apply σ.erase)
  cases hU : U.apply σ.erase with
  | error =>
    rcases ht with rfl | ht
    · trivial
    · obtain ⟨_, h'⟩ := Upd.totalB_apply σ.erase U ht
      rw [hU] at h'; cases h'
  | ok σ₁ => exact fun σ' e _ => (Fml.substU_holds hU φ hs σ σ' rfl e).1 h

/-! ## The rules -/

/-- The update rules on scoped formulas, each a rewrite `φ ⇝ ψ` whose `ψ`
gives `φ`.  Hover a constructor for the KeY taclet it is. -/
inductive UpdRuleS : {Γ : Ctx} → Fml C Γ → Fml C Γ → Prop
  /-- `sequentialToParallel2 { \find({u}{u2}phi) \replacewith({u || {u}u2}phi) }`,
  where `{u}u2` reads (`Upd.seqPar`). -/
  | sequentialToParallel {Γ Δ₁ Δ₂ : Ctx} {m : Modality} {u : Upd C Γ Δ₁} {u2 : Upd C Δ₁ Δ₂}
      {w : Upd C Γ Δ₂} {φ : Fml C Δ₂} (hw : u.seqPar u2 = some w) :
      UpdRuleS (.upd m u (.upd m u2 φ)) (.upd m w φ)
  /-- `simplifyUpdate2 { \find({u}phi)
  \varcond(\dropEffectlessElementaries(u, phi, result)) \replacewith(result) }`,
  the elements setting a local `u` pops later, under the box (`Upd.simp`). -/
  | simplifyUpdate {Γ Δ : Ctx} {u : Upd C Γ Δ} {φ : Fml C Δ} :
      UpdRuleS (.upd .box u φ) (.upd .box (u.simp 0) φ)
  /-- `applySkip2 { \find({skip}phi) \replacewith(phi) }`, `phi` with no modality. -/
  | applySkip {Γ : Ctx} {m : Modality} {φ : Fml C Γ} (hm : φ.modalFree = true) :
      UpdRuleS (.upd m .nil φ) φ
  /-- `applyOnRigidFormula { \find({u}phi)
  \varcond(\applyUpdateOnRigid(u, phi, result)) \replacewith(result) }`, and
  `applyOnPV`/`applyOnDifferentPV` on the terms under it (`Fml.substU`);
  under the diamond for `u` that cannot halt. -/
  | applyOnRigid {Γ Δ : Ctx} {m : Modality} {u : Upd C Γ Δ} {φ : Fml C Δ} {φ' : Fml C Γ}
      (hs : Fml.substU u φ = some φ') (ht : m = .box ∨ u.totalB = true) :
      UpdRuleS (.upd m u φ) φ'

/-- **Soundness of the update rules**: what a rule rewrites to gives what
it rewrote.

Example: `x = 1; y = x;` leaves `{ x := 1 } { y := x } y = 1`;
`sequentialToParallel` rewrites it to `{ x := 1 ‖ y := 1 } y = 1`, which
gives it. -/
theorem UpdRuleS.sound {Γ : Ctx} {φ ψ : Fml C Γ} : UpdRuleS φ ψ → ∀ σ, holds σ ψ → holds σ φ
  | .sequentialToParallel hw, σ, h => holds_upd_seqPar hw σ h
  | .simplifyUpdate, σ, h => holds_upd_simp σ h
  | .applySkip hm, σ, h => (holds_upd_nil _ hm σ).2 h
  | .applyOnRigid hs ht, σ, h => holds_upd_of_substU' hs ht σ h

/-! ## One rule at a time -/

/-- The rules, by name (`sol_upd r`). -/
inductive UpdRuleNameS where
  | sequentialToParallel
  | simplifyUpdate
  | applySkip
  | applyOnRigid
  deriving DecidableEq, Repr

/-- The number of elements, pops and frame ends of an update. -/
def Upd.size {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Nat
  | _, .nil => 0
  | _, .snoc U _ | _, .decl U _ _ | _, .pop U _ | _, .drop U _ => U.size + 1

/-- Rule `r` on `{U} φ` under `m`, if it fits and changes something. -/
def UpdRuleNameS.top {Γ Δ : Ctx} : UpdRuleNameS → Modality → Upd C Γ Δ → Fml C Δ →
    Option (Fml C Γ)
  | .sequentialToParallel, m, U, .upd m' V φ =>
    if m' = m then (U.seqPar V).map fun W => .upd m W φ else none
  | .simplifyUpdate, .box, U, φ =>
    if (U.simp 0).size < U.size then some (.upd .box (U.simp 0) φ) else none
  | .applySkip, _, .nil, φ => if φ.modalFree then some φ else none
  | .applyOnRigid, m, U, φ =>
    if m = .box ∨ U.totalB = true then Fml.substU U φ else none
  | _, _, _, _ => none

/-- When rule `r` fits at the top of `{U} φ`, what it returns is an
`UpdRuleS` rewrite of `{U} φ`. -/
theorem UpdRuleNameS.top_rule {Γ Δ : Ctx} {r : UpdRuleNameS} {m : Modality} {U : Upd C Γ Δ}
    {φ : Fml C Δ} {ψ : Fml C Γ} (h : r.top m U φ = some ψ) : UpdRuleS (.upd m U φ) ψ := by
  cases r with
  | sequentialToParallel =>
    cases φ with
    | upd m' V φ =>
      simp only [UpdRuleNameS.top] at h
      split at h
      · rename_i hm; subst hm
        obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 h
        exact .sequentialToParallel hW
      · cases h
    | _ => simp only [UpdRuleNameS.top, reduceCtorEq] at h
  | simplifyUpdate =>
    cases m with
    | box =>
      simp only [UpdRuleNameS.top] at h
      split at h
      · cases h; exact .simplifyUpdate
      · cases h
    | diamond => simp only [UpdRuleNameS.top, reduceCtorEq] at h
  | applySkip =>
    cases U with
    | nil =>
      simp only [UpdRuleNameS.top] at h
      split at h
      · rename_i hm; cases h; exact .applySkip hm
      · cases h
    | _ => simp only [UpdRuleNameS.top, reduceCtorEq] at h
  | applyOnRigid =>
    simp only [UpdRuleNameS.top] at h
    split at h
    · rename_i ht; exact .applyOnRigid h ht
    · cases h

/-- A rewrite of `{U} φ` that gives it. -/
def UpdRw (C : Contract) : Type :=
  {Γ Δ : Ctx} → Modality → Upd C Γ Δ → Fml C Δ → Option (Fml C Γ)

/-- The rewrite `top` gives what it rewrites. -/
def UpdRw.Sound (top : UpdRw C) : Prop :=
  ∀ {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) (ψ : Fml C Γ),
    top m U φ = some ψ → ∀ σ, holds σ ψ → holds σ (.upd m U φ)

/-- `top` at the first update where it fits, outermost first, then left to
right, at the positive positions only: under an update, a conjunction,
the right of an implication, a binder, `{havoc}`, `{anon}` and a
modality's postcondition. -/
def Fml.rwAtS (top : UpdRw C) : {Γ : Ctx} → Fml C Γ → Option (Fml C Γ)
  | _, .upd m U φ => (top m U φ).orElse fun _ => (Fml.rwAtS top φ).map (.upd m U)
  | _, .and φ ψ => match Fml.rwAtS top φ with
    | some φ' => some (.and φ' ψ)
    | none => (Fml.rwAtS top ψ).map (.and φ)
  | _, .imp φ ψ => (Fml.rwAtS top ψ).map (.imp φ)
  | _, .modal m P κ φ => (Fml.rwAtS top φ).map (.modal m P κ)
  | _, .havoc φ => (Fml.rwAtS top φ).map .havoc
  | _, .all x p φ => (Fml.rwAtS top φ).map (.all x p)
  | _, .bind m x t φ => (Fml.rwAtS top φ).map (.bind m x t)
  | _, .anon xs φ => (Fml.rwAtS top φ).map (.anon xs)
  | _, .tt | _, .eq .. | _, .defined _ | _, .not _ => none

/-- A rewrite that gives what it rewrites, applied where it fits first,
gives the formula. -/
theorem Fml.rwAtS_sound {top : UpdRw C} (htop : top.Sound) :
    {Γ : Ctx} → (φ : Fml C Γ) → {ψ : Fml C Γ} → φ.rwAtS top = some ψ →
      ∀ σ, holds σ ψ → holds σ φ
  | _, .upd m U φ, ψ, h, σ, hψ => by
    simp only [Fml.rwAtS] at h
    cases ht : top m U φ with
    | some χ =>
      simp only [ht, Option.orElse, Option.some.injEq] at h; subst h
      exact htop m U φ _ ht σ hψ
    | none =>
      simp only [ht, Option.orElse, Option.map_eq_some_iff] at h
      obtain ⟨φ', h', rfl⟩ := h
      exact holds_upd_mono (fun τ => Fml.rwAtS_sound htop φ h' τ) σ hψ
  | _, .and φ₁ φ₂, ψ, h, σ, hψ => by
    simp only [Fml.rwAtS] at h
    split at h
    · rename_i h₁; cases h
      exact ⟨Fml.rwAtS_sound htop φ₁ h₁ σ hψ.1, hψ.2⟩
    · obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.1 h
      exact ⟨hψ.1, Fml.rwAtS_sound htop φ₂ h' σ hψ.2⟩
  | _, .imp φ₁ φ₂, ψ, h, σ, hψ => by
    obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun ha => Fml.rwAtS_sound htop φ₂ h' σ (hψ ha)
  | _, .modal m P κ φ, ψ, h, σ, hψ => by
    obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.1 h
    exact Modality.afterRunTR_imp (p := (holds · φ')) hψ fun τ => Fml.rwAtS_sound htop φ h' τ
  | _, .havoc φ, ψ, h, σ, hψ => by
    obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun st nt => Fml.rwAtS_sound htop φ h' _ (hψ st nt)
  | _, .all _ _ φ, ψ, h, σ, hψ => by
    obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun v => Fml.rwAtS_sound htop φ h' _ (hψ v)
  | _, .bind _ _ _ φ, ψ, h, σ, hψ => by
    obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun v => Fml.rwAtS_sound htop φ h' _ (hψ v)
  | _, .anon _ φ, ψ, h, σ, hψ => by
    obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun b => Fml.rwAtS_sound htop φ h' _ (hψ b)
  | _, .tt, _, h, _, _ | _, .eq .., _, h, _, _ | _, .defined _, _, h, _, _
  | _, .not _, _, h, _, _ => by simp only [Fml.rwAtS, reduceCtorEq] at h

/-- Rule `r` at the first update where it fits (`Fml.rwAtS`). -/
def Fml.updAtS (r : UpdRuleNameS) {Γ : Ctx} (φ : Fml C Γ) : Option (Fml C Γ) :=
  φ.rwAtS fun m U ψ => r.top m U ψ

/-- Applying an update rule where it fits first gives a formula that gives
the original. -/
theorem Fml.updAtS_sound {r : UpdRuleNameS} {Γ : Ctx} (φ : Fml C Γ) {ψ : Fml C Γ}
    (h : φ.updAtS r = some ψ) (σ : State C Γ) (hψ : holds σ ψ) : holds σ φ :=
  Fml.rwAtS_sound (fun _ _ _ _ ht σ h => (UpdRuleNameS.top_rule ht).sound σ h) φ h σ hψ

/-! ## All of them: `Fml.simpUpdsS`

Bottom-up, at the positive positions, every stack `{U}{V}…` of one
modality becomes one update where `Upd.seqPar` reads it
(`sequentialToParallel`), the elements setting a local it pops later go
under the box (`simplifyUpdate`), and an update left empty goes before a
formula with no modality (`applySkip`). -/

/-- `{U} φ` with its popped elements dropped under the box, and without the
braces when nothing is left and `φ` has no modality. -/
def Fml.cleanS {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) : Fml C Γ :=
  let U' := if m = .box then U.simp 0 else U
  match Δ, U', φ with
  | _, .nil, φ => if φ.modalFree then φ else .upd m .nil φ
  | _, U', φ => .upd m U' φ

/-- `{U} φ`, merged with an update of the same modality at the head of `φ`
where `Upd.seqPar` reads it, then cleaned. -/
def Fml.mkUpdS {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) : Fml C Δ → Fml C Γ
  | .upd m' V φ =>
    if m' = m then
      match U.seqPar V with
      | some W => Fml.cleanS m W φ
      | none => Fml.cleanS m U (.upd m' V φ)
    else Fml.cleanS m U (.upd m' V φ)
  | φ => Fml.cleanS m U φ

/-- Merge every stack of updates at the positive positions and drop what is
popped. -/
def Fml.simpUpdsS : {Γ : Ctx} → Fml C Γ → Fml C Γ
  | _, .upd m U φ => Fml.mkUpdS m U (Fml.simpUpdsS φ)
  | _, .and φ ψ => .and (Fml.simpUpdsS φ) (Fml.simpUpdsS ψ)
  | _, .imp φ ψ => .imp φ (Fml.simpUpdsS ψ)
  | _, .modal m P κ φ => .modal m P κ (Fml.simpUpdsS φ)
  | _, .havoc φ => .havoc (Fml.simpUpdsS φ)
  | _, .all x p φ => .all x p (Fml.simpUpdsS φ)
  | _, .bind m x t φ => .bind m x t (Fml.simpUpdsS φ)
  | _, .anon xs φ => .anon xs (Fml.simpUpdsS φ)
  | _, φ => φ

theorem Fml.cleanS_holds {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ)
    (σ : State C Γ) (h : holds σ (Fml.cleanS m U φ)) : holds σ (.upd m U φ) := by
  have key : holds σ (.upd m (if m = .box then U.simp 0 else U) φ) := by
    unfold Fml.cleanS at h
    generalize (if m = .box then U.simp 0 else U) = U' at h ⊢
    cases U' with
    | nil =>
      simp only at h
      split at h
      · rename_i hm; exact (holds_upd_nil m hm σ).2 h
      · exact h
    | _ => exact h
  split at key
  · rename_i hm; subst hm; exact holds_upd_simp σ key
  · exact key

theorem Fml.mkUpdS_holds {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ)
    (σ : State C Γ) (h : holds σ (Fml.mkUpdS m U φ)) : holds σ (.upd m U φ) := by
  cases φ with
  | upd m' V φ =>
    simp only [Fml.mkUpdS] at h
    split at h
    · rename_i hm; subst hm
      split at h
      · rename_i W hW
        exact holds_upd_seqPar hW σ (Fml.cleanS_holds _ _ _ σ h)
      · exact Fml.cleanS_holds _ _ _ σ h
    · exact Fml.cleanS_holds _ _ _ σ h
  | _ => exact Fml.cleanS_holds _ _ _ σ h

/-- **`Fml.simpUpdsS` gives a formula that gives the original.**

Example: `x = 1; y = x;` leaves `{ x := 1 } { y := x } y = 1`, which
`simpUpdsS` merges into `{ x := 1 ‖ y := 1 } y = 1`. -/
theorem Fml.simpUpdsS_holds : {Γ : Ctx} → (φ : Fml C Γ) → ∀ σ, holds σ φ.simpUpdsS → holds σ φ
  | _, .upd m U φ, σ, h =>
    holds_upd_mono (fun τ => Fml.simpUpdsS_holds φ τ) σ (Fml.mkUpdS_holds m U _ σ h)
  | _, .and φ ψ, σ, h => ⟨Fml.simpUpdsS_holds φ σ h.1, Fml.simpUpdsS_holds ψ σ h.2⟩
  | _, .imp _ ψ, σ, h => fun ha => Fml.simpUpdsS_holds ψ σ (h ha)
  | _, .modal _ _ _ φ, _, h =>
    Modality.afterRunTR_imp (p := (holds · φ.simpUpdsS)) h fun τ => Fml.simpUpdsS_holds φ τ
  | _, .havoc φ, _, h => fun st nt => Fml.simpUpdsS_holds φ _ (h st nt)
  | _, .all _ _ φ, _, h => fun v => Fml.simpUpdsS_holds φ _ (h v)
  | _, .bind _ _ _ φ, _, h => fun v => Fml.simpUpdsS_holds φ _ (h v)
  | _, .anon _ φ, _, h => fun b => Fml.simpUpdsS_holds φ _ (h b)
  | _, .tt, _, h | _, .eq .., _, h | _, .defined _, _, h | _, .not _, _, h => h

/-- A scoped formula is valid where its simplification is. -/
theorem Valid.of_simpUpdsS {φ : Fml C []} (h : Valid φ.simpUpdsS) : Valid φ :=
  fun σ => Fml.simpUpdsS_holds φ σ (h σ)

/-- A scoped formula is valid where a rule's rewrite of it is. -/
theorem Valid.of_updAtS {r : UpdRuleNameS} {φ ψ : Fml C []} (hr : φ.updAtS r = some ψ)
    (h : Valid ψ) : Valid φ :=
  fun σ => Fml.updAtS_sound φ hr σ (h σ)

end Solidity
