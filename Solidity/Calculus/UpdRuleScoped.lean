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
(`Upd.totalB`): what the erased `Upd.total` admits (a literal, an alias to a
root and its fields, `sp1 := alice.account`), and also a local, which a
typed state always binds, `unset` and the ledger's saves; under the box any
update applies, as `Proves.applyOnRigidBox`.

`elimSelfUpdate` (commented out in solkey; theorems only in the erased
form) is not ported.

The kernel evaluates these functions (the examples' `rfl`), so they keep
Gate G0's first two conditions: the walks over a whole formula or update
(`Fml.rwAtS`, `Fml.simpUpdsS`, `Upd.totalB`, `Upd.size`) are written by
the recursor, each with its `match` form as the `implemented_by` twin
(`Fml.rwAtSM`, …) and a link theorem (`Fml.rwAtS_eq_rwAtSM`, …), the
proofs stated on the twins; a look at a formula's or an update's head is
`Fml.casesOn`/`Upd.casesOn` (`Fml.updHead?`, `Upd.skipS`).  `match` stays
on the helpers that take one `Tm` or `Rhs` apart (`Tm.totalB`,
`Tm.totalP`, `Rhs.totalB`), decision 83's.  `Upd.seqPar`, `Upd.simp` and
`Fml.substU` are Graft's and UpdateRules', under their exemption.
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

/-- A path that cannot halt: a root and its fields (`alice.account`), not
an alias, which may be unset. -/
def Tm.totalP {Γ : Ctx} : {s : Srt} → Tm C Γ s → Bool
  | _, .app0 (.root _) => true
  | _, .app1 (.field _) _ p => Tm.totalP p
  | _, _ => false

/-- A right-hand side that cannot halt. -/
def Rhs.totalB {Γ : Ctx} : {t : LTy} → Rhs C Γ t → Bool
  | _, .val t => t.totalB
  | _, .path p => p.totalP
  | _, .unset | _, .saveNet | _, .saveNetMt => true
  | _, _ => false

/-- An element that cannot halt: a local set to what cannot halt. -/
def UpdElem.totalB {Γ Δ : Ctx} : UpdElem C Γ Δ → Bool
  | .local _ r => r.totalB
  | _ => false

/-- `Upd.totalB`'s compiled twin. -/
def Upd.totalBM {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => true
  | _, .snoc U e => e.totalB && Upd.totalBM U
  | _, .decl U _ r => r.totalB && Upd.totalBM U
  | _, .pop U _ | _, .drop U _ => Upd.totalBM U

/-- An update that cannot halt: it sets and declares locals to what cannot
halt, and pops, by the recursor.  It admits what the erased `Upd.total`
does, and locals, `unset` and the ledger's saves besides. -/
@[implemented_by Upd.totalBM]
def Upd.totalB {Γ Δ : Ctx} (U : Upd C Γ Δ) : Bool :=
  Upd.rec (motive := fun _ _ => Bool) true (fun _ e ih => e.totalB && ih)
    (fun _ _ r ih => r.totalB && ih) (fun _ _ ih => ih) (fun _ _ ih => ih) U

theorem Upd.totalB_eq_totalBM {Γ Δ : Ctx} (U : Upd C Γ Δ) : U.totalB = U.totalBM := by
  induction U with
  | nil => rfl
  | snoc U e ih | decl U x r ih | pop U h ih | drop U h ih =>
    simp only [Upd.totalBM, ← ih]; rfl

theorem Tm.totalB_eval {Γ : Ctx} (σ : EState C Γ) :
    (t : Tm C Γ .val) → t.totalB = true → ∃ v, t.eval σ = .ok v
  | .pvV _, _ => ⟨_, rfl⟩
  | .app0 (.lit v), _ => ⟨v, rfl⟩

/-- A root and its fields read as a path: `Op0.root` and `Op1.field` do
not halt. -/
theorem Tm.totalP_eval {Γ : Ctx} (σ : EState C Γ) :
    (p : Tm C Γ .path) → p.totalP = true → ∃ v, p.eval σ = .ok v
  | .app0 (.root r), _ => ⟨(r, []), rfl⟩
  | .app1 (.field f) _ p, h => by
    obtain ⟨⟨r, segs⟩, hv⟩ := Tm.totalP_eval σ p h
    exact ⟨(r, segs ++ [.field f]), by
      show (do let (r, segs) ← p.eval σ; pure (r, segs ++ [Semantics.Seg.field f])) = _
      rw [hv]; rfl⟩

theorem Rhs.totalB_eval {Γ : Ctx} (σ : EState C Γ) :
    {t : LTy} → (r : Rhs C Γ t) → r.totalB = true → ∃ v, r.eval σ = .ok v
  | _, .val t, h => Tm.totalB_eval σ t h
  | _, .path p, h => by
    obtain ⟨v, hv⟩ := Tm.totalP_eval σ p h
    exact ⟨some v, by show (do pure (some (← p.eval σ))) = _; rw [hv]; rfl⟩
  | _, .unset, _ => ⟨_, rfl⟩
  | _, .saveNet, _ => ⟨_, rfl⟩
  | _, .saveNetMt, _ => ⟨_, rfl⟩

/-- An update that cannot halt runs (on the twin). -/
theorem Upd.totalBM_apply {Γ : Ctx} (σ₀ : EState C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → U.totalBM = true → ∃ σ₁, U.apply σ₀ = .ok σ₁
  | _, .nil, _ => ⟨σ₀, rfl⟩
  | _, .snoc U (.local i r), h => by
    have h : r.totalB = true ∧ U.totalBM = true := Bool.and_eq_true_iff.mp h
    obtain ⟨τ, hτ⟩ := Upd.totalBM_apply σ₀ U h.2
    obtain ⟨v, hv⟩ := Rhs.totalB_eval σ₀ r h.1
    exact ⟨τ.setLocal i v, by
      change (do UpdElem.write σ₀ (.local i r) (← U.apply σ₀)) = _
      rw [hτ]
      change (do pure (τ.setLocal i (← r.eval σ₀))) = _
      rw [hv]; rfl⟩
  | _, .snoc _ (.storage _), h | _, .snoc _ (.memory _), h | _, .snoc _ (.selfBalance ..), h
  | _, .snoc _ (.net ..), h | _, .snoc _ (.pay ..), h | _, .snoc _ (.netMt ..), h
  | _, .snoc _ (.setBalance _), h => absurd h Bool.false_ne_true
  | _, .decl U _ r, h => by
    have h : r.totalB = true ∧ U.totalBM = true := Bool.and_eq_true_iff.mp h
    obtain ⟨τ, hτ⟩ := Upd.totalBM_apply σ₀ U h.2
    obtain ⟨v, hv⟩ := Rhs.totalB_eval σ₀ r h.1
    exact ⟨τ.push v, by
      change (do let τ ← U.apply σ₀; pure (τ.push (← r.eval σ₀))) = _
      rw [hτ, hv]; rfl⟩
  | _, .pop U e, h => by
    obtain ⟨τ, hτ⟩ := Upd.totalBM_apply σ₀ U h
    exact ⟨τ.drop e, by change (U.apply σ₀).map (EState.drop e) = _; rw [hτ]; rfl⟩
  | _, .drop U e, h => by
    obtain ⟨τ, hτ⟩ := Upd.totalBM_apply σ₀ U h
    exact ⟨τ.thin e, by change (U.apply σ₀).map (EState.thin e) = _; rw [hτ]; rfl⟩

/-- An update that cannot halt runs. -/
theorem Upd.totalB_apply {Γ Δ : Ctx} (σ₀ : EState C Γ) (U : Upd C Γ Δ) (h : U.totalB = true) :
    ∃ σ₁, U.apply σ₀ = .ok σ₁ :=
  Upd.totalBM_apply σ₀ U (U.totalB_eq_totalBM ▸ h)

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

/-- `Upd.size`'s compiled twin. -/
def Upd.sizeM {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Nat
  | _, .nil => 0
  | _, .snoc U _ | _, .decl U _ _ | _, .pop U _ | _, .drop U _ => U.sizeM + 1

/-- The number of elements, pops and frame ends of an update, by the
recursor. -/
@[implemented_by Upd.sizeM]
def Upd.size {Γ Δ : Ctx} (U : Upd C Γ Δ) : Nat :=
  Upd.rec (motive := fun _ _ => Nat) 0 (fun _ _ ih => ih + 1) (fun _ _ _ ih => ih + 1)
    (fun _ _ ih => ih + 1) (fun _ _ ih => ih + 1) U

theorem Upd.size_eq_sizeM {Γ Δ : Ctx} (U : Upd C Γ Δ) : U.size = U.sizeM := by
  induction U with
  | nil => rfl
  | snoc U e ih | decl U x r ih | pop U h ih | drop U h ih => simp only [Upd.sizeM, ← ih]; rfl

/-- An update at the head of a formula: `{U} φ`, `U` leaving `Δ'`. -/
structure UHead (C : Contract) (Γ : Ctx) where
  {Δ' : Ctx}
  m : Modality
  U : Upd C Γ Δ'
  φ : Fml C Δ'

/-- The update at the head of `φ`, if `φ` is one (`Fml.casesOn`). -/
def Fml.updHead? {Γ : Ctx} (φ : Fml C Γ) : Option (UHead C Γ) :=
  Fml.casesOn (motive := fun Γ _ => Option (UHead C Γ)) (tt := none) (eq := fun _ _ => none)
    (defined := fun _ => none) (not := fun _ => none) (and := fun _ _ => none)
    (imp := fun _ _ => none) (upd := fun m U φ => some ⟨m, U, φ⟩)
    (modal := fun _ _ _ _ => none) (havoc := fun _ => none) (all := fun _ _ _ => none)
    (bind := fun _ _ _ _ => none) (anon := fun _ _ => none) φ

/-- `{} φ` as `φ`, for `φ` with no modality (`applySkip`); `none` for any
other update (`Upd.casesOn`). -/
def Upd.skipS {Γ Δ : Ctx} (U : Upd C Γ Δ) (φ : Fml C Δ) : Option (Fml C Γ) :=
  Upd.casesOn (motive := fun Δ _ => Fml C Δ → Option (Fml C Γ)) U
    (nil := fun φ => if φ.modalFree then some φ else none) (snoc := fun _ _ _ => none)
    (decl := fun _ _ _ _ => none) (pop := fun _ _ _ => none) (drop := fun _ _ _ => none) φ

/-- What `Upd.skipS` returns is an `applySkip` rewrite of `{U} φ`. -/
theorem Upd.skipS_rule {Γ Δ : Ctx} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ} {ψ : Fml C Γ}
    (h : U.skipS φ = some ψ) : UpdRuleS (.upd m U φ) ψ := by
  cases U with
  | nil =>
    change (if φ.modalFree then some φ else none) = some ψ at h
    split at h
    · rename_i hm; cases h; exact .applySkip hm
    · cases h
  | _ => cases h

/-- Rule `r` on `{U} φ` under `m`, if it fits and changes something. -/
def UpdRuleNameS.top {Γ Δ : Ctx} (r : UpdRuleNameS) (m : Modality) (U : Upd C Γ Δ)
    (φ : Fml C Δ) : Option (Fml C Γ) :=
  match r with
  | .sequentialToParallel =>
    match φ.updHead? with
    | some ⟨m', V, ψ⟩ => if m' = m then (U.seqPar V).map fun W => .upd m W ψ else none
    | none => none
  | .simplifyUpdate =>
    match m with
    | .box => if (U.simp 0).size < U.size then some (.upd .box (U.simp 0) φ) else none
    | .diamond => none
  | .applySkip => U.skipS φ
  | .applyOnRigid => if m = .box ∨ U.totalB = true then Fml.substU U φ else none

/-- When rule `r` fits at the top of `{U} φ`, what it returns is an
`UpdRuleS` rewrite of `{U} φ`. -/
theorem UpdRuleNameS.top_rule {Γ Δ : Ctx} {r : UpdRuleNameS} {m : Modality} {U : Upd C Γ Δ}
    {φ : Fml C Δ} {ψ : Fml C Γ} (h : r.top m U φ = some ψ) : UpdRuleS (.upd m U φ) ψ := by
  cases r with
  | sequentialToParallel =>
    cases φ with
    | upd m' V φ =>
      change (if m' = m then (U.seqPar V).map fun W => Fml.upd m W φ else none) = some ψ at h
      split at h
      · rename_i hm; subst hm
        obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 h
        exact .sequentialToParallel hW
      · cases h
    | _ => cases h
  | simplifyUpdate =>
    cases m with
    | box =>
      change (if (U.simp 0).size < U.size then some (Fml.upd .box (U.simp 0) φ) else none) =
        some ψ at h
      split at h
      · cases h; exact .simplifyUpdate
      · cases h
    | diamond => cases h
  | applySkip => exact Upd.skipS_rule h
  | applyOnRigid =>
    change (if m = .box ∨ U.totalB = true then Fml.substU U φ else none) = some ψ at h
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

/-- `Fml.rwAtS`'s compiled twin. -/
def Fml.rwAtSM (top : UpdRw C) : {Γ : Ctx} → Fml C Γ → Option (Fml C Γ)
  | _, .upd m U φ => (top m U φ).orElse fun _ => (Fml.rwAtSM top φ).map (.upd m U)
  | _, .and φ ψ => match Fml.rwAtSM top φ with
    | some φ' => some (.and φ' ψ)
    | none => (Fml.rwAtSM top ψ).map (.and φ)
  | _, .imp φ ψ => (Fml.rwAtSM top ψ).map (.imp φ)
  | _, .modal m P κ φ => (Fml.rwAtSM top φ).map (.modal m P κ)
  | _, .havoc φ => (Fml.rwAtSM top φ).map .havoc
  | _, .all x p φ => (Fml.rwAtSM top φ).map (.all x p)
  | _, .bind m x t φ => (Fml.rwAtSM top φ).map (.bind m x t)
  | _, .anon xs φ => (Fml.rwAtSM top φ).map (.anon xs)
  | _, .tt | _, .eq .. | _, .defined _ | _, .not _ => none

/-- `top` at the first update where it fits, outermost first, then left to
right, at the positive positions only: under an update, a conjunction,
the right of an implication, a binder, `{havoc}`, `{anon}` and a
modality's postcondition; by the recursor. -/
@[implemented_by Fml.rwAtSM]
def Fml.rwAtS (top : UpdRw C) {Γ : Ctx} (φ : Fml C Γ) : Option (Fml C Γ) :=
  Fml.rec (motive := fun Γ _ => Option (Fml C Γ)) (tt := none) (eq := fun _ _ => none)
    (defined := fun _ => none) (not := fun _ _ => none)
    (and := fun φ ψ ihφ ihψ => match ihφ with
      | some φ' => some (.and φ' ψ)
      | none => ihψ.map (.and φ))
    (imp := fun φ _ _ ihψ => ihψ.map (.imp φ))
    (upd := fun m U φ ih => (top m U φ).orElse fun _ => ih.map (.upd m U))
    (modal := fun m P κ _ ih => ih.map (.modal m P κ)) (havoc := fun _ ih => ih.map .havoc)
    (all := fun x p _ ih => ih.map (.all x p)) (bind := fun m x t _ ih => ih.map (.bind m x t))
    (anon := fun xs _ ih => ih.map (.anon xs)) φ

theorem Fml.rwAtS_eq_rwAtSM (top : UpdRw C) {Γ : Ctx} (φ : Fml C Γ) :
    φ.rwAtS top = φ.rwAtSM top := by
  induction φ with
  | tt | eq | defined | not => rfl
  | upd m U φ ih | modal m P κ φ ih | havoc φ ih | all x p φ ih | bind m x t φ ih
  | anon xs φ ih => simp only [Fml.rwAtSM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [Fml.rwAtSM, ← ihφ, ← ihψ]; rfl

/-- A rewrite that gives what it rewrites, applied where it fits first,
gives the formula (on the twin). -/
theorem Fml.rwAtSM_sound {top : UpdRw C} (htop : top.Sound) :
    {Γ : Ctx} → (φ : Fml C Γ) → {ψ : Fml C Γ} → φ.rwAtSM top = some ψ →
      ∀ σ, holds σ ψ → holds σ φ
  | _, .upd m U φ, ψ, h, σ, hψ => by
    simp only [Fml.rwAtSM] at h
    cases ht : top m U φ with
    | some χ =>
      simp only [ht, Option.orElse, Option.some.injEq] at h; subst h
      exact htop m U φ _ ht σ hψ
    | none =>
      simp only [ht, Option.orElse, Option.map_eq_some_iff] at h
      obtain ⟨φ', h', rfl⟩ := h
      exact holds_upd_mono (fun τ => Fml.rwAtSM_sound htop φ h' τ) σ hψ
  | _, .and φ₁ φ₂, ψ, h, σ, hψ => by
    simp only [Fml.rwAtSM] at h
    split at h
    · rename_i h₁; cases h
      exact ⟨Fml.rwAtSM_sound htop φ₁ h₁ σ hψ.1, hψ.2⟩
    · obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.1 h
      exact ⟨hψ.1, Fml.rwAtSM_sound htop φ₂ h' σ hψ.2⟩
  | _, .imp φ₁ φ₂, ψ, h, σ, hψ => by
    obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun ha => Fml.rwAtSM_sound htop φ₂ h' σ (hψ ha)
  | _, .modal m P κ φ, ψ, h, σ, hψ => by
    obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.1 h
    exact Modality.afterRunTR_imp (p := (holds · φ')) hψ fun τ => Fml.rwAtSM_sound htop φ h' τ
  | _, .havoc φ, ψ, h, σ, hψ => by
    obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun st nt => Fml.rwAtSM_sound htop φ h' _ (hψ st nt)
  | _, .all _ _ φ, ψ, h, σ, hψ => by
    obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun v => Fml.rwAtSM_sound htop φ h' _ (hψ v)
  | _, .bind _ _ _ φ, ψ, h, σ, hψ => by
    obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun v => Fml.rwAtSM_sound htop φ h' _ (hψ v)
  | _, .anon _ φ, ψ, h, σ, hψ => by
    obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun b => Fml.rwAtSM_sound htop φ h' _ (hψ b)
  | _, .tt, _, h, _, _ | _, .eq .., _, h, _, _ | _, .defined _, _, h, _, _
  | _, .not _, _, h, _, _ => by simp only [Fml.rwAtSM, reduceCtorEq] at h

/-- A rewrite that gives what it rewrites, applied where it fits first,
gives the formula. -/
theorem Fml.rwAtS_sound {top : UpdRw C} (htop : top.Sound) {Γ : Ctx} (φ : Fml C Γ)
    {ψ : Fml C Γ} (h : φ.rwAtS top = some ψ) (σ : State C Γ) (hψ : holds σ ψ) : holds σ φ :=
  Fml.rwAtSM_sound htop φ (Fml.rwAtS_eq_rwAtSM top φ ▸ h) σ hψ

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
  (U'.skipS φ).getD (.upd m U' φ)

/-- `{U} φ`, merged with an update of the same modality at the head of `φ`
where `Upd.seqPar` reads it, then cleaned. -/
def Fml.mkUpdS {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) : Fml C Γ :=
  match φ.updHead? with
  | some ⟨m', V, ψ⟩ =>
    if m' = m then
      match U.seqPar V with
      | some W => Fml.cleanS m W ψ
      | none => Fml.cleanS m U φ
    else Fml.cleanS m U φ
  | none => Fml.cleanS m U φ

/-- `Fml.simpUpdsS`'s compiled twin. -/
def Fml.simpUpdsSM : {Γ : Ctx} → Fml C Γ → Fml C Γ
  | _, .upd m U φ => Fml.mkUpdS m U (Fml.simpUpdsSM φ)
  | _, .and φ ψ => .and (Fml.simpUpdsSM φ) (Fml.simpUpdsSM ψ)
  | _, .imp φ ψ => .imp φ (Fml.simpUpdsSM ψ)
  | _, .modal m P κ φ => .modal m P κ (Fml.simpUpdsSM φ)
  | _, .havoc φ => .havoc (Fml.simpUpdsSM φ)
  | _, .all x p φ => .all x p (Fml.simpUpdsSM φ)
  | _, .bind m x t φ => .bind m x t (Fml.simpUpdsSM φ)
  | _, .anon xs φ => .anon xs (Fml.simpUpdsSM φ)
  | _, φ => φ

/-- Merge every stack of updates at the positive positions and drop what is
popped, by the recursor. -/
@[implemented_by Fml.simpUpdsSM]
def Fml.simpUpdsS {Γ : Ctx} (φ : Fml C Γ) : Fml C Γ :=
  Fml.rec (motive := fun Γ _ => Fml C Γ) (tt := .tt) (eq := fun a b => .eq a b)
    (defined := fun t => .defined t) (not := fun φ _ => .not φ)
    (and := fun _ _ ihφ ihψ => .and ihφ ihψ) (imp := fun φ _ _ ihψ => .imp φ ihψ)
    (upd := fun m U _ ih => Fml.mkUpdS m U ih) (modal := fun m P κ _ ih => .modal m P κ ih)
    (havoc := fun _ ih => .havoc ih) (all := fun x p _ ih => .all x p ih)
    (bind := fun m x t _ ih => .bind m x t ih) (anon := fun xs _ ih => .anon xs ih) φ

theorem Fml.simpUpdsS_eq_simpUpdsSM {Γ : Ctx} (φ : Fml C Γ) : φ.simpUpdsS = φ.simpUpdsSM := by
  induction φ with
  | tt | eq | defined | not => rfl
  | upd m U φ ih | modal m P κ φ ih | havoc φ ih | all x p φ ih | bind m x t φ ih
  | anon xs φ ih => simp only [Fml.simpUpdsSM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [Fml.simpUpdsSM, ← ihφ, ← ihψ]; rfl

/-- What `Upd.skipS` returns gives `{U} φ`. -/
theorem Upd.skipS_holds {Γ Δ : Ctx} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ} {ψ : Fml C Γ}
    (h : U.skipS φ = some ψ) (σ : State C Γ) (hψ : holds σ ψ) : holds σ (.upd m U φ) :=
  (Upd.skipS_rule h).sound σ hψ

theorem Fml.cleanS_holds {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ)
    (σ : State C Γ) (h : holds σ (Fml.cleanS m U φ)) : holds σ (.upd m U φ) := by
  have key : holds σ (.upd m (if m = .box then U.simp 0 else U) φ) := by
    change holds σ (((if m = .box then U.simp 0 else U).skipS φ).getD
      (.upd m (if m = .box then U.simp 0 else U) φ)) at h
    generalize (if m = .box then U.simp 0 else U) = U' at h ⊢
    cases hs : U'.skipS φ with
    | some ψ => rw [hs] at h; exact Upd.skipS_holds hs σ h
    | none => rw [hs] at h; exact h
  split at key
  · rename_i hm; subst hm; exact holds_upd_simp σ key
  · exact key

theorem Fml.mkUpdS_holds {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ)
    (σ : State C Γ) (h : holds σ (Fml.mkUpdS m U φ)) : holds σ (.upd m U φ) := by
  cases φ with
  | upd m' V φ =>
    change holds σ (if m' = m then
      match U.seqPar V with
      | some W => Fml.cleanS m W φ
      | none => Fml.cleanS m U (.upd m' V φ)
    else Fml.cleanS m U (.upd m' V φ)) at h
    split at h
    · rename_i hm; subst hm
      split at h
      · rename_i W hW
        exact holds_upd_seqPar hW σ (Fml.cleanS_holds _ _ _ σ h)
      · exact Fml.cleanS_holds _ _ _ σ h
    · exact Fml.cleanS_holds _ _ _ σ h
  | _ => exact Fml.cleanS_holds _ _ _ σ h

/-- `Fml.simpUpdsS` gives a formula that gives the original (on the twin). -/
theorem Fml.simpUpdsSM_holds : {Γ : Ctx} → (φ : Fml C Γ) → ∀ σ, holds σ φ.simpUpdsSM → holds σ φ
  | _, .upd m U φ, σ, h =>
    holds_upd_mono (fun τ => Fml.simpUpdsSM_holds φ τ) σ (Fml.mkUpdS_holds m U _ σ h)
  | _, .and φ ψ, σ, h => ⟨Fml.simpUpdsSM_holds φ σ h.1, Fml.simpUpdsSM_holds ψ σ h.2⟩
  | _, .imp _ ψ, σ, h => fun ha => Fml.simpUpdsSM_holds ψ σ (h ha)
  | _, .modal _ _ _ φ, _, h =>
    Modality.afterRunTR_imp (p := (holds · φ.simpUpdsSM)) h fun τ => Fml.simpUpdsSM_holds φ τ
  | _, .havoc φ, _, h => fun st nt => Fml.simpUpdsSM_holds φ _ (h st nt)
  | _, .all _ _ φ, _, h => fun v => Fml.simpUpdsSM_holds φ _ (h v)
  | _, .bind _ _ _ φ, _, h => fun v => Fml.simpUpdsSM_holds φ _ (h v)
  | _, .anon _ φ, _, h => fun b => Fml.simpUpdsSM_holds φ _ (h b)
  | _, .tt, _, h | _, .eq .., _, h | _, .defined _, _, h | _, .not _, _, h => h

/-- **`Fml.simpUpdsS` gives a formula that gives the original.**

Example: `x = 1; y = x;` leaves `{ x := 1 } { y := x } y = 1`, which
`simpUpdsS` merges into `{ x := 1 ‖ y := 1 } y = 1`. -/
theorem Fml.simpUpdsS_holds {Γ : Ctx} (φ : Fml C Γ) (σ : State C Γ)
    (h : holds σ φ.simpUpdsS) : holds σ φ :=
  Fml.simpUpdsSM_holds φ σ (Fml.simpUpdsS_eq_simpUpdsSM φ ▸ h)

/-- A scoped formula is valid where its simplification is. -/
theorem Valid.of_simpUpdsS {φ : Fml C []} (h : Valid φ.simpUpdsS) : Valid φ :=
  fun σ => Fml.simpUpdsS_holds φ σ (h σ)

/-- A scoped formula is valid where a rule's rewrite of it is. -/
theorem Valid.of_updAtS {r : UpdRuleNameS} {φ ψ : Fml C []} (hr : φ.updAtS r = some ψ)
    (h : Valid ψ) : Valid φ :=
  fun σ => Fml.updAtS_sound φ hr σ (h σ)

end Solidity
