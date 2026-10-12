import Solidity.Calculus.UpdateRules

/-!
# Update simplification on scoped formulas

KeY's update simplification (`updateRules.key`) on `Fml C Γ` and its
updates `Upd C Γ Δ`, read over the typed state (`holds`):

| KeY taclet | here |
|---|---|
| `sequentialToParallel1/2/3`: `{u}{u2}φ ⇝ {u ‖ {u}u2}φ` | `UpdRuleS.sequentialToParallel` (`Upd.seqPar`, `Calculus/Graft.lean`) |
| `simplifyUpdate1/2/3` (`\dropEffectlessElementaries`) | `UpdRuleS.simplifyUpdate` (`Upd.simpS`: `Upd.simp`, `Calculus/UpdateRules.lean`, under the box; the shadowed writes, `Upd.shadow`, under either modality) |
| `applySkip1/2/3`: `{skip}φ ⇝ φ` | `UpdRuleS.applySkip` |
| `applyOnRigidFormula`, `applyOnPV`, `applyOnDifferentPV` | `UpdRuleS.applyOnRigid` (`Fml.substU`) |
| — (Lean only) | `UpdRuleS.mergeHidden` (`Fml.mergeB`: `sequentialToParallel` through hidden binders), `UpdRuleS.absorbPops` (`Fml.absorbPops`: scope ends merged in), `UpdRuleS.trans` |

`sol_upd sequentialToParallel` is `mergeHidden` (`Fml.mergeB`), and
`sol_upd simplifyUpdate` is `absorbPops` then `simplifyUpdate`
(`Fml.simpAt`, `Fml.simpAt_rule`): the taclets' own shapes are the two
constructors named after them.

**One way.**  Each rule rewrites `φ` to a `ψ` that gives it
(`UpdRuleS.sound`: `holds σ ψ → holds σ φ`), the direction a derivation
uses.  The converse fails, because
`{U} φ` reads `φ` in every *typed* state the update lands on
(`holds`, `Upd.Lands`), and a merged update may reach a typed state the two updates in
turn do not: `{x := 300}{x := 1} φ` for a `uint8` local `x` holds
vacuously (no typed state holds `300` in `x`), its merge
`{x := 300 ‖ x := 1} φ` only where `φ` does.  So a rule applies at the
positive positions of a formula only (`Fml.updAtS`, `Fml.simpUpdsS`): under
an update, a conjunction, the right of an implication, a binder, `{havoc}`,
`{anon}` and a modality's postcondition, not under a negation or on the
left of an implication.

**What the scope changes.**  An update's locals are positions, so what
KeY's `dropEffectless` drops by name splits in two: an element that
sets a local the same update pops later (a capture's `se1`, `sp1`) goes
(`Upd.simp`, under the box, as `Proves.simplify`), and so does a write a
later one to the same local shadows (`Upd.shadow`, under either modality);
an element that sets a local still in scope that `φ` does not read stays.  `applySkip` asks a formula with no modality (`Fml.modalFree`): such a
formula holds in a typed state by what its terms read of it and its heap
typing alone (`holds_congr_reads`), and the states `{}` reads `φ` in are
those.
`applyOnRigid` under the diamond asks an update that cannot halt
(`Upd.totalB`): a literal, an alias to a root and its fields
(`sp1 := alice.account`), a local, which a typed state always binds,
`unset` and the ledger's saves; under the box any
update applies, as `Proves.applyOnRigidBox`.

`elimSelfUpdate` (commented out in solkey) is not ported.

The kernel evaluates these functions (the examples' `rfl`), so they keep
Gate G0's first two conditions: the walks over a whole formula or update
(`Fml.rwAtS`, `Fml.simpUpdsS`, `Fml.mergeB`, `Fml.cleanB`, `Upd.totalB`,
`Upd.size`, `Upd.unsetAt`, `Upd.redecl`, `Upd.shadow`) are written by the
recursor, each with its `match` form as the `implemented_by` twin
(`Fml.rwAtSM`, …, `Upd.shadowM`) and a link theorem
(`Fml.rwAtS_eq_rwAtSM`, …, `Upd.shadow_eq_shadowM`), the proofs stated on
the twins; `Upd.redecl` reads the declaration's `Idx` by `Idx.casesOn`
with no cast (`Upd.declAt`); a look at a formula's or an update's head is
`Fml.casesOn`/`Upd.casesOn` (`Fml.updHead?`, `Upd.skipS`).  `match` stays
on the helpers that take one `Tm` or `Rhs` apart (`Tm.totalB`,
`Tm.totalP`, `Rhs.totalB`), decision 83's.  `Upd.seqPar`, `Upd.simp` and
`Fml.substU` are Graft's and UpdateRules', under their exemption.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)

variable {C : Contract}

/-! ## Reading a formula by what it reads -/

/-- Two sets of locals that read alike read alike with the same locals set. -/
theorem TEnv.foldl_set_erase_congr {H : HTy} {Γ : Ctx} (xs : List ((t : LTy) × Idx Γ t))
    (b : (x : (t : LTy) × Idx Γ t) → x.1.TDenote C H) :
    ∀ e e' : TEnv C H Γ, (∀ {t : LTy} (i : Idx Γ t),
      LTy.TDenote.erase t (TEnv.get i e) = LTy.TDenote.erase t (TEnv.get i e')) →
      ∀ {t : LTy} (i : Idx Γ t),
        LTy.TDenote.erase t (TEnv.get i (xs.foldl (fun e x => TEnv.set x.2 (b x) e) e)) =
          LTy.TDenote.erase t (TEnv.get i (xs.foldl (fun e x => TEnv.set x.2 (b x) e) e')) := by
  induction xs with
  | nil => intro e e' h; exact h
  | cons x xs ih =>
    intro e e' h
    refine ih _ _ fun {u} j => ?_
    obtain ⟨t, i⟩ := x
    by_cases hj : i.toNat = j.toNat
    · obtain rfl := Idx.ty_eq_of_toNat hj
      obtain rfl := Idx.toNat_inj i j hj
      rw [TEnv.get_set, TEnv.get_set]
    · rw [TEnv.get_set_ne _ _ _ _ hj, TEnv.get_set_ne _ _ _ _ hj]
      exact h j

/-- **A formula with no modality reads the typed state by what its terms
read of it and its heap typing alone** (`State.ReadsAs`): its atoms read the
global part and the locals erased, an update reads the state it is applied
in so, and its binders push, havoc and anonymise alike. -/
theorem holds_congr_reads : {Γ : Ctx} → (φ : Fml C Γ) → φ.modalFree = true →
    (σ σ' : State C Γ) → σ.H = σ'.H → σ.ReadsAs σ' → (holds σ φ ↔ holds σ' φ)
  | _, .tt, _, _, _, _, _ => Iff.rfl
  | _, .eq a b, _, σ, σ', _, he => by
    show Theory.StValue.Equiv (a.denoteT σ) (b.denoteT σ) ↔
      Theory.StValue.Equiv (a.denoteT σ') (b.denoteT σ')
    rw [Tm.denoteT_congr he a, Tm.denoteT_congr he b]
  | _, .defined t, _, σ, σ', _, he => by
    show (∃ x, t.evalT σ = .ok x) ↔ (∃ x, t.evalT σ' = .ok x)
    rw [Tm.evalT_congr he t]
  | _, .not φ, hm, σ, σ', hH, he => not_congr (holds_congr_reads φ hm σ σ' hH he)
  | _, .and φ ψ, hm, σ, σ', hH, he => by
    have hm : φ.modalFree = true ∧ ψ.modalFree = true := Bool.and_eq_true_iff.mp hm
    exact and_congr (holds_congr_reads φ hm.1 σ σ' hH he) (holds_congr_reads ψ hm.2 σ σ' hH he)
  | _, .imp φ ψ, hm, σ, σ', hH, he => by
    have hm : φ.modalFree = true ∧ ψ.modalFree = true := Bool.and_eq_true_iff.mp hm
    exact imp_congr (holds_congr_reads φ hm.1 σ σ' hH he) (holds_congr_reads ψ hm.2 σ σ' hH he)
  | _, .upd m U φ, _, σ, σ', hH, he => Upd.afterT_congr m he hH U _
  | _, .modal .., hm, _, _, _, _ => absurd hm Bool.false_ne_true
  | _, .havoc φ, hm, σ, σ', hH, he => by
    show (∀ st nt, holds (σ.havoc st nt) φ) ↔ (∀ st nt, holds (σ'.havoc st nt) φ)
    refine forall_congr' fun st => forall_congr' fun nt => holds_congr_reads φ hm _ _ hH ?_
    exact ⟨by rw [State.globE_havoc, State.globE_havoc, he.1], fun i => he.2 i⟩
  | _, .all _ p φ, hm, σ, σ', hH, he => by
    show (∀ v : p.Denote, holds (σ.push (t := .val p) v) φ) ↔
      (∀ v : p.Denote, holds (σ'.push (t := .val p) v) φ)
    refine forall_congr' fun v => holds_congr_reads φ hm _ _ hH ⟨he.1, fun i => ?_⟩
    cases i with
    | here => rfl
    | there j => exact he.2 j
  | _, .bind m _ t φ, hm, σ, σ', hH, he => by
    obtain ⟨st, H, hp, env, nt, sb, tx⟩ := σ
    obtain ⟨st', H', hp', env', nt', sb', tx'⟩ := σ'
    cases hH
    refine forall_congr' fun v => holds_congr_reads φ hm _ _ rfl ⟨he.1, fun i => ?_⟩
    cases i with
    | here => rfl
    | there j => exact he.2 j
  | _, .anon xs φ, hm, σ, σ', hH, he => by
    obtain ⟨st, H, hp, env, nt, sb, tx⟩ := σ
    obtain ⟨st', H', hp', env', nt', sb', tx'⟩ := σ'
    cases hH
    refine forall_congr' fun b => holds_congr_reads φ hm _ _ rfl
      ⟨he.1, fun i => TEnv.foldl_set_erase_congr xs b env env' (fun j => he.2 j) i⟩

/-- Two typed states that read alike, the heap typing of one a prefix of
the other's, have one heap typing: the next identity is its length. -/
theorem State.H_eq_of_globE {Γ : Ctx} {σ σ' : State C Γ} (hg : σ'.globE = σ.globE)
    (hp : σ.H <+: σ'.H) : σ.H = σ'.H := by
  have hl : σ'.H.length = σ.H.length := congrArg Semantics.State.nextId hg
  exact hp.sublist.eq_of_length hl.symm

/-- `{} φ` holds where `φ` does, for `φ` with no modality. -/
theorem holds_upd_nil {Γ : Ctx} (m : Modality) {φ : Fml C Γ} (hm : φ.modalFree = true)
    (σ : State C Γ) : holds σ (.upd m .nil φ) ↔ holds σ φ := by
  refine ⟨fun h => h.of_lands (Upd.lands_nil σ) (List.prefix_refl _), fun h => ?_⟩
  refine Upd.afterT_intro (fun _ he => nomatch he) fun g σ' hL hp => ?_
  have hg : g = σ.globE := (Except.ok.inj hL.1).symm
  have hr : σ.ReadsAs σ' := ⟨(hL.2.1.trans hg).symm, fun i => (hL.2.2 i).symm⟩
  exact (holds_congr_reads φ hm σ σ' (State.H_eq_of_globE hr.1.symm hp) hr).1 h

/-! ## Updates read one way -/

/-- What gives `φ` after an update gives it after the update. -/
theorem holds_upd_mono {Γ Δ : Ctx} {m : Modality} {U : Upd C Γ Δ} {φ ψ : Fml C Δ}
    (hφ : ∀ τ, holds τ ψ → holds τ φ) (σ : State C Γ) (h : holds σ (.upd m U ψ)) :
    holds σ (.upd m U φ) :=
  Upd.afterT_imp h hφ

/-- What gives `φ` after a run gives it after the run. -/
theorem _root_.Solidity.Modality.afterRunTR_imp {α : Type} {m : Modality} {p q : α → Prop}
    {r : TRes α} (h : m.afterRunTR p r) (hpq : ∀ a, p a → q a) : m.afterRunTR q r := by
  cases r with
  | ok a => exact ⟨hpq a h.1, h.2⟩
  | error _ => exact h

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
halt, and pops, by the recursor: locals, `unset` and the ledger's saves
among them. -/
@[implemented_by Upd.totalBM]
def Upd.totalB {Γ Δ : Ctx} (U : Upd C Γ Δ) : Bool :=
  Upd.rec (motive := fun _ _ => Bool) true (fun _ e ih => e.totalB && ih)
    (fun _ _ r ih => r.totalB && ih) (fun _ _ ih => ih) (fun _ _ ih => ih) U

theorem Upd.totalB_eq_totalBM {Γ Δ : Ctx} (U : Upd C Γ Δ) : U.totalB = U.totalBM := by
  induction U with
  | nil => rfl
  | snoc U e ih | decl U x r ih | pop U h ih | drop U h ih =>
    simp only [Upd.totalBM, ← ih]; rfl

theorem Tm.totalB_evalT {Γ : Ctx} (σ : State C Γ) :
    (t : Tm C Γ .val) → t.totalB = true → ∃ v, t.evalT σ = .ok v
  | .pvV _, _ => ⟨_, rfl⟩
  | .app0 (.lit v), _ => ⟨v, rfl⟩

/-- A root and its fields read as a path: `Op0.root` and `Op1.field` do
not halt. -/
theorem Tm.totalP_evalT {Γ : Ctx} (σ : State C Γ) :
    (p : Tm C Γ .path) → p.totalP = true → ∃ v, p.evalT σ = .ok v
  | .app0 (.root r), _ => ⟨(r, []), rfl⟩
  | .app1 (.field f) _ p, h => by
    obtain ⟨⟨r, segs⟩, hv⟩ := Tm.totalP_evalT σ p h
    exact ⟨(r, segs ++ [.field f]), by
      show (do let (r, segs) ← p.evalT σ; pure (r, segs ++ [Semantics.Seg.field f])) = _
      rw [hv]; rfl⟩

theorem Rhs.totalB_evalT {Γ : Ctx} (σ : State C Γ) :
    {t : LTy} → (r : Rhs C Γ t) → r.totalB = true → ∃ v, r.evalT σ = .ok v
  | _, .val t, h => Tm.totalB_evalT σ t h
  | _, .path p, h => by
    obtain ⟨v, hv⟩ := Tm.totalP_evalT σ p h
    exact ⟨some v, by show (do pure (some (← p.evalT σ))) = _; rw [hv]; rfl⟩
  | _, .unset, _ => ⟨_, rfl⟩
  | _, .saveNet, _ => ⟨_, rfl⟩
  | _, .saveNetMt, _ => ⟨_, rfl⟩

/-- An update that cannot halt computes a global part (on the twin). -/
theorem Upd.totalBM_globT {Γ : Ctx} (σ₀ : State C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → U.totalBM = true → ∃ g, U.globT σ₀ = .ok g
  | _, .nil, _ => ⟨σ₀.globE, rfl⟩
  | _, .snoc U (.local i r), h => by
    have h : r.totalB = true ∧ U.totalBM = true := Bool.and_eq_true_iff.mp h
    obtain ⟨g, hg⟩ := Upd.totalBM_globT σ₀ U h.2
    obtain ⟨v, hv⟩ := Rhs.totalB_evalT σ₀ r h.1
    exact ⟨g, by
      change (do UpdElem.globT σ₀ (.local i r) (← U.globT σ₀)) = _
      rw [hg]
      change (do let _ ← r.evalT σ₀; pure g) = _
      rw [hv]; rfl⟩
  | _, .snoc _ (.storage _), h | _, .snoc _ (.memory _), h | _, .snoc _ (.selfBalance ..), h
  | _, .snoc _ (.net ..), h | _, .snoc _ (.pay ..), h | _, .snoc _ (.netMt ..), h
  | _, .snoc _ (.setBalance _), h => absurd h Bool.false_ne_true
  | _, .decl U _ r, h => by
    have h : r.totalB = true ∧ U.totalBM = true := Bool.and_eq_true_iff.mp h
    obtain ⟨g, hg⟩ := Upd.totalBM_globT σ₀ U h.2
    obtain ⟨v, hv⟩ := Rhs.totalB_evalT σ₀ r h.1
    exact ⟨g, by
      change (do let g ← U.globT σ₀; let _ ← r.evalT σ₀; pure g) = _
      rw [hg, hv]; rfl⟩
  | _, .pop U _, h => Upd.totalBM_globT σ₀ U h
  | _, .drop U _, h => Upd.totalBM_globT σ₀ U h

/-- An update that cannot halt computes a global part. -/
theorem Upd.totalB_globT {Γ Δ : Ctx} (σ₀ : State C Γ) (U : Upd C Γ Δ) (h : U.totalB = true) :
    ∃ g, U.globT σ₀ = .ok g :=
  Upd.totalBM_globT σ₀ U (U.totalB_eq_totalBM ▸ h)

/-- **`applyOnRigidFormula`**: a first-order goal read before the update
(`Fml.substU`) gives the update in front of it, under the box for any
update, under the diamond for one that cannot halt. -/
theorem holds_upd_of_substU' {m : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ}
    {φ' : Fml C Γ} (hs : Fml.substU U φ = some φ') (ht : m = .box ∨ U.totalB = true)
    (σ : State C Γ) (h : holds σ φ') : holds σ (.upd m U φ) := by
  refine Upd.afterT_intro (fun e he => ?_) fun _ _ hL _ => (Fml.substU_holds hL φ hs).1 h
  rcases ht with rfl | ht
  · trivial
  · obtain ⟨_, h'⟩ := Upd.totalB_globT σ U ht
    rw [he] at h'; cases h'

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

/-- Whether a modality is the box. -/
def Modality.isBoxS : Modality → Bool
  | .box => true
  | .diamond => false

/-! ## Writes shadowed by a later one

`{… ‖ x := a ‖ … ‖ x := b ‖ …}` sets `x` to `b`: the earlier write goes
(the shadowed elements `\dropEffectlessElementaries` drops, decision 87),
in the same scope (no declaration, pop or frame end between the two), where
`a` cannot halt (`Rhs.totalB`) or under the box, where a halt of the update
makes it true. -/

section Shadow

/-- `W ‖ e`, or `W` where `e` writes the local at position `i` and may go:
its right-hand side cannot halt, or `box`. -/
def UpdElem.unsetSnoc {Γ Δ : Ctx} (box : Bool) (i : Nat) (W : Upd C Γ Δ) :
    UpdElem C Γ Δ → Upd C Γ Δ
  | .local j r => if j.toNat = i ∧ (box || r.totalB) = true then W else .snoc W (.local j r)
  | e => .snoc W e

/-- `Upd.unsetAt`'s compiled twin. -/
def Upd.unsetAtM {Γ : Ctx} (box : Bool) (i : Nat) : {Δ : Ctx} → Upd C Γ Δ → Upd C Γ Δ
  | _, .nil => .nil
  | _, .snoc U e => UpdElem.unsetSnoc box i (Upd.unsetAtM box i U) e
  | _, .decl U x r => .decl U x r
  | _, .pop U h => .pop U h
  | _, .drop U h => .drop U h

/-- Whether the element sets the local at position `n`. -/
def UpdElem.setsAt {Γ Δ : Ctx} (n : Nat) : UpdElem C Γ Δ → Bool
  | .local j _ => j.toNat == n
  | _ => false

/-- `Upd.redecl`'s compiled twin. -/
def Upd.redeclM {Γ : Ctx} (box : Bool) : {Δ : Ctx} → Upd C Γ Δ → {t : LTy} → Idx Δ t →
    Rhs C Γ t → Option (Upd C Γ Δ)
  | _, .snoc U e, _, i, r =>
    if e.setsAt i.toNat then none else (Upd.redeclM box U i r).map (.snoc · e)
  | _, .decl U x r0, _, .here, r =>
    if (box || r0.totalB) = true then some (.decl U x r) else none
  | _, _, _, _, _ => none

/-- `Upd.shadow`'s compiled twin. -/
def Upd.shadowM {Γ : Ctx} (box : Bool) : {Δ : Ctx} → Upd C Γ Δ → Upd C Γ Δ
  | _, .nil => .nil
  | _, .snoc U (.local j r) =>
    let W := (Upd.shadowM box U).unsetAtM box j.toNat
    (W.redeclM box j r).getD (.snoc W (.local j r))
  | _, .snoc U e => .snoc (Upd.shadowM box U) e
  | _, .decl U x r => .decl (Upd.shadowM box U) x r
  | _, .pop U h => .pop (Upd.shadowM box U) h
  | _, .drop U h => .drop (Upd.shadowM box U) h

/-- `U` with its writes to the local at position `i` dropped, down to its
first declaration, pop or frame end (`UpdElem.unsetSnoc`), by the
recursor. -/
@[implemented_by Upd.unsetAtM]
def Upd.unsetAt {Γ : Ctx} (box : Bool) (i : Nat) {Δ : Ctx} (U : Upd C Γ Δ) : Upd C Γ Δ :=
  Upd.rec (motive := fun Δ _ => Upd C Γ Δ) .nil (fun _ e ih => UpdElem.unsetSnoc box i ih e)
    (fun U x r _ => .decl U x r) (fun U h _ => .pop U h) (fun U h _ => .drop U h) U

theorem Upd.unsetAt_eq_unsetAtM {Γ : Ctx} (box : Bool) (i : Nat) {Δ : Ctx} (U : Upd C Γ Δ) :
    U.unsetAt box i = U.unsetAtM box i := by
  induction U with
  | snoc U e ih => simp only [Upd.unsetAtM, ← ih]; rfl
  | _ => rfl

/-- `{U ‖ x := r}` where `i` is the local `x` declares (`Idx.casesOn`), with
no cast: `Δ'.tail` is the context under it. -/
def Upd.declAt {Γ Δ : Ctx} {t₀ t : LTy} (U : Upd C Γ Δ) (x : Var) (i : Idx (t₀ :: Δ) t)
    (r : Rhs C Γ t) : Option (Upd C Γ (t₀ :: Δ)) :=
  Idx.casesOn (motive := fun Δ' t _ => Rhs C Γ t → Upd C Γ Δ'.tail → Option (Upd C Γ Δ')) i
    (fun r U => some (.decl U x r)) (fun _ _ _ => none) r U

/-- `W ‖ i := r` as `W` with the declaration of `i` it shadows given `r`:
`W` declares `i` last, and after it sets only other locals and global
parts; the declaration's right-hand side cannot halt, or `box`; by the
recursor. -/
@[implemented_by Upd.redeclM]
def Upd.redecl {Γ : Ctx} (box : Bool) {Δ : Ctx} (U : Upd C Γ Δ) :
    {t : LTy} → Idx Δ t → Rhs C Γ t → Option (Upd C Γ Δ) :=
  Upd.rec (motive := fun Δ _ => {t : LTy} → Idx Δ t → Rhs C Γ t → Option (Upd C Γ Δ))
    (fun _ _ => none)
    (fun _ e ih => fun i r => if e.setsAt i.toNat then none else (ih i r).map (.snoc · e))
    (fun U x r₀ _ => fun i r => if (box || r₀.totalB) = true then U.declAt x i r else none)
    (fun _ _ _ => fun _ _ => none) (fun _ _ _ => fun _ _ => none) U

theorem Upd.redecl_eq_redeclM {Γ : Ctx} (box : Bool) {Δ : Ctx} (U : Upd C Γ Δ) :
    ∀ {t : LTy} (i : Idx Δ t) (r : Rhs C Γ t), U.redecl box i r = U.redeclM box i r := by
  induction U with
  | snoc U e ih => intro t i r; simp only [Upd.redeclM, ← ih]; rfl
  | decl U x r₀ ih =>
    intro t i r
    cases i <;> first | rfl | (show (if _ then none else none) = none; split <;> rfl)
  | _ => intro t i r; rfl

/-- `W ‖ e` with a write to a local that shadows earlier ones: those
dropped (`Upd.unsetAt`), and the declaration it shadows given its
right-hand side where that fits (`Upd.redecl`). -/
def UpdElem.shadowSnoc {Γ Δ : Ctx} (box : Bool) (W : Upd C Γ Δ) : UpdElem C Γ Δ → Upd C Γ Δ
  | .local j r =>
    let W' := W.unsetAt box j.toNat
    (W'.redecl box j r).getD (.snoc W' (.local j r))
  | e => .snoc W e

/-- `U` with every write shadowed by a later one to the same local in the
same scope dropped (`Upd.unsetAt`), and a declaration a later write
shadows given that write's right-hand side (`Upd.redecl`), by the
recursor. -/
@[implemented_by Upd.shadowM]
def Upd.shadow {Γ : Ctx} (box : Bool) {Δ : Ctx} (U : Upd C Γ Δ) : Upd C Γ Δ :=
  Upd.rec (motive := fun Δ _ => Upd C Γ Δ) .nil (fun _ e ih => UpdElem.shadowSnoc box ih e)
    (fun _ x r ih => .decl ih x r) (fun _ h ih => .pop ih h) (fun _ h ih => .drop ih h) U

theorem Upd.shadow_eq_shadowM {Γ : Ctx} (box : Bool) {Δ : Ctx} (U : Upd C Γ Δ) :
    U.shadow box = U.shadowM box := by
  induction U with
  | nil => rfl
  | snoc U e ih =>
    cases e with
    | «local» j r =>
      simp only [Upd.shadowM, ← ih, ← Upd.unsetAt_eq_unsetAtM, ← Upd.redecl_eq_redeclM]; rfl
    | _ => simp only [Upd.shadowM, ← ih]; rfl
  | decl U x r ih | pop U h ih | drop U h ih => simp only [Upd.shadowM, ← ih]; rfl

/-- An update's outcome and the outcome of it with writes dropped: both
return, to states `R` relates; both halt; or only the first halts, under
the box. -/
def ResRel {α : Type} (box : Bool) (R : α → α → Prop) : Semantics.Res α → Semantics.Res α → Prop
  | .ok a, .ok b => R a b
  | .error _, .error _ => True
  | .error _, .ok _ => box = true
  | .ok _, .error _ => False

theorem ResRel.refl {α : Type} {box : Bool} {R : α → α → Prop} (hR : ∀ a, R a a) :
    (x : Semantics.Res α) → ResRel box R x x
  | .ok a => hR a
  | .error _ => trivial

theorem ResRel.trans_eq {α : Type} {box : Bool} {a b c : Semantics.Res α}
    (h₁ : ResRel box (· = ·) a b) (h₂ : ResRel box (· = ·) b c) : ResRel box (· = ·) a c := by
  cases a <;> cases b <;> cases c <;>
    first | trivial | exact h₁.elim | exact h₂.elim | exact h₁ | exact h₂ | exact h₁.trans h₂

/-- The same continuation after two related outcomes. -/
theorem ResRel.bind_eq {α β : Type} {box : Bool} {a b : Semantics.Res α}
    (h : ResRel box (· = ·) a b) (f : α → Semantics.Res β) :
    ResRel box (· = ·) (a >>= f) (b >>= f) := by
  cases a with
  | error => cases b with
    | error => trivial
    | ok y =>
      show ResRel box _ (.error _) (f y)
      cases f y with
      | error => trivial
      | ok => exact h
  | ok x => cases b with
    | error => exact h.elim
    | ok y =>
      cases (h : x = y)
      exact ResRel.refl (fun _ => rfl) _

/-- **Where an update returns, it with its writes to the local `i` dropped
returns the same global part**; where it halts the other halts too, or the
drop was the box's. -/
theorem Upd.unsetAt_globT {Γ : Ctx} (box : Bool) (i : Nat) (σ₀ : State C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) →
      ResRel box (· = ·) (U.globT σ₀) ((U.unsetAtM box i).globT σ₀)
  | _, .nil => ResRel.refl (fun _ => rfl) _
  | _, .decl U x r => ResRel.refl (fun _ => rfl) _
  | _, .pop U h => ResRel.refl (fun _ => rfl) _
  | _, .drop U h => ResRel.refl (fun _ => rfl) _
  | _, .snoc U e => by
    have ih := Upd.unsetAt_globT box i σ₀ U
    show ResRel box _ (U.globT σ₀ >>= e.globT σ₀)
      ((UpdElem.unsetSnoc box i (U.unsetAtM box i) e).globT σ₀)
    cases e with
    | «local» j r =>
      simp only [UpdElem.unsetSnoc]
      split
      · rename_i hd
        generalize U.globT σ₀ = a at ih ⊢
        generalize (U.unsetAtM box i).globT σ₀ = b at ih ⊢
        cases a with
        | error => cases b with
          | error => trivial
          | ok => exact ih
        | ok g =>
          cases b with
          | error => exact ih.elim
          | ok g' =>
            cases (ih : g = g')
            show ResRel box _ (do let _ ← r.evalT σ₀; pure g) (.ok g)
            cases hr : r.evalT σ₀ with
            | error =>
              show box = true
              rcases Bool.or_eq_true_iff.mp hd.2 with hb | ht
              · exact hb
              · obtain ⟨v, hv⟩ := Rhs.totalB_evalT σ₀ r ht
                rw [hv] at hr; cases hr
            | ok v => rfl
      · exact ResRel.bind_eq ih _
    | _ => exact ResRel.bind_eq ih _

/-- …and leaves every other local as it does. -/
theorem Upd.unsetAt_held {Γ : Ctx} (box : Bool) (i : Nat) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → ∀ {t : LTy} (k : Idx Δ t), k.toNat ≠ i →
      (U.unsetAtM box i).held k = U.held k
  | _, .nil, _, _, _ => rfl
  | _, .decl U x r, _, _, _ => rfl
  | _, .pop U h, _, _, _ => rfl
  | _, .drop U h, _, _, _ => rfl
  | _, .snoc U e, t, k, hk => by
    have ih := Upd.unsetAt_held box i U k hk
    cases e with
    | «local» j r =>
      show (UpdElem.unsetSnoc box i (U.unsetAtM box i) (.local j r)).held k =
        Subst.set (Upd.held U) j r k
      simp only [UpdElem.unsetSnoc]
      split
      · rename_i hd
        unfold Subst.set
        rw [dif_neg (by rw [hd.1]; exact Ne.symm hk)]
        exact ih
      · show Subst.set (Upd.held (U.unsetAtM box i)) j r k = Subst.set (Upd.held U) j r k
        unfold Subst.set
        split
        · rfl
        · exact ih
    | storage _ | memory _ | selfBalance _ _ | net _ _ _ | pay _ _ | netMt _ _ | setBalance _ =>
      exact ih

/-- **A declaration given the right-hand side of the write that shadows
it** returns where the two did, the same global part. -/
theorem Upd.redecl_globT {Γ : Ctx} (box : Bool) (σ₀ : State C Γ) :
    {Δ : Ctx} → (W : Upd C Γ Δ) → {t : LTy} → (i : Idx Δ t) → (r : Rhs C Γ t) →
      {W' : Upd C Γ Δ} → W.redeclM box i r = some W' →
      ResRel box (· = ·) ((Upd.snoc W (.local i r)).globT σ₀) (W'.globT σ₀)
  | _, .snoc U e, _, i, r, W', h => by
    simp only [Upd.redeclM] at h
    split at h
    · cases h
    · obtain ⟨U', hU', rfl⟩ := Option.map_eq_some_iff.1 h
      have ih := Upd.redecl_globT box σ₀ U i r hU'
      have hc : ResRel box (· = ·) ((Upd.snoc (.snoc U e) (.local i r)).globT σ₀)
          ((Upd.snoc (.snoc U (.local i r)) e).globT σ₀) := by
        show ResRel box _ ((U.globT σ₀ >>= e.globT σ₀) >>= (UpdElem.local i r).globT σ₀)
          ((U.globT σ₀ >>= (UpdElem.local i r).globT σ₀) >>= e.globT σ₀)
        cases U.globT σ₀ with
        | error => trivial
        | ok g =>
          show ResRel box _ (e.globT σ₀ g >>= fun g' => do let _ ← r.evalT σ₀; pure g')
            ((do let _ ← r.evalT σ₀; pure g) >>= e.globT σ₀)
          cases r.evalT σ₀ with
          | error => cases e.globT σ₀ g <;> trivial
          | ok v =>
            show ResRel box _ (e.globT σ₀ g >>= fun g' => pure g') (e.globT σ₀ g)
            cases e.globT σ₀ g <;> exact ResRel.refl (fun _ => rfl) _
      exact ResRel.trans_eq hc (ResRel.bind_eq ih _)
  | _, .decl U x r0, _, .here, r, W', h => by
    simp only [Upd.redeclM] at h
    split at h
    · rename_i hb
      cases h
      show ResRel box _
        ((do let g ← U.globT σ₀; let _ ← r0.evalT σ₀; pure g) >>= (UpdElem.local .here r).globT σ₀)
        (do let g ← U.globT σ₀; let _ ← r.evalT σ₀; pure g)
      cases U.globT σ₀ with
      | error => trivial
      | ok g =>
        cases h0 : r0.evalT σ₀ with
        | error =>
          show ResRel box _ (.error _) (do let _ ← r.evalT σ₀; pure g)
          cases r.evalT σ₀ with
          | error => trivial
          | ok =>
            show box = true
            rcases Bool.or_eq_true_iff.mp hb with hb | ht
            · exact hb
            · obtain ⟨v, hv⟩ := Rhs.totalB_evalT σ₀ r0 ht
              rw [hv] at h0; cases h0
        | ok v0 =>
          show ResRel box _ (do let _ ← r.evalT σ₀; pure g) (do let _ ← r.evalT σ₀; pure g)
          exact ResRel.refl (fun _ => rfl) _
    · cases h
  | _, .nil, _, _, _, _, h | _, .pop .., _, _, _, _, h | _, .drop .., _, _, _, _, h => by
    simp only [Upd.redeclM] at h; cases h
  | _, .decl .., _, .there _, _, _, h => by simp only [Upd.redeclM] at h; cases h

/-- …and leaves each local as the two did. -/
theorem Upd.redecl_held {Γ : Ctx} (box : Bool) :
    {Δ : Ctx} → (W : Upd C Γ Δ) → {t : LTy} → (i : Idx Δ t) → (r : Rhs C Γ t) →
      {W' : Upd C Γ Δ} → W.redeclM box i r = some W' →
      ∀ {u : LTy} (k : Idx Δ u), W'.held k = (Upd.snoc W (.local i r)).held k
  | _, .snoc U e, _, i, r, W', h, u, k => by
    simp only [Upd.redeclM] at h
    split at h
    · cases h
    · rename_i he
      obtain ⟨U', hU', rfl⟩ := Option.map_eq_some_iff.1 h
      have ih : ∀ {u : LTy} (k : Idx _ u), U'.held k = (Upd.snoc U (.local i r)).held k :=
        fun k => Upd.redecl_held box U i r hU' k
      cases e with
      | «local» j r2 =>
        have hji : j.toNat ≠ i.toNat := fun hc =>
          he (by simp only [UpdElem.setsAt, hc, beq_self_eq_true])
        show Subst.set (Upd.held U') j r2 k = Subst.set (Subst.set (Upd.held U) j r2) i r k
        by_cases hjk : j.toNat = k.toNat
        · have hik : i.toNat ≠ k.toNat := fun h => hji (hjk.trans h.symm)
          simp only [Subst.set, dif_neg hik, dif_pos hjk]
        · have hk : U'.held k = Subst.set (Upd.held U) i r k := ih k
          simp only [Subst.set] at hk
          simp only [Subst.set, dif_neg hjk, hk]
      | storage _ | memory _ | selfBalance _ _ | net _ _ _ | pay _ _ | netMt _ _ | setBalance _ =>
        exact ih k
  | _, .decl U x r0, _, .here, r, W', h, u, k => by
    simp only [Upd.redeclM] at h
    split at h
    · cases h
      cases k with
      | here => rfl
      | there j => rfl
    · cases h
  | _, .nil, _, _, _, _, h, _, _ | _, .pop .., _, _, _, _, h, _, _
  | _, .drop .., _, _, _, _, h, _, _ => by
    simp only [Upd.redeclM] at h; cases h
  | _, .decl .., _, .there _, _, _, h, _, _ => by simp only [Upd.redeclM] at h; cases h

/-- **Where an update returns, it with its shadowed writes dropped returns
the same global part**; where it halts the other halts too, or the drop
was the box's. -/
theorem Upd.shadow_globT {Γ : Ctx} (box : Bool) (σ₀ : State C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → ResRel box (· = ·) (U.globT σ₀) ((U.shadowM box).globT σ₀)
  | _, .nil => ResRel.refl (fun _ => rfl) _
  | _, .decl U x r => ResRel.bind_eq (Upd.shadow_globT box σ₀ U) _
  | _, .pop U _ => Upd.shadow_globT box σ₀ U
  | _, .drop U _ => Upd.shadow_globT box σ₀ U
  | _, .snoc U e => by
    have ih := Upd.shadow_globT box σ₀ U
    cases e with
    | «local» j r =>
      have hu := Upd.unsetAt_globT box j.toNat σ₀ (U.shadowM box)
      have hs : ResRel box (· = ·) ((Upd.snoc U (.local j r)).globT σ₀)
          ((Upd.snoc ((U.shadowM box).unsetAtM box j.toNat) (.local j r)).globT σ₀) :=
        ResRel.bind_eq (ResRel.trans_eq ih hu) _
      show ResRel box _ _ (Upd.globT σ₀ ((((U.shadowM box).unsetAtM box j.toNat).redeclM box j r).getD
        (.snoc ((U.shadowM box).unsetAtM box j.toNat) (.local j r))))
      cases hd : ((U.shadowM box).unsetAtM box j.toNat).redeclM box j r with
      | none => exact hs
      | some W' => exact ResRel.trans_eq hs (Upd.redecl_globT box σ₀ _ j r hd)
    | _ => exact ResRel.bind_eq ih _

/-- …and leaves each local as the update does. -/
theorem Upd.shadow_held {Γ : Ctx} (box : Bool) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → ∀ {t : LTy} (k : Idx Δ t), (U.shadowM box).held k = U.held k
  | _, .nil, _, _ => rfl
  | _, .decl U x r, _, k => by
    cases k with
    | here => rfl
    | there j => exact Upd.shadow_held box U j
  | _, .pop U h, _, k => Upd.shadow_held box U (k.ext h)
  | _, .drop U h, _, k => Upd.shadow_held box U (k.wk h)
  | _, .snoc U e, _, k => by
    have ih : ∀ {t : LTy} (k : Idx _ t), (U.shadowM box).held k = U.held k :=
      fun k => Upd.shadow_held box U k
    cases e with
    | «local» j r =>
      have hs : (Upd.snoc ((U.shadowM box).unsetAtM box j.toNat) (.local j r)).held k =
          (Upd.snoc U (.local j r)).held k := by
        show Subst.set (Upd.held ((U.shadowM box).unsetAtM box j.toNat)) j r k =
          Subst.set (Upd.held U) j r k
        unfold Subst.set
        split
        · rfl
        · rename_i hjk
          exact (Upd.unsetAt_held box j.toNat (U.shadowM box) k (Ne.symm hjk)).trans (ih k)
      show Upd.held ((((U.shadowM box).unsetAtM box j.toNat).redeclM box j r).getD
        (.snoc ((U.shadowM box).unsetAtM box j.toNat) (.local j r))) k = _
      cases hd : ((U.shadowM box).unsetAtM box j.toNat).redeclM box j r with
      | none => exact hs
      | some W' => exact (Upd.redecl_held box _ j r hd k).trans hs
    | storage _ | memory _ | selfBalance _ _ | net _ _ _ | pay _ _ | netMt _ _ | setBalance _ =>
      exact ih k

/-- **`{U} φ` from `U` with its shadowed writes dropped**: under the box
any write, under the diamond a write that cannot halt. -/
theorem holds_upd_shadow {Γ Δ : Ctx} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ}
    (σ : State C Γ) (h : holds σ (.upd m (U.shadow m.isBoxS) φ)) : holds σ (.upd m U φ) := by
  rw [Upd.shadow_eq_shadowM] at h
  have hr := Upd.shadow_globT m.isBoxS σ U
  refine Upd.afterT_of_lands (fun e he h' => ?_) (fun g σ' hL => ?_) h
  · rw [he] at hr
    cases m with
    | box => trivial
    | diamond =>
      cases hb : (U.shadowM Modality.diamond.isBoxS).globT σ with
      | error e' => exact h'.of_error hb
      | ok => rw [hb] at hr; exact absurd hr Bool.false_ne_true
  · refine ⟨?_, hL.2.1, fun k => ?_⟩
    · rw [hL.1] at hr
      cases hb : (U.shadowM m.isBoxS).globT σ with
      | error => rw [hb] at hr; exact hr.elim
      | ok g' => rw [hb] at hr; cases (hr : g = g'); rfl
    · rw [Upd.shadow_held]
      exact hL.2.2 k

/-- `\dropEffectlessElementaries` on a scoped update under `m`: the
elements setting a local the update pops later (`Upd.simp`, under the box)
and the writes a later one shadows (`Upd.shadow`) dropped. -/
def Upd.simpS {Γ Δ : Ctx} : Modality → Upd C Γ Δ → Upd C Γ Δ
  | .box, U => (U.simp 0).shadow true
  | .diamond, U => U.shadow false

/-- `{U} φ` from `U` simplified. -/
theorem holds_upd_simpS {Γ Δ : Ctx} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ}
    (σ : State C Γ) (h : holds σ (.upd m (U.simpS m) φ)) : holds σ (.upd m U φ) := by
  cases m with
  | box => exact holds_upd_simp σ (holds_upd_shadow (m := .box) σ h)
  | diamond => exact holds_upd_shadow (m := .diamond) σ h

end Shadow

/-! ## Through hidden binders

`{U}{V}` merges where hidden binders stand between the two, as
`Calculus/Merge.lean`'s `Fml.merge2` merges a chain's line: `U` moved under
each (`Upd.lift?`, `Fml.upd_bind_of_lift`), here with `Upd.seqPar`'s
storage. -/

/-- The update `φ` is, with its parts, if it is one. -/
theorem Fml.updHead?_eq {Γ : Ctx} {φ : Fml C Γ} {h : UHead C Γ} (e : φ.updHead? = some h) :
    φ = .upd h.m h.U h.φ := by
  cases φ <;> (cases e; try rfl)

/-- `{W}_m ψ`, with the scope ends `ψ` begins with under `m` merged into
`W` (they print as nothing). -/
def Fml.absorbPops {Γ Δ : Ctx} (m : Modality) (W : Upd C Γ Δ) (ψ : Fml C Δ) : Fml C Γ :=
  match ψ.updHead? with
  | some ⟨m', P, ψ'⟩ =>
    if m' = m ∧ P.popsOnly = true then
      match W.seqPar P with
      | some W' => .upd m W' ψ'
      | none => .upd m W ψ
    else .upd m W ψ
  | none => .upd m W ψ

theorem Fml.absorbPops_holds {Γ Δ : Ctx} {m : Modality} {W : Upd C Γ Δ} {ψ : Fml C Δ}
    (σ : State C Γ) (h : holds σ (Fml.absorbPops m W ψ)) : holds σ (.upd m W ψ) := by
  unfold Fml.absorbPops at h
  split at h
  · rename_i m' P ψ' hψ
    split at h
    · rename_i hc
      split at h
      · rename_i W' hW
        rw [Fml.updHead?_eq hψ]
        obtain ⟨rfl, -⟩ := hc
        exact holds_upd_seqPar hW σ h
      · exact h
    · exact h
  · exact h

/-- `simplifyUpdate` on `{U}_m φ`: the scope ends `φ` begins with merged
into `U` (`Fml.absorbPops`), then `U` simplified (`Upd.simpS`), if that
drops something. -/
def Fml.simpAt {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) : Option (Fml C Γ) :=
  match (Fml.absorbPops m U φ).updHead? with
  | some ⟨m', W, ψ⟩ => if (W.simpS m').size < W.size then some (.upd m' (W.simpS m') ψ) else none
  | none => none

theorem Fml.simpAt_holds {Γ Δ : Ctx} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ}
    {χ : Fml C Γ} (h : Fml.simpAt m U φ = some χ) (σ : State C Γ) (hχ : holds σ χ) :
    holds σ (.upd m U φ) := by
  unfold Fml.simpAt at h
  split at h
  · rename_i m' W ψ hh
    split at h
    · cases h
      refine Fml.absorbPops_holds σ ?_
      rw [Fml.updHead?_eq hh]
      exact holds_upd_simpS σ hχ
    · cases h
  · cases h

/-- `Fml.mergeB`'s compiled twin. -/
def Fml.mergeBM (m : Modality) : {Δ : Ctx} → Fml C Δ → (Γ : Ctx) → Upd C Γ Δ → Option (Fml C Γ)
  | _, .upd m' V ψ, _, U =>
    if m' = m then (U.seqPar V).map (Fml.absorbPops m · ψ) else none
  | _, .bind m' x t ψ, _, U =>
    if (t.notMem || U.keepsNext) = true then
      (U.lift? (t := t)).bind fun U' => (Fml.mergeBM m ψ _ U').map (.bind m' x t)
    else none
  | _, _, _, _ => none

/-- `{U}_m φ` with `U` merged into the update of `φ` under its hidden
binders (`sequentialToParallel`), by the recursor. -/
@[implemented_by Fml.mergeBM]
def Fml.mergeB (m : Modality) {Δ : Ctx} (φ : Fml C Δ) : (Γ : Ctx) → Upd C Γ Δ → Option (Fml C Γ) :=
  Fml.rec (motive := fun Δ _ => (Γ : Ctx) → Upd C Γ Δ → Option (Fml C Γ))
    (tt := fun _ _ => none) (eq := fun _ _ _ _ => none) (defined := fun _ _ _ => none)
    (not := fun _ _ _ _ => none) (and := fun _ _ _ _ _ _ => none)
    (imp := fun _ _ _ _ _ _ => none)
    (upd := fun m' V ψ _ _ U => if m' = m then (U.seqPar V).map (Fml.absorbPops m · ψ) else none)
    (modal := fun _ _ _ _ _ _ _ => none) (havoc := fun _ _ _ _ => none)
    (all := fun _ _ _ _ _ _ => none)
    (bind := fun m' x t _ ih _ U => if (t.notMem || U.keepsNext) = true then
      (U.lift? (t := t)).bind fun U' => (ih _ U').map (.bind m' x t) else none)
    (anon := fun _ _ _ _ _ => none) φ

theorem Fml.mergeB_eq_mergeBM (m : Modality) {Δ : Ctx} (φ : Fml C Δ) :
    ∀ (Γ : Ctx) (U : Upd C Γ Δ), φ.mergeB m Γ U = φ.mergeBM m Γ U := by
  induction φ with
  | bind m' x t ψ ih => intro Γ U; simp only [Fml.mergeBM, ← ih]; rfl
  | _ => intro Γ U; rfl

/-- The merged update gives the two (on the twin). -/
theorem Fml.mergeBM_sound {m : Modality} : {Δ : Ctx} → (φ : Fml C Δ) → {Γ : Ctx} →
    (U : Upd C Γ Δ) → {χ : Fml C Γ} → φ.mergeBM m Γ U = some χ →
      ∀ σ, holds σ χ → holds σ (.upd m U φ)
  | _, .upd m' V ψ, _, U, _, h => by
    simp only [Fml.mergeBM] at h
    split at h
    · rename_i hc
      subst hc
      obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 h
      exact fun σ hψ => holds_upd_seqPar hW σ (Fml.absorbPops_holds σ hψ)
    · cases h
  | _, .bind m' x t ψ, _, U, _, h => by
    simp only [Fml.mergeBM] at h
    split at h
    · rename_i ht
      obtain ⟨U', hU', h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨χ', hχ', rfl⟩ := Option.map_eq_some_iff.1 h
      intro σ hψ
      exact Fml.upd_bind_of_lift hU' ht σ
        (Modality.forallB_imp (fun _ h => Fml.mergeBM_sound ψ U' hχ' _ h) hψ)
    · cases h
  | _, .tt, _, _, _, h | _, .eq .., _, _, _, h | _, .defined _, _, _, _, h
  | _, .not _, _, _, _, h | _, .and .., _, _, _, h | _, .imp .., _, _, _, h
  | _, .modal .., _, _, _, h | _, .havoc _, _, _, _, h | _, .all .., _, _, _, h
  | _, .anon .., _, _, _, h => nomatch h

/-- **The merged update gives the two.** -/
theorem Fml.mergeB_sound {m : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ}
    {χ : Fml C Γ} (h : φ.mergeB m Γ U = some χ) (σ : State C Γ) (hχ : holds σ χ) :
    holds σ (.upd m U φ) :=
  Fml.mergeBM_sound φ U (Fml.mergeB_eq_mergeBM m φ Γ U ▸ h) σ hχ


/-! ## The rules -/

/-- The update rules on scoped formulas, each a rewrite `φ ⇝ ψ` whose `ψ`
gives `φ`.  Hover a constructor for the KeY taclet it is; the last three
are Lean only (hidden binders and scope ends, which KeY's updates do not
have, and a rule after a rule). -/
inductive UpdRuleS : {Γ : Ctx} → Fml C Γ → Fml C Γ → Prop
  /-- `sequentialToParallel2 { \find({u}{u2}phi) \replacewith({u || {u}u2}phi) }`,
  where `{u}u2` reads (`Upd.seqPar`). -/
  | sequentialToParallel {Γ Δ₁ Δ₂ : Ctx} {m : Modality} {u : Upd C Γ Δ₁} {u2 : Upd C Δ₁ Δ₂}
      {w : Upd C Γ Δ₂} {φ : Fml C Δ₂} (hw : u.seqPar u2 = some w) :
      UpdRuleS (.upd m u (.upd m u2 φ)) (.upd m w φ)
  /-- `simplifyUpdate2 { \find({u}phi)
  \varcond(\dropEffectlessElementaries(u, phi, result)) \replacewith(result) }`:
  the elements setting a local `u` pops later, under the box, and the
  writes a later one shadows (`Upd.simpS`). -/
  | simplifyUpdate {Γ Δ : Ctx} {m : Modality} {u : Upd C Γ Δ} {φ : Fml C Δ} :
      UpdRuleS (.upd m u φ) (.upd m (u.simpS m) φ)
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
  /-- Lean only: `sequentialToParallel` through the hidden binders between
  the two updates (`Fml.mergeB`), the scope ends after them absorbed. -/
  | mergeHidden {Γ Δ : Ctx} {m : Modality} {u : Upd C Γ Δ} {φ : Fml C Δ} {χ : Fml C Γ}
      (hw : φ.mergeB m Γ u = some χ) : UpdRuleS (.upd m u φ) χ
  /-- Lean only: the scope ends `φ` begins with, under `m`, merged into `u`
  (`Fml.absorbPops`; they print as nothing). -/
  | absorbPops {Γ Δ : Ctx} {m : Modality} {u : Upd C Γ Δ} {φ : Fml C Δ} :
      UpdRuleS (.upd m u φ) (Fml.absorbPops m u φ)
  /-- Lean only: one rule after another. -/
  | trans {Γ : Ctx} {φ ψ χ : Fml C Γ} : UpdRuleS φ ψ → UpdRuleS ψ χ → UpdRuleS φ χ

/-- **Soundness of the update rules**: what a rule rewrites to gives what
it rewrote.

Example: `x = 1; y = x;` leaves `{ x := 1 } { y := x } y = 1`;
`sequentialToParallel` rewrites it to `{ x := 1 ‖ y := 1 } y = 1`, which
gives it. -/
theorem UpdRuleS.sound {Γ : Ctx} {φ ψ : Fml C Γ} : UpdRuleS φ ψ → ∀ σ, holds σ ψ → holds σ φ
  | .sequentialToParallel hw, σ, h => holds_upd_seqPar hw σ h
  | .simplifyUpdate, σ, h => holds_upd_simpS σ h
  | .applySkip hm, σ, h => (holds_upd_nil _ hm σ).2 h
  | .applyOnRigid hs ht, σ, h => holds_upd_of_substU' hs ht σ h
  | .mergeHidden hw, σ, h => Fml.mergeB_sound hw σ h
  | .absorbPops, σ, h => Fml.absorbPops_holds σ h
  | .trans h₁ h₂, σ, h => h₁.sound σ (h₂.sound σ h)

/-- `Fml.simpAt` is `absorbPops`, then `simplifyUpdate`. -/
theorem Fml.simpAt_rule {Γ Δ : Ctx} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ}
    {χ : Fml C Γ} (h : Fml.simpAt m U φ = some χ) : UpdRuleS (.upd m U φ) χ := by
  unfold Fml.simpAt at h
  split at h
  · rename_i m' W ψ hh
    split at h
    · cases h
      have he := Fml.updHead?_eq hh
      exact .trans .absorbPops (by rw [he]; exact .simplifyUpdate)
    · cases h
  · cases h

/-! ## One rule at a time -/

/-- The rules, by name (`sol_upd r`). -/
inductive UpdRuleNameS where
  | sequentialToParallel
  | simplifyUpdate
  | applySkip
  | applyOnRigid
  deriving DecidableEq, Repr

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
  | .sequentialToParallel => φ.mergeB m Γ U
  | .simplifyUpdate => Fml.simpAt m U φ
  | .applySkip => U.skipS φ
  | .applyOnRigid => if m = .box ∨ U.totalB = true then Fml.substU U φ else none

/-- When rule `r` fits at the top of `{U} φ`, what it returns is an
`UpdRuleS` rewrite of `{U} φ`. -/
theorem UpdRuleNameS.top_rule {Γ Δ : Ctx} {r : UpdRuleNameS} {m : Modality} {U : Upd C Γ Δ}
    {φ : Fml C Δ} {ψ : Fml C Γ} (h : r.top m U φ = some ψ) : UpdRuleS (.upd m U φ) ψ := by
  cases r with
  | sequentialToParallel => exact .mergeHidden h
  | simplifyUpdate => exact Fml.simpAt_rule h
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

/-- `{U} φ` with its popped elements dropped under the box and its
shadowed writes (`Upd.simpS`), and without the braces when nothing is left
and `φ` has no modality. -/
def Fml.cleanS {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) : Fml C Γ :=
  ((U.simpS m).skipS φ).getD (.upd m (U.simpS m) φ)

/-- `Fml.cleanB`'s compiled twin. -/
def Fml.cleanBM : {Γ : Ctx} → Fml C Γ → Fml C Γ
  | _, .bind m x t φ => .bind m x t (Fml.cleanBM φ)
  | _, .upd m U φ => Fml.cleanS m U φ
  | _, φ => φ

/-- The first update under the hidden binders in front, cleaned
(`Fml.cleanS`), by the recursor. -/
@[implemented_by Fml.cleanBM]
def Fml.cleanB {Γ : Ctx} (φ : Fml C Γ) : Fml C Γ :=
  Fml.rec (motive := fun Γ _ => Fml C Γ) (tt := .tt) (eq := fun a b => .eq a b)
    (defined := fun t => .defined t) (not := fun φ _ => .not φ)
    (and := fun φ ψ _ _ => .and φ ψ) (imp := fun φ ψ _ _ => .imp φ ψ)
    (upd := fun m U φ _ => Fml.cleanS m U φ) (modal := fun m P κ φ _ => .modal m P κ φ)
    (havoc := fun φ _ => .havoc φ) (all := fun x p φ _ => .all x p φ)
    (bind := fun m x t _ ih => .bind m x t ih) (anon := fun xs φ _ => .anon xs φ) φ

theorem Fml.cleanB_eq_cleanBM {Γ : Ctx} (φ : Fml C Γ) : φ.cleanB = φ.cleanBM := by
  induction φ with
  | bind m x t φ ih => simp only [Fml.cleanBM, ← ih]; rfl
  | _ => rfl

/-- `{U} φ`, merged with an update of the same modality at the head of `φ`,
under its hidden binders (`Fml.mergeB`), then cleaned. -/
def Fml.mkUpdS {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) : Fml C Γ :=
  match φ.mergeB m Γ U with
  | some χ => χ.cleanB
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
  refine holds_upd_simpS σ ?_
  change holds σ (((U.simpS m).skipS φ).getD (.upd m (U.simpS m) φ)) at h
  generalize U.simpS m = U' at h ⊢
  cases hs : U'.skipS φ with
  | some ψ => rw [hs] at h; exact Upd.skipS_holds hs σ h
  | none => rw [hs] at h; exact h

/-- The first update under the hidden binders, cleaned, gives it (on the
twin). -/
theorem Fml.cleanBM_holds : {Γ : Ctx} → (φ : Fml C Γ) → ∀ σ, holds σ φ.cleanBM → holds σ φ
  | _, .bind _ _ _ φ, _, h => Modality.forallB_imp (fun _ h => Fml.cleanBM_holds φ _ h) h
  | _, .upd m U φ, σ, h => Fml.cleanS_holds m U φ σ h
  | _, .tt, _, h | _, .eq .., _, h | _, .defined _, _, h | _, .not _, _, h | _, .and .., _, h
  | _, .imp .., _, h | _, .modal .., _, h | _, .havoc _, _, h | _, .all .., _, h
  | _, .anon .., _, h => h

theorem Fml.mkUpdS_holds {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ)
    (σ : State C Γ) (h : holds σ (Fml.mkUpdS m U φ)) : holds σ (.upd m U φ) := by
  unfold Fml.mkUpdS at h
  split at h
  · rename_i χ hχ
    exact Fml.mergeB_sound hχ σ (Fml.cleanBM_holds χ σ (Fml.cleanB_eq_cleanBM χ ▸ h))
  · exact Fml.cleanS_holds _ _ _ σ h

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

/-- A scoped formula is valid where a rule's rewrite of it is, or, where
the rule fits nowhere, itself (`sol_upd r`). -/
theorem Valid.of_updAtSD (r : UpdRuleNameS) {φ : Fml C []} (h : Valid ((φ.updAtS r).getD φ)) :
    Valid φ := by
  cases hr : φ.updAtS r with
  | none => rw [hr] at h; exact h
  | some ψ => rw [hr] at h; exact Valid.of_updAtS hr h

end Solidity
