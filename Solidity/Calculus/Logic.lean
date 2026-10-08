import Solidity.Calculus.Hyp
import Solidity.Calculus.UpdateRules
import Solidity.Calculus.TermTaclets

/-!
# The closer's sequent calculus: `Γ ⊢ φ`

`Proves Γ φ` is the sequent calculus the closer runs on a leaf the scoped
strategy leaves (`Calculus/Core/Logic.lean` is the calculus on programs):
the context `Γ` holds what sits in front of the current formula — the
preconditions, the updates, the quantified locals — and the rules move a
connective into it (`impRight`, `allRight`, `{U}` by `updIntro`), merge and
simplify its updates (`sequentialToParallel`, `simplifyUpdate`), apply them
to a first-order goal (`applyOnRigidFormula`), rewrite by a term taclet
(`rewrite`, `updRw`), and leave the calculus where no modality is left
(`close`) or the context refutes itself (`closeFalse`).  Each constructor is
written as KeY writes a sequent rule, its premises above its conclusion,
`dl{ ..Γ, c ⟹[R] φ }` being `Proves R (Γ ++ [.pre c]) φ`
(`RuleSyntax.lean`), and the rules KeY names otherwise have its names too
(`Proves.impRight` for `intro`).  `Proves.sound` says once and for all that
a derivation is a proof.

The judgement is indexed by a rule set (`RuleSet`, `Hyp.lean`) as the
scoped one is; none of these rules is a program rule, so the index is read
by none.  The program rules and their soundness went with today's rule
table (W4 `calc-del`, `docs/intrinsic.md`); the update in front of a
`⟨⟩ φ` still goes (`emptyModality`).

An update never panics (`Upd.apply_ne_panic`), which is what lets an update
rule's premise read a halt as the box reads a revert.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-- `Γ ⊢ φ`: the calculus proves `φ` in the context `Γ`; `Γ ⊢ₖ φ`: solkey's
rules alone do. -/
inductive Proves : RuleSet → List (Hyp C) → Fml C → Prop
  /-- `impRight`: the precondition moves into the context. -/
  | intro {R : RuleSet} {Γ : List (Hyp C)} {a φ : Fml C} (h : dl{ ..Γ, a ⟹[R] φ }) :
      dl{ ..Γ ⟹[R] a → φ }
  /-- `allRight`: a quantified local joins the context, holding any value of
  its type. -/
  | allIntro {R : RuleSet} {Γ : List (Hyp C)} {x : Var} {p : PrimTy} {φ : Fml C}
      (h : dl{ ..Γ, ∀ p x ⟹[R] φ }) : dl{ ..Γ ⟹[R] ‹.all x p φ› }
  /-- An update in front of the formula joins the context: `⟹ {U} φ` is
  `{U} ⟹ φ`, the sequent KeY writes with the update on the formula.  The
  snapshot `{ old := storage }` of a specification (`Calculus/Spec.lean`)
  enters the derivation so. -/
  | updIntro {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {U : Upd C} {φ : Fml C}
      (h : dl{ ..Γ, {U} ⟹[R] φ }) : dl{ ..Γ ⟹[R] {U} φ }
  /-- `emptyModality`: `⟨⟩ φ` and `[] φ` are `φ`. -/
  | empty {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {φ : Fml C} (h : dl{ ..Γ ⟹[R] φ }) :
      dl{ ..Γ ⟹[R] ⟨[ ]⟩ φ }
  /-- A term taclet as a rewrite rule (`TermTaclet`, `Calculus/TermTaclets.lean`):
  `t` becomes `t'` in every equation of the sequent, at any depth
  (`Hyp.rwEq`, `Fml.rwEq`).  The derivation names the taclet; why it is
  sound is `TermTaclet.sound`, on the `⊨` side. -/
  | rewrite {R : RuleSet} {Γ : List (Hyp C)} {φ : Fml C} {t t' : Term C}
      (r : TermTaclet t t') (d : dl{ ..(Hyp.rwEq (t, t') Γ) ⟹[R] ‹Fml.rwEq (t, t') φ› }) :
      dl{ ..Γ ⟹[R] φ }
  /-- A term taclet inside the context's updates: `t` becomes `t'` in the
  right-hand sides of every box update (`Hyp.rwUpd`), where `t'` cannot halt
  (`Tm.total`), so returns whatever `t` returns.  With `rewrite` it reaches
  the whole sequent, as mini-solkey's `rewrite` does. -/
  | updRw {R : RuleSet} {Γ : List (Hyp C)} {φ : Fml C} {t t' : Term C}
      (r : TermTaclet t t') (ht : t'.total = true) (d : dl{ ..(Hyp.rwUpd (t, t') Γ) ⟹[R] φ }) :
      dl{ ..Γ ⟹[R] φ }
  /-- `sequentialToParallel`: the last two updates of the context merge into
  one parallel update, the first substituted into the second, when the first
  writes only locals (`UpdRule.sequentialToParallel`). -/
  | merge {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {U V : Upd C} {φ : Fml C}
      (hU : U.envOnly = true) (h : dl{ ..Γ, {U ‖ {U}V} ⟹[R] φ }) :
      dl{ ..Γ, {U}, {V} ⟹[R] φ }
  /-- `sequentialToParallel` over a storage write, `{storage := s ‖ {storage := s}V}`,
  for a `V` whose storage reads are all `storage` terms (`Upd.mergeStorage_holds`). -/
  | mergeStorage {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {s : STerm C} {V : Upd C}
      {φ : Fml C} (h : Proves R (Γ ++ [.upd m (.storage s :: V.withSt s)]) φ)
      (hV : V.all (·.stExplicit) = true := by rfl) :
      dl{ ..Γ, {storage := s}, {V} ⟹[R] φ }
  /-- `simplifyUpdate`: the effectless elements of the last update are
  dropped (`Upd.dropEffectless`). -/
  | simplify {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {U : Upd C} {φ : Fml C}
      (h : Proves R (Γ ++ [.upd m (U.dropEffectless φ.vars)]) φ) : dl{ ..Γ, {U} ⟹[R] φ }
  /-- `applyOnRigidFormula` under the box: the last update, of locals (or
  locals and a storage write, under a goal that reads no storage), applied to
  a first-order goal and dropped (`Fml.subst_box`, `Fml.subst_box_st`). -/
  | applyOnRigidBox {R : RuleSet} {Γ : List (Hyp C)} {U : Upd C} {φ : Fml C}
      (h : dl{ ..Γ ⟹[R] ‹φ.subst U› })
      (hU : (U.envOnly || U.localsOrStorage && φ.stFree) = true := by first | rfl | decide)
      (hr : φ.rigid = true := by first | rfl | decide)
      (hs : φ.sortedFor U = true := by first | rfl | decide) :
      dl{ ..Γ, {U} [ ] ⟹[R] φ }
  /-- `applyOnRigidFormula` for a storage write under the box: `s` for every
  `storage` of a first-order goal (`Fml.withSt_box`). -/
  | applyStorageBox {R : RuleSet} {Γ : List (Hyp C)} {s : STerm C} {φ : Fml C}
      (h : dl{ ..Γ ⟹[R] ‹φ.withSt s› })
      (hr : φ.rigid = true := by first | rfl | decide)
      (he : φ.stExplicit = true := by first | rfl | decide) :
      dl{ ..Γ, {storage := s} [ ] ⟹[R] φ }
  /-- `closeFalse`: a context that refutes itself closes any goal.  KeY's
  `closeFalse` has no premise: it closes `false ⟹`, the antecedent a
  condition became when its updates were applied and it was simplified.
  This rule is KeY's `cut` on `false` followed by `closeFalse` on the TRUE
  goal; the FALSE goal, the context refuted (`Γ ⟹ false`), is the premise,
  which the closer proves (`Derive.splitRes`).  A deviation in shape. -/
  | closeFalse {R : RuleSet} {Γ : List (Hyp C)} {φ : Fml C} (h : dl{ ..Γ ⟹[R] false }) :
      dl{ ..Γ ⟹[R] φ }
  /-- Leave the calculus: with no modality left anywhere in the sequent, what
  is left is proved in the logic. -/
  | close {R : RuleSet} {Γ : List (Hyp C)} {φ : Fml C} (h : Valid (Hyp.wrap Γ φ))
      (hφ : (Hyp.wrap Γ φ).modalFree = true := by first | rfl | decide) : dl{ ..Γ ⟹[R] φ }

namespace Proves
scoped notation:25 Γ:26 " ⊢ " φ:26 => Proves RuleSet.all Γ φ
scoped notation:25 "⊢ " φ:26 => Proves RuleSet.all [] φ
scoped notation:25 Γ:26 " ⊢ₖ " φ:26 => Proves RuleSet.solkey Γ φ
scoped notation:25 "⊢ₖ " φ:26 => Proves RuleSet.solkey [] φ
end Proves

/-! ### The rules by solkey's names

The constructors whose rule KeY has under another name, under that name too:
`apply Proves.impRight` is `apply Proves.intro`. -/

/-- `impRight` (`intro`). -/
theorem Proves.impRight {R : RuleSet} {Γ : List (Hyp C)} {a φ : Fml C}
    (h : dl{ ..Γ, a ⟹[R] φ }) : dl{ ..Γ ⟹[R] a → φ } := .intro h

/-- `allRight` (`allIntro`). -/
theorem Proves.allRight {R : RuleSet} {Γ : List (Hyp C)} {x : Var} {p : PrimTy} {φ : Fml C}
    (h : dl{ ..Γ, ∀ p x ⟹[R] φ }) : dl{ ..Γ ⟹[R] ‹.all x p φ› } := .allIntro h

/-- `emptyModality` (`empty`). -/
theorem Proves.emptyModality {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {φ : Fml C}
    (h : dl{ ..Γ ⟹[R] φ }) : dl{ ..Γ ⟹[R] ⟨[ ]⟩ φ } := .empty h

/-- `sequentialToParallel` (`merge`). -/
theorem Proves.sequentialToParallel {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {U V : Upd C}
    {φ : Fml C} (hU : U.envOnly = true) (h : dl{ ..Γ, {U ‖ {U}V} ⟹[R] φ }) :
    dl{ ..Γ, {U}, {V} ⟹[R] φ } := .merge hU h

/-- `sequentialToParallel` over a storage write (`mergeStorage`). -/
theorem Proves.sequentialToParallelStorage {R : RuleSet} {Γ : List (Hyp C)} {m : Modality}
    {s : STerm C} {V : Upd C} {φ : Fml C}
    (h : Proves R (Γ ++ [.upd m (.storage s :: V.withSt s)]) φ)
    (hV : V.all (·.stExplicit) = true := by rfl) :
    dl{ ..Γ, {storage := s}, {V} ⟹[R] φ } := .mergeStorage h hV

/-- `simplifyUpdate` (`simplify`). -/
theorem Proves.simplifyUpdate {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {U : Upd C}
    {φ : Fml C} (h : Proves R (Γ ++ [.upd m (U.dropEffectless φ.vars)]) φ) :
    dl{ ..Γ, {U} ⟹[R] φ } := .simplify h

/-- `applyOnRigidFormula` under the box (`applyOnRigidBox`). -/
theorem Proves.applyOnRigidFormula {R : RuleSet} {Γ : List (Hyp C)} {U : Upd C} {φ : Fml C}
    (h : dl{ ..Γ ⟹[R] ‹φ.subst U› })
    (hU : (U.envOnly || U.localsOrStorage && φ.stFree) = true := by first | rfl | decide)
    (hr : φ.rigid = true := by first | rfl | decide)
    (hs : φ.sortedFor U = true := by first | rfl | decide) :
    dl{ ..Γ, {U} [ ] ⟹[R] φ } := .applyOnRigidBox h hU hr hs

theorem Hyp.wrap_append (Γ Δ : List (Hyp C)) (φ : Fml C) :
    Hyp.wrap (Γ ++ Δ) φ = Hyp.wrap Γ (Hyp.wrap Δ φ) := by
  induction Γ with
  | nil => rfl
  | cons h Γ ih => cases h <;> simp [Hyp.wrap, ih]

/-! ## The states a context leads to -/

/-- `Reaches Γ σ τ`: running the context `Γ` from `σ` ends in `τ` — every
update returns, every precondition holds where it is met, and a `havoc`
leaves any storage and ledger. -/
def Hyp.Reaches : List (Hyp C) → State → State → Prop
  | [], σ, τ => τ = σ
  | .pre a :: Γ, σ, τ => holds σ a ∧ Hyp.Reaches Γ σ τ
  | .upd _ U :: Γ, σ, τ => ∃ ρ, U.apply σ = .ok ρ ∧ Hyp.Reaches Γ ρ τ
  | .havoc :: Γ, σ, τ => ∃ st nt, Hyp.Reaches Γ (σ.havoc st nt) τ
  | .all x p :: Γ, σ, τ => ∃ v, p.admits v ∧ Hyp.Reaches Γ (σ.setEnv x (.val v)) τ
  | .anon xs :: Γ, σ, τ => ∃ b, Hyp.Reaches Γ (σ.anon xs b) τ

/-- What follows a context is judged only in the states it leads to. -/
theorem Hyp.wrap_reach {A B : Fml C} : (Γ : List (Hyp C)) → ∀ σ,
    (∀ τ, Hyp.Reaches Γ σ τ → holds τ A → holds τ B) →
      holds σ (Hyp.wrap Γ A) → holds σ (Hyp.wrap Γ B)
  | [], σ, h => h σ rfl
  | .pre _ :: Γ, σ, h => fun hA ha => Hyp.wrap_reach Γ σ (fun τ hr => h τ ⟨ha, hr⟩) (hA ha)
  | .upd m U :: Γ, σ, h => by
    simp only [Hyp.wrap, holds]
    cases hU : U.apply σ with
    | error _ => exact id
    | ok ρ => exact Hyp.wrap_reach Γ ρ (fun τ hr => h τ ⟨ρ, hU, hr⟩)
  | .havoc :: Γ, σ, h => fun hA st nt =>
    Hyp.wrap_reach Γ _ (fun τ hr => h τ ⟨st, nt, hr⟩) (hA st nt)
  | .all _ _ :: Γ, σ, h => fun hA v hv =>
    Hyp.wrap_reach Γ _ (fun τ hr => h τ ⟨v, hv, hr⟩) (hA v hv)
  | .anon _ :: Γ, σ, h => fun hA b =>
    Hyp.wrap_reach Γ _ (fun τ hr => h τ ⟨b, hr⟩) (hA b)

/-- An implication between two formulas survives wrapping both in the same
context. -/
theorem Hyp.wrap_mono {ψ φ : Fml C} (h : ∀ σ, holds σ ψ → holds σ φ) (Γ : List (Hyp C))
    (σ : State) : holds σ (Hyp.wrap Γ ψ) → holds σ (Hyp.wrap Γ φ) :=
  Hyp.wrap_reach Γ σ fun τ _ => h τ

/-- A state `Γ ++ Δ` leads to is one `Δ` leads to from a state `Γ` leads to. -/
theorem Hyp.reaches_append : (Γ Δ : List (Hyp C)) → ∀ σ τ,
    Hyp.Reaches (Γ ++ Δ) σ τ → ∃ ρ, Hyp.Reaches Γ σ ρ ∧ Hyp.Reaches Δ ρ τ
  | [], _, σ, _, h => ⟨σ, rfl, h⟩
  | .pre _ :: Γ, Δ, σ, τ, ⟨ha, h⟩ =>
    let ⟨ρ, h₁, h₂⟩ := Hyp.reaches_append Γ Δ σ τ h
    ⟨ρ, ⟨ha, h₁⟩, h₂⟩
  | .upd _ _ :: Γ, Δ, _, τ, ⟨ρ', hU, h⟩ =>
    let ⟨ρ, h₁, h₂⟩ := Hyp.reaches_append Γ Δ ρ' τ h
    ⟨ρ, ⟨ρ', hU, h₁⟩, h₂⟩
  | .havoc :: Γ, Δ, _, τ, ⟨st, nt, h⟩ =>
    let ⟨ρ, h₁, h₂⟩ := Hyp.reaches_append Γ Δ _ τ h
    ⟨ρ, ⟨st, nt, h₁⟩, h₂⟩
  | .all _ _ :: Γ, Δ, _, τ, ⟨v, hv, h⟩ =>
    let ⟨ρ, h₁, h₂⟩ := Hyp.reaches_append Γ Δ _ τ h
    ⟨ρ, ⟨v, hv, h₁⟩, h₂⟩
  | .anon _ :: Γ, Δ, _, τ, ⟨b, h⟩ =>
    let ⟨ρ, h₁, h₂⟩ := Hyp.reaches_append Γ Δ _ τ h
    ⟨ρ, ⟨b, h₁⟩, h₂⟩

/-- No diamond update in the context: a halting update proves what follows. -/
def Hyp.boxOnly : List (Hyp C) → Bool
  | [] => true
  | .upd .diamond _ :: _ => false
  | _ :: Γ => Hyp.boxOnly Γ

/-- Behind a context with no diamond, what holds in every state it leads to
holds. -/
theorem Hyp.wrap_of_reaches {φ : Fml C} : (Γ : List (Hyp C)) → Hyp.boxOnly Γ = true → ∀ σ,
    (∀ τ, Hyp.Reaches Γ σ τ → holds τ φ) → holds σ (Hyp.wrap Γ φ)
  | [], _, σ, h => h σ rfl
  | .pre _ :: Γ, hb, σ, h => fun ha => Hyp.wrap_of_reaches Γ hb σ (fun τ hr => h τ ⟨ha, hr⟩)
  | .upd .box U :: Γ, hb, σ, h => by
    simp only [Hyp.wrap, holds]
    cases hU : U.apply σ with
    | error _ => trivial
    | ok ρ => exact Hyp.wrap_of_reaches Γ hb ρ (fun τ hr => h τ ⟨ρ, hU, hr⟩)
  | .upd .diamond _ :: _, hb, _, _ => by cases hb
  | .havoc :: Γ, hb, σ, h => fun st nt =>
    Hyp.wrap_of_reaches Γ hb _ (fun τ hr => h τ ⟨st, nt, hr⟩)
  | .all _ _ :: Γ, hb, σ, h => fun v hv =>
    Hyp.wrap_of_reaches Γ hb _ (fun τ hr => h τ ⟨v, hv, hr⟩)
  | .anon _ :: Γ, hb, σ, h => fun b =>
    Hyp.wrap_of_reaches Γ hb _ (fun τ hr => h τ ⟨b, hr⟩)

/-- What is valid is valid behind a context with no diamond. -/
theorem Hyp.valid_wrap {φ : Fml C} {Γ : List (Hyp C)} (hb : Hyp.boxOnly Γ = true) (h : Valid φ) :
    Valid (Hyp.wrap Γ φ) :=
  fun σ => Hyp.wrap_of_reaches Γ hb σ fun τ _ => h τ

/-- Past a `havoc`, what came before is forgotten: a sequent valid from the
`havoc` on is valid behind a context with no diamond in front of it. -/
theorem Hyp.valid_after_havoc {φ : Fml C} {Γ Δ : List (Hyp C)} (hb : Hyp.boxOnly Γ = true)
    (h : Valid (Hyp.wrap Δ φ)) : Valid (Hyp.wrap (Γ ++ .havoc :: Δ) φ) := by
  rw [Hyp.wrap_append]
  exact Hyp.valid_wrap hb fun σ _ _ => h _

/-- `Hyp.wrap_mono` for three premises, as a branch has. -/
theorem Hyp.wrap_mono₃ {ψ₁ ψ₂ ψ₃ φ : Fml C}
    (h : ∀ σ, holds σ ψ₁ → holds σ ψ₂ → holds σ ψ₃ → holds σ φ) :
    (Γ : List (Hyp C)) → ∀ σ, holds σ (Hyp.wrap Γ ψ₁) → holds σ (Hyp.wrap Γ ψ₂) →
      holds σ (Hyp.wrap Γ ψ₃) → holds σ (Hyp.wrap Γ φ)
  | [] => h
  | .pre _ :: Γ => fun σ h₁ h₂ h₃ ha => Hyp.wrap_mono₃ h Γ σ (h₁ ha) (h₂ ha) (h₃ ha)
  | .upd m U :: Γ => fun σ => by
    simp only [Hyp.wrap, holds]
    cases U.apply σ with
    | error _ => exact fun h _ _ => h
    | ok τ => exact Hyp.wrap_mono₃ h Γ τ
  | .havoc :: Γ => fun σ h₁ h₂ h₃ st nt =>
    Hyp.wrap_mono₃ h Γ _ (h₁ st nt) (h₂ st nt) (h₃ st nt)
  | .all _ _ :: Γ => fun σ h₁ h₂ h₃ v hv =>
    Hyp.wrap_mono₃ h Γ _ (h₁ v hv) (h₂ v hv) (h₃ v hv)
  | .anon _ :: Γ => fun σ h₁ h₂ h₃ b =>
    Hyp.wrap_mono₃ h Γ _ (h₁ b) (h₂ b) (h₃ b)

/-- `Hyp.wrap_mono` for two premises. -/
theorem Hyp.wrap_mono₂ {ψ₁ ψ₂ φ : Fml C} (h : ∀ σ, holds σ ψ₁ → holds σ ψ₂ → holds σ φ)
    (Γ : List (Hyp C)) (σ : State) (h₁ : holds σ (Hyp.wrap Γ ψ₁)) (h₂ : holds σ (Hyp.wrap Γ ψ₂)) :
    holds σ (Hyp.wrap Γ φ) :=
  Hyp.wrap_mono₃ (ψ₃ := .tt) (fun σ h₁ h₂ _ => h σ h₁ h₂) Γ σ h₁ h₂
    (Hyp.wrap_mono (ψ := ψ₁) (φ := .tt) (fun _ _ => trivial) Γ σ h₁)

/-- A conjunction holds behind a context where each of its conjuncts does. -/
theorem Hyp.wrap_conj (Γ : List (Hyp C)) : (φs : List (Fml C)) →
    (∀ φ ∈ φs, Valid (Hyp.wrap Γ φ)) → φs ≠ [] → ∀ σ, holds σ (Hyp.wrap Γ (Fml.conj φs))
  | [φ], h, _, σ => h φ List.mem_cons_self σ
  | φ :: ψ :: φs, h, _, σ =>
    Hyp.wrap_mono₂ (fun _ h₁ h₂ => by simp only [Fml.conj, holds] at h₂ ⊢; exact ⟨h₁, h₂⟩) Γ σ
      (h φ List.mem_cons_self σ) (Hyp.wrap_conj Γ (ψ :: φs) (fun χ hχ => h χ (List.mem_cons_of_mem _ hχ)) (by simp) σ)

/-- A variable of a formula is a variable of the formula wrapped in a context. -/
theorem Hyp.vars_wrap {x : Var} {φ : Fml C} :
    (Γ : List (Hyp C)) → x ∈ φ.vars → x ∈ (Hyp.wrap Γ φ).vars
  | [], h => h
  | .pre _ :: Γ, h | .upd _ _ :: Γ, h | .havoc :: Γ, h | .all _ _ :: Γ, h | .anon _ :: Γ, h => by
    simp [Hyp.wrap, Fml.vars, Hyp.vars_wrap Γ h]

/-! ### The Theory rewrite -/

/-- Rewriting the context and the goal is rewriting the sequent. -/
theorem Hyp.wrap_rwEq (q : Term C × Term C) (φ : Fml C) :
    (Γ : List (Hyp C)) → Hyp.wrap (Hyp.rwEq q Γ) (φ.rwEq q) = (Hyp.wrap Γ φ).rwEq q
  | [] => rfl
  | .pre _ :: Γ | .upd _ _ :: Γ | .havoc :: Γ | .all _ _ :: Γ | .anon _ :: Γ => by
    simp only [Hyp.rwEq, Hyp.wrap, Fml.rwEq, Hyp.wrap_rwEq q φ Γ]

/-- A sequent rewritten by a Theory equation holds where the sequent does. -/
theorem Proves.rewrite_sound {Γ : List (Hyp C)} {φ : Fml C} {t t' : Term C}
    (h : Term.Theq t t') (d : Valid (Hyp.wrap (Hyp.rwEq (t, t') Γ) (Fml.rwEq (t, t') φ))) :
    Valid (Hyp.wrap Γ φ) := fun σ => by
  have hσ : holds σ (Hyp.wrap (Hyp.rwEq (t, t') Γ) (Fml.rwEq (t, t') φ)) := d σ
  rw [Hyp.wrap_rwEq] at hσ
  exact (Fml.rwEq_holds (q := (t, t')) h _ σ).1 hσ

/-! ### The update rules -/

/-- A context whose box updates are rewritten gives the context: each
rewritten box update gives the update (`Upd.rw_box`). -/
theorem Hyp.rwUpd_wrap {q : Term C × Term C} (hq : Term.EvalRefines q.1 q.2) {φ : Fml C} :
    (Γ : List (Hyp C)) → ∀ σ, holds σ (Hyp.wrap (Hyp.rwUpd q Γ) φ) → holds σ (Hyp.wrap Γ φ)
  | [], _, h => h
  | .pre _ :: Γ, σ, h => fun ha => Hyp.rwUpd_wrap hq Γ σ (h ha)
  | .upd .box _ :: Γ, σ, h => Upd.rw_box hq (Hyp.rwUpd_wrap hq Γ) σ h
  | .upd .diamond U :: Γ, σ, h => by
    simp only [Hyp.rwUpd, Hyp.wrap, holds] at h ⊢
    cases hU : U.apply σ with
    | error _ => rw [hU] at h; exact h
    | ok τ => rw [hU] at h; exact Hyp.rwUpd_wrap hq Γ τ h
  | .havoc :: Γ, σ, h => fun st nt => Hyp.rwUpd_wrap hq Γ _ (h st nt)
  | .all _ _ :: Γ, σ, h => fun v hv => Hyp.rwUpd_wrap hq Γ _ (h v hv)
  | .anon _ :: Γ, σ, h => fun b => Hyp.rwUpd_wrap hq Γ _ (h b)

theorem Proves.merge_sound {Γ : List (Hyp C)} {m : Modality} {U V : Upd C} {φ : Fml C}
    (hU : U.envOnly = true) (d : Valid (Hyp.wrap (Γ ++ [.upd m (U ++ V.subst U)]) φ)) :
    Valid (Hyp.wrap (Γ ++ [.upd m U] ++ [.upd m V]) φ) := fun σ => by
  have hσ : holds σ (Hyp.wrap (Γ ++ [.upd m (U ++ V.subst U)]) φ) := d σ
  simp only [List.append_assoc, List.cons_append, List.nil_append, Hyp.wrap_append,
    Hyp.wrap] at hσ ⊢
  exact Hyp.wrap_mono (fun τ hτ => ((UpdRule.sequentialToParallel (u2 := V) (φ := φ) hU).sound τ).1 hτ)
    Γ σ hσ

theorem Proves.mergeStorage_sound {Γ : List (Hyp C)} {m : Modality} {s : STerm C} {V : Upd C}
    {φ : Fml C} (hV : V.all (·.stExplicit) = true)
    (d : Valid (Hyp.wrap (Γ ++ [.upd m (.storage s :: V.withSt s)]) φ)) :
    Valid (Hyp.wrap (Γ ++ [.upd m [.storage s]] ++ [.upd m V]) φ) := fun σ => by
  have hσ : holds σ (Hyp.wrap (Γ ++ [.upd m (.storage s :: V.withSt s)]) φ) := d σ
  simp only [List.append_assoc, List.cons_append, List.nil_append, Hyp.wrap_append,
    Hyp.wrap] at hσ ⊢
  exact Hyp.wrap_mono (fun τ hτ => (Upd.mergeStorage_holds m s V hV φ τ).1 hτ) Γ σ hσ

theorem Proves.simplify_sound {Γ : List (Hyp C)} {m : Modality} {U : Upd C} {φ : Fml C}
    (d : Valid (Hyp.wrap (Γ ++ [.upd m (U.dropEffectless φ.vars)]) φ)) :
    Valid (Hyp.wrap (Γ ++ [.upd m U]) φ) := fun σ => by
  have hσ : holds σ (Hyp.wrap (Γ ++ [.upd m (U.dropEffectless φ.vars)]) φ) := d σ
  simp only [Hyp.wrap_append, Hyp.wrap] at hσ ⊢
  exact Hyp.wrap_mono (fun τ hτ => (Upd.dropEffectless_holds m U φ τ).1 hτ) Γ σ hσ

theorem Proves.applyOnRigidBox_sound {Γ : List (Hyp C)} {U : Upd C} {φ : Fml C}
    (hU : (U.envOnly || U.localsOrStorage && φ.stFree) = true) (hr : φ.rigid = true)
    (hs : φ.sortedFor U = true) (d : Valid (Hyp.wrap Γ (φ.subst U))) :
    Valid (Hyp.wrap (Γ ++ [.upd .box U]) φ) := fun σ => by
  rw [Hyp.wrap_append]
  refine Hyp.wrap_mono (fun τ hτ => ?_) Γ σ (d σ)
  rcases Bool.or_eq_true_iff.1 hU with hU | hU
  · exact Fml.subst_box hU hr hs τ hτ
  · simp only [Bool.and_eq_true] at hU
    exact Fml.subst_box_st hU.1 hU.2 hs τ hτ

theorem Proves.applyStorageBox_sound {Γ : List (Hyp C)} {s : STerm C} {φ : Fml C}
    (hr : φ.rigid = true) (he : φ.stExplicit = true) (d : Valid (Hyp.wrap Γ (φ.withSt s))) :
    Valid (Hyp.wrap (Γ ++ [.upd .box [.storage s]]) φ) := fun σ => by
  rw [Hyp.wrap_append]
  exact Hyp.wrap_mono (fun τ hτ => Fml.withSt_box hr he τ hτ) Γ σ (d σ)

/-- **Soundness of the calculus**: a derivation of `Γ ⊢ φ` proves `φ`
wrapped in its context `Γ`.

Example: from the derivation of `a == 1, {x := a} ⟹ ⟨⟩ x == 1`
(`empty`, then `close`) follows `⊨ a == 1 → {x := a} ⟨⟩ x == 1`. -/
theorem Proves.sound {R : RuleSet} {Γ : List (Hyp C)} {φ : Fml C} (h : Proves R Γ φ) :
    Valid (Hyp.wrap Γ φ) := by
  induction h with
  | intro _ ih => simpa [Hyp.wrap_append, Hyp.wrap] using ih
  | allIntro _ ih => simpa [Hyp.wrap_append, Hyp.wrap] using ih
  | updIntro _ ih => simpa [Hyp.wrap_append, Hyp.wrap] using ih
  | @empty Γ m φ _ ih =>
    exact fun σ => Hyp.wrap_mono (ψ := φ) (φ := .modal m [] φ)
      (fun _ h => ⟨by cases m <;> exact h, nofun⟩) Γ σ (ih σ)
  | rewrite r _ ih => exact Proves.rewrite_sound r.sound ih
  | updRw r ht _ ih => exact fun σ => Hyp.rwUpd_wrap (Term.EvalRefines.of_theq r.sound ht) _ σ (ih σ)
  | merge hU _ ih => exact Proves.merge_sound hU ih
  | mergeStorage _ hV ih => exact Proves.mergeStorage_sound hV ih
  | simplify _ ih => exact Proves.simplify_sound ih
  | applyOnRigidBox _ hU hr hs ih => exact Proves.applyOnRigidBox_sound hU hr hs ih
  | applyStorageBox _ hr he ih => exact Proves.applyStorageBox_sound hr he ih
  | closeFalse _ ih =>
    exact fun σ => Hyp.wrap_mono (ψ := .ff) (fun _ h => absurd trivial h) _ σ (ih σ)
  | close h _ => exact h

open Proves in
/-- A derivation from the empty context proves validity: `⊢ φ` gives `⊨ φ`. -/
theorem Proves.valid {φ : Fml C} (h : ⊢ φ) : Valid φ := h.sound

/-- solkey's rules are some of the rules: `Γ ⊢ₖ φ` gives `Γ ⊢ φ`. -/
theorem Proves.toAll {R : RuleSet} {Γ : List (Hyp C)} {φ : Fml C} (h : Proves R Γ φ) :
    Proves .all Γ φ := by
  induction h with
  | intro _ ih => exact .intro ih
  | allIntro _ ih => exact .allIntro ih
  | updIntro _ ih => exact .updIntro ih
  | empty _ ih => exact .empty ih
  | rewrite r _ ih => exact .rewrite r ih
  | updRw r ht _ ih => exact .updRw r ht ih
  | merge hU _ ih => exact .merge hU ih
  | mergeStorage _ hV ih => exact .mergeStorage ih hV
  | simplify _ ih => exact .simplify ih
  | applyOnRigidBox _ hU hr hs ih => exact .applyOnRigidBox ih hU hr hs
  | applyStorageBox _ hr he ih => exact .applyStorageBox ih hr he
  | closeFalse _ ih => exact .closeFalse ih
  | close h hφ => exact .close h hφ

/-! ## Printing sequents

`Proves Γ φ` prints as the sequent `dl{ Γ ⟹ φ }`, so every goal of an
`apply` derivation reads as the line of the derivation it is: the context
left of `⟹`, in order, and the formula still to prove right of it.  A goal
of `⊢ₖ`, solkey's rules alone, prints as `dl{ Γ ⟹ₖ φ }`; both read back. -/

section Print
open Lean Meta PrettyPrinter Delaborator SubExpr
set_option hygiene false

/-- `Proves .all Γ φ`: `dl{ Γ ⟹ φ }`; `Proves .solkey Γ φ`: `dl{ Γ ⟹ₖ φ }`;
over a rule set `R` that is a variable, `dl{ Γ ⟹[R] φ }`.  A context `Γ ++ […]`
prints `..Γ` first. -/
@[delab app.Solidity.Proves]
def delabProves : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 4)
  let R ← whnf (e.getArg! 1)
  let some (rest, hs) ← hypSpine? (e.getArg! 2) | failure
  let mut out := #[]
  if let some Γ := rest then out := out.push (← `(dl_hyp| ..$Γ:ident))
  for h in hs do
    let some h ← ppHyp? h | failure
    out := out.push h
  let φ ← ppFml (e.getArg! 3)
  guard !(isEscape φ)
  if R.isConstOf ``RuleSet.all then `(dl{ $[$out],* ⟹ $φ:dl_fml })
  else if R.isConstOf ``RuleSet.solkey then `(dl{ $[$out],* ⟹ₖ $φ:dl_fml })
  else if let some r ← fvarName? R then `(dl{ $[$out],* ⟹[$(nameIdent r)] $φ:dl_fml })
  else failure

end Print

end Solidity
