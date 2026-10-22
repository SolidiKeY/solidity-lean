import Solidity.Calculus.Lands
import Solidity.Calculus.Logic
import Solidity.Calculus.RuleSyntax

/-!
# `⊨`, minimal: what a correctness statement means

`holds` (`Calculus/Logic.lean`) reads every formula the calculus writes on
its way to a leaf: updates by where they land, hidden binders, `{havoc}`,
`{anon}`, the heap grown, the frames left open.  Those are the proof's
intermediate forms; to read a correctness statement one should not have to
read them.  `Spec` is only what a statement says, intrinsically typed as
`Fml` is (a local is a position `Idx Γ t`, a program a `Prog C Γ Γ'`), and
`Spec.sat` reads it by the typed run alone.

* An equation requires both terms to evaluate to the same value (`Tm.eval`);
  two undefined terms do not satisfy it. `wt(s)` is the storage's test.
* `∀ t x; φ` ranges over what a local of type `t` may hold in the state's
  heap (a value, a storage reference, a memory reference or `none`).
* `[ P ] φ`: `P` does not panic, and `φ` holds where it ends normally; a
  revert, divergence or exhaustion satisfies it.
  `⟨ P ⟩ φ`: `P` ends normally and `φ` holds there, or it is exhausted
  (decision 15: KeY models no gas, so neither modality refutes a run out of
  it).

`Spec.toFml` is the formula the calculus proves. An equation captures its
operands in a parallel box update, negated so a failed capture is rejected;
the Theory's total equations remain available inside derivations.
`Spec.sat_iff_holds` proves that translation exact in every typed state.
`Spec.valid_iff` lifts it to validity; `Proves.valid` (`Calculus/Sound.lean`)
then proves `⊢ φ.toFml → ⊨ φ`. Internal formula validity is `Fml.Valid`
(`⊨ᶠ`), separate from this judgement.
-/

namespace Solidity

variable {C : Contract}

/-- A correctness statement about programs of `C`, read in `Γ`. -/
inductive Spec (C : Contract) : Ctx → Type where
  | tt {Γ : Ctx} : Spec C Γ
  /-- `a = b` -/
  | eq {Γ : Ctx} {p : PrimTy} (a b : Tm C Γ (.val p)) : Spec C Γ
  /-- `wt(s)` -/
  | wellFormed {Γ : Ctx} (s : Tm C Γ .st) : Spec C Γ
  | not {Γ : Ctx} (φ : Spec C Γ) : Spec C Γ
  | and {Γ : Ctx} (φ ψ : Spec C Γ) : Spec C Γ
  | imp {Γ : Ctx} (φ ψ : Spec C Γ) : Spec C Γ
  /-- `∀ t x; φ` -/
  | all {Γ : Ctx} (x : Var) (t : LTy) (φ : Spec C (t :: Γ)) : Spec C Γ
  /-- `[ P ] φ` -/
  | box {Γ Γ' : Ctx} (P : Prog C Γ Γ') (φ : Spec C Γ') : Spec C Γ
  /-- `⟨ P ⟩ φ` -/
  | diamond {Γ Γ' : Ctx} (P : Prog C Γ Γ') (φ : Spec C Γ') : Spec C Γ

/-- An equation with evaluated operands: both captures must return, and their
values must agree. Negating a box update rejects every failed capture,
including exhaustion. -/
def Fml.evalEq {Γ : Ctx} {p : PrimTy} (a b : Tm C Γ (.val p)) : Fml C Γ :=
  .not (.upd .box ((Upd.nil.decl (.user "lhs") (.val a)).decl (.user "rhs") (.val b))
    (.not (.eq (.pvV (.there .here)) (.pvV .here))))

/-- Capturing two operands tests equality only where both evaluate. -/
theorem Fml.holds_evalEq {Γ : Ctx} {p : PrimTy} (σ : State C Γ)
    (a b : Tm C Γ (.val p)) :
    holds σ (Fml.evalEq a b) ↔ ∃ v, a.eval σ = some v ∧ b.eval σ = some v := by
  cases ha : a.eval σ <;> cases hb : b.eval σ <;>
    simp only [evalEq, holds, Upd.afterT, Upd.globT, Rhs.eval, ha, hb,
      Option.bind_none, Option.bind_some, Modality.onHalt, true_or, not_true_eq_false,
      reduceCtorEq, false_and, and_false, exists_false, iff_self, Option.some.injEq,
      exists_eq_left']
  rename_i x y
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    apply h
    intro τ hL heq
    have hx : x = TEnv.get (.there .here) τ.env := Option.some.inj (ha.symm.trans (hL.2.2 (.there .here)))
    have hy : y = TEnv.get .here τ.env := Option.some.inj (hb.symm.trans (hL.2.2 .here))
    exact hne (hy.trans ((Option.some.inj heq).symm.trans hx.symm))
  · intro heq h
    have hL := Upd.lands_decl (r := .val b) (v := y)
      (Upd.lands_decl (r := .val a) (v := x) (Upd.lands_nil σ) (.user "lhs") ha)
      (.user "rhs") hb
    exact h _ hL (congrArg some heq.symm)

namespace Spec

/-- **`φ` holds in the typed state `σ`.** -/
def sat : {Γ : Ctx} → State C Γ → Spec C Γ → Prop
  | _, _, .tt => True
  | _, σ, .eq a b => ∃ v, a.eval σ = some v ∧ b.eval σ = some v
  | _, σ, .wellFormed s => ∃ st, s.eval σ = some st ∧ st.wtB = true
  | _, σ, .not φ => ¬ sat σ φ
  | _, σ, .and φ ψ => sat σ φ ∧ sat σ ψ
  | _, σ, .imp φ ψ => sat σ φ → sat σ ψ
  | _, σ, .all _ t φ => ∀ v : t.TDenote C σ.H, sat (σ.push v) φ
  | _, σ, .box P φ =>
    match Prog.run σ P with
    | .ok o => sat o.st φ
    | .error e => e ≠ .panic
  | _, σ, .diamond P φ =>
    match Prog.run σ P with
    | .ok o => sat o.st φ
    | .error e => e = .exhausted

/-- **`⊨ φ`**: `φ` holds in every typed state of the empty context. -/
def Valid (φ : Spec C []) : Prop := ∀ σ : State C [], sat σ φ

/-- The formula the calculus proves for `φ`: a modality with no frames
left, a binder hidden. -/
def toFml : {Γ : Ctx} → Spec C Γ → Fml C Γ
  | _, .tt => .tt
  | _, .eq a b => Fml.evalEq a b
  | _, .wellFormed s => .wellFormed s
  | _, .not φ => .not φ.toFml
  | _, .and φ ψ => .and φ.toFml ψ.toFml
  | _, .imp φ ψ => .imp φ.toFml ψ.toFml
  | _, .all x t φ => .bind .box x t φ.toFml
  | _, .box P φ => .modal .box P .nil φ.toFml
  | _, .diamond P φ => .modal .diamond P .nil φ.toFml

/-- A statement's direct reading agrees with the formula proved by the calculus. -/
theorem sat_iff_holds {Γ : Ctx} (φ : Spec C Γ) (σ : State C Γ) :
    sat σ φ ↔ holds σ φ.toFml := by
  induction φ with
  | box P φ ih =>
    cases h : Prog.run σ P <;>
      simp only [sat, toFml, holds, Prog.runFrames, h, Modality.afterRunTR,
        Frames.run, bind, Except.bind, pure, Except.pure, Modality.onTHalt,
        ne_eq, reduceCtorEq, not_false_eq_true, and_true, true_and, ih]
    constructor <;> grind
  | diamond P φ ih =>
    cases h : Prog.run σ P <;>
      simp only [sat, toFml, holds, Prog.runFrames, h, Modality.afterRunTR,
        Frames.run, bind, Except.bind, pure, Except.pure, Modality.onTHalt,
        ne_eq, reduceCtorEq, not_false_eq_true, and_true, ih]
    constructor
    · exact fun he => ⟨he, by cases he; intro hp; cases hp⟩
    · exact And.left
  | tt => rfl
  | eq a b => exact (Fml.holds_evalEq σ a b).symm
  | wellFormed s => rfl
  | not φ ih => exact not_congr (ih σ)
  | and φ ψ ihφ ihψ => exact and_congr (ihφ σ) (ihψ σ)
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ σ) (ihψ σ)
  | all x t φ ih => exact ⟨fun h v => (ih (σ.push v)).mp (h v), fun h v => (ih (σ.push v)).mpr (h v)⟩

/-- The calculus's translated statement is valid exactly when the statement is. -/
theorem valid_iff (φ : Spec C []) : Valid φ ↔ Fml.Valid φ.toFml :=
  ⟨fun h σ => (sat_iff_holds φ σ).mp (h σ),
    fun h σ => (sat_iff_holds φ σ).mpr (h σ)⟩

end Spec

/-- `⊨ φ` reads a correctness statement by the typed run alone. -/
syntax:25 (name := specValidSyntax) "⊨ " term:26 : term

open Lean Elab Term Meta in
/-- Only correctness statements have the public validity judgement. -/
elab_rules : term
  | `(⊨ $φ:term) => do
    let e ← elabTerm φ none
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    match (← whnf (← inferType e)).getAppFn.constName? with
    | some ``Spec => mkAppM ``Spec.Valid #[e]
    | _ => throwError "⊨ reads a correctness statement (`Spec C []`), not{indentExpr e}"

/-- `Spec.Valid φ` prints as `⊨ φ`. -/
@[app_unexpander Spec.Valid]
def Spec.unexpandValid : Lean.PrettyPrinter.Unexpander
  | `($_ $φ) => `(⊨ $φ)
  | _ => throw ()

/-- info: 'Solidity.Spec.sat_iff_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spec.sat_iff_holds

example : ⊨ (Spec.tt : Spec C []) := fun _ => trivial

end Solidity
