import Solidity.Calculus.QueryReduction

/-!
# Exact removal of certified declaration premises

Generated mapping ranges are quantified formulas inside specification
antecedents. The read-query fragment accepts a universal prefix, so merely
certifying those facts is not enough: they must be removed by an exact
rewrite. Every replacement here carries a kernel-checked equivalence in
every typed state. The normalizer uses only the declaration certifier, not
user hypotheses or finite samples of keys.
-/

namespace Solidity

variable {C : Contract} {Γ : Ctx}

/-- A normalized formula and the exact meaning of its normalization. -/
structure DeclarationReduction (φ : Fml C Γ) where
  formula : Fml C Γ
  correct : ∀ σ : State C Γ, holds σ formula ↔ holds σ φ

namespace DeclarationReduction

def keep (φ : Fml C Γ) : DeclarationReduction φ := ⟨φ, fun _ => Iff.rfl⟩

def certified (φ : Fml C Γ) (h : DeclarationFacts.Valid φ) : DeclarationReduction φ :=
  ⟨.tt, fun σ => ⟨fun _ => h σ, fun _ => trivial⟩⟩

def andFormula (φ ψ : Fml C Γ) : Fml C Γ :=
  match φ, ψ with
  | .tt, ψ => ψ
  | φ, .tt => φ
  | φ, ψ => .and φ ψ

theorem andFormula_holds (σ : State C Γ) (φ ψ : Fml C Γ) :
    holds σ (andFormula φ ψ) ↔ holds σ φ ∧ holds σ ψ := by
  unfold andFormula
  split <;> simp only [holds, true_and, and_true]

def impFormula (φ ψ : Fml C Γ) : Fml C Γ :=
  match φ with
  | .tt => ψ
  | φ => .imp φ ψ

theorem impFormula_holds (σ : State C Γ) (φ ψ : Fml C Γ) :
    holds σ (impFormula φ ψ) ↔ (holds σ φ → holds σ ψ) := by
  unfold impFormula
  split <;> simp only [holds, true_implies]

def and {φ ψ : Fml C Γ} (a : DeclarationReduction φ) (b : DeclarationReduction ψ) :
    DeclarationReduction (.and φ ψ) :=
  ⟨andFormula a.formula b.formula,
    fun σ => (andFormula_holds σ _ _).trans (and_congr (a.correct σ) (b.correct σ))⟩

def imp {φ ψ : Fml C Γ} (a : DeclarationReduction φ) (b : DeclarationReduction ψ) :
    DeclarationReduction (.imp φ ψ) :=
  ⟨impFormula a.formula b.formula,
    fun σ => (impFormula_holds σ _ _).trans (imp_congr (a.correct σ) (b.correct σ))⟩

def not {φ : Fml C Γ} (a : DeclarationReduction φ) : DeclarationReduction (.not φ) :=
  ⟨.not a.formula, fun σ => not_congr (a.correct σ)⟩

def all (x : Var) (p : PrimTy) {φ : Fml C (.val p :: Γ)} (a : DeclarationReduction φ) :
    DeclarationReduction (.all x p φ) :=
  ⟨.all x p a.formula, fun σ => forall_congr' (fun v => a.correct (σ.push v))⟩

/-- Function parameters use hidden typed binders. Normalize beneath them
with the same pointwise equivalence, under either modality. -/
def bind (m : Modality) (x : Var) (t : LTy) {φ : Fml C (t :: Γ)}
    (a : DeclarationReduction φ) : DeclarationReduction (.bind m x t φ) :=
  ⟨.bind m x t a.formula, fun σ => forall_congr' (fun v => a.correct (σ.push v))⟩

open Lean Meta Elab

/-- Bounded structural normalization. A declaration attempt has the
certifier's own bounded search and catches runtime timeouts. A failed
attempt leaves the formula intact or visits its logical children. -/
private partial def reduceCore (φ : Expr) : StateRefT Nat MetaM Expr := do
  let n ← get
  if n == 0 then return ← mkAppM ``keep #[φ]
  set (n - 1)
  let saved ← saveState
  let proof ← liftM <| tryCatchRuntimeEx
    (do pure (some (← DeclarationFacts.prove φ (conjunctions := false))))
    (fun _ => saved.restore *> pure none)
  if let some h := proof then return ← mkAppM ``certified #[φ, h]
  let e ← whnf φ
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``Fml.and => mkAppM ``and #[← reduceCore args[2]!, ← reduceCore args[3]!]
  | some ``Fml.imp => mkAppM ``imp #[← reduceCore args[2]!, ← reduceCore args[3]!]
  | some ``Fml.not => mkAppM ``not #[← reduceCore args[2]!]
  | some ``Fml.all => mkAppM ``all #[args[2]!, args[3]!, ← reduceCore args[4]!]
  | some ``Fml.bind => mkAppM ``bind #[args[2]!, args[3]!, args[4]!, ← reduceCore args[5]!]
  | _ => mkAppM ``keep #[φ]

/-- Produce the normalized formula together with its ordinary proof of
equivalence. The structural node budget is shared by all descendants. -/
def reduce (φ : Expr) (budget : Nat := 2048) : MetaM Expr := do
  instantiateMVars (← (reduceCore φ).run' budget)

syntax (name := declarationReductionTerm) "declaration_reduce[" term "]" : term

@[term_elab declarationReductionTerm]
def elabDeclarationReduction : Term.TermElab := fun stx _ => do
  let φ ← Term.elabTerm stx[1] none
  let ty ← whnf (← inferType φ)
  unless ty.isAppOfArity ``Fml 2 do throwError "declaration_reduce: expected a scoped formula"
  reduce φ

end DeclarationReduction

/-- Declaration normalization composed with exact typed read reduction. -/
structure DeclarationReadReduction (φ : Fml C []) where
  declaration : DeclarationReduction φ
  reads : Decide.ReadReduction declaration.formula

namespace DeclarationReadReduction

open ReadRealization Semantics

/-- The source formula keeps its meaning through declaration removal and
both stages of exact read reduction. -/
theorem valid_iff {φ : Fml C []} (r : DeclarationReadReduction φ) :
    Valid φ ↔ ∀ (g : State C []) (args : List CallValue) (rd : (q : Ref C) → q.Value),
      (r.reads.sentence.query g Decide.AEnv.dflt args).run rd = true := by
  rw [← r.reads.valid_iff]
  exact forall_congr' (fun σ => (r.declaration.correct σ).symm)

/-- A candidate refutes the original formula with all its declaration
premises retained in the certified conclusion. -/
def countermodel? {φ : Fml C []} (r : DeclarationReadReduction φ) (g : State C [])
    (args : List CallValue) (a : Assignment C) : Option { σ : State C [] // ¬ holds σ φ } :=
  (r.reads.countermodel? g args a).map fun cm =>
    ⟨cm.val, fun hv => cm.property ((r.declaration.correct cm.val).2 hv)⟩

open Lean Meta Elab

syntax (name := declarationReadReductionTerm) "declaration_read_reduce[" term "]" : term

@[term_elab declarationReadReductionTerm]
def elabDeclarationReadReduction : Term.TermElab := fun stx _ => do
  let φ ← Term.elabTerm stx[1] none
  let d ← DeclarationReduction.reduce φ
  let normalized ← mkAppM ``DeclarationReduction.formula #[d]
  let reads ← mkAppM ``Decide.readReduction? #[normalized]
  let some ← mkAppM ``Option.isSome #[reads]
  let eq ← mkEq some (mkConst ``Bool.true)
  unless ← isDefEq (← mkDecide eq) (mkConst ``Bool.true) do
    throwError "declaration_read_reduce: normalized formula is outside the exact read fragment"
  let proof ← mkDecideProof eq
  let r ← mkAppM ``Option.get #[reads, proof]
  mkAppM ``DeclarationReadReduction.mk #[d, r]

end DeclarationReadReduction

end Solidity
