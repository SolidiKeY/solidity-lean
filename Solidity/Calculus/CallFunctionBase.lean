import Solidity.Calculus.CallFunctionGraph
import Solidity.Calculus.TermWk
import Solidity.Calculus.TermAgree

/-! # Satisfiable intrinsic base function definitions
The base term predates the new table local. Thinning inserts that local
beneath the input and result positions, so the definition cannot read
its own fresh table. Operational evaluation is connected separately.
-/
namespace Solidity.CallFunctionBase
open CallFunctionTable
variable {C : Contract} {Γ : Ctx}

/-- Insert the fresh table below the original input position. -/
def inputTerm (t : Tm C (.val .uint :: Γ) (.val .uint)) :
    Tm C (.val .uint :: .oldNet :: Γ) (.val .uint) :=
  t.wk (.keep (.drop .refl))

/-- A further fresh primitive result head leaves all original reads intact. -/
def resultTerm (t : Tm C (.val .uint :: Γ) (.val .uint)) :
    Tm C (.val .uint :: .val .uint :: .oldNet :: Γ) (.val .uint) :=
  (inputTerm t).wk (.drop .refl)

/-- The actual term ignores both new local slots at every typed state. -/
theorem result_reads (t : Tm C (.val .uint :: Γ) (.val .uint))
    (σ : State C Γ) (L : Ledger) (x r : Key) :
    (resultTerm t).denote ((((σ.push (t := .oldNet) L).push
      (t := .val .uint) x).push (t := .val .uint) r)) =
      t.denote (σ.push (t := .val .uint) x) := by
  simp only [resultTerm, inputTerm, Tm.denote_wk]
  rfl

/-- A returning value fixes the graph entry; absence of every returning
value fixes the failure code. Both clauses quantify all actual UInts. -/
def clause (inputName resultName : Var)
    (t : Tm C (.val .uint :: Γ) (.val .uint)) : Fml C (.oldNet :: Γ) :=
  .all inputName .uint
    (.and
      (.all resultName .uint
        (.imp (.eq (resultTerm t) (.pvV .here))
          (CallFunctionGraph.equalZ
            (.netOf (.there (.there .here)) (.pvV (.there .here)))
            (.app1 .toInt (.pvV .here)))))
      (.imp
        (.all resultName .uint (.not (.eq (resultTerm t) (.pvV .here))))
        (CallFunctionGraph.equalZ (.netOf (.there .here) (.pvV .here)) (.app0 (.zlit (-1))))))

/-- Returning observations plus explicit failure determine the full representation. -/
theorem represents_iff_observations (L : Ledger) (f : Key → Option Key) :
    Represents L f ↔ ∀ x : Key,
      (∀ r : Key, f x = some r → L.at x = r.val) ∧
      ((∀ r : Key, f x ≠ some r) → L.at x = -1) := by
  constructor
  · intro hp x
    constructor
    · intro r hr
      exact (returns_iff hp x r).mpr hr
    · intro hn
      have hf : f x = none := by
        cases hx : f x with
        | none => rfl
        | some r => exact False.elim (hn r hx)
      exact (failure_iff hp x).mpr hf
  · intro hp x
    change L.at x = encode (f x)
    cases hx : f x with
    | none =>
      have hn : ∀ r : Key, f x ≠ some r := by
        intro r hr
        rw [hx] at hr
        cases hr
      exact (hp x).2 hn
    | some r => exact (hp x).1 r hx

/-- The actual intrinsic definition determines exactly the term's theory
observations, including absence, without an evaluation-agreement premise. -/
theorem holds_clause (inputName resultName : Var)
    (t : Tm C (.val .uint :: Γ) (.val .uint)) (σ : State C Γ) (L : Ledger) :
    holds (σ.push (t := .oldNet) L) (clause inputName resultName t) ↔
      Represents L (fun x => t.denote (σ.push (t := .val .uint) x)) := by
  rw [represents_iff_observations]
  dsimp only [clause, holds]
  change (∀ x : Key,
    (∀ r : Key,
      (resultTerm t).denote (((σ.push (t := .oldNet) L).push
        (t := .val .uint) x).push (t := .val .uint) r) = some r →
      (some (decide (L.at x = r.val)) : Option Bool) = some true) ∧
    ((∀ r : Key,
      (resultTerm t).denote (((σ.push (t := .oldNet) L).push
        (t := .val .uint) x).push (t := .val .uint) r) ≠ some r) →
      (some (decide (L.at x = -1)) : Option Bool) = some true)) ↔ _
  simp only [result_reads, Option.some.injEq, decide_eq_true_eq]

/-- Actual definition clauses have a model at every original typed state.
The full-domain table remains a logical witness, not an evaluated object. -/
theorem satisfiable (inputName resultName : Var)
    (t : Tm C (.val .uint :: Γ) (.val .uint)) (σ : State C Γ) :
    ∃ L : Ledger, holds (σ.push (t := .oldNet) L) (clause inputName resultName t) := by
  obtain ⟨L, hL⟩ := exists_represents (fun x => t.denote (σ.push (t := .val .uint) x))
  exact ⟨L, (holds_clause inputName resultName t σ L).mpr hL⟩

/-- A checked agreement certificate connects the same clause to operational
return/failure, rather than assuming theory and evaluation always coincide. -/
theorem holds_clause_eval (inputName resultName : Var)
    (t : Tm C (.val .uint :: Γ) (.val .uint)) (ha : t.agreeB = true)
    (σ : State C Γ) (L : Ledger) :
    holds (σ.push (t := .oldNet) L) (clause inputName resultName t) ↔
      Represents L (fun x => t.eval (σ.push (t := .val .uint) x)) := by
  simp only [holds_clause, Represents, Tm.agreeB_denote ha]

/-- Thinning changes positions, not the emitted term structure. -/
theorem term_size_wk {Δ : Ctx} (h : Thin Γ Δ) {s : Srt} (t : Tm C Γ s) :
    (t.wk h).size = t.size := by
  induction t with
  | pvV i => rfl
  | pvP i => rfl
  | pvS i => rfl
  | pvI i => rfl
  | pvZ i => rfl
  | app0 o => rfl
  | netOf i a ih => simp only [Tm.wk_netOf, Tm.size, ih]
  | app1 o a ih => simp only [Tm.wk_app1, Tm.size, ih]
  | app2 o a b iha ihb => simp only [Tm.wk_app2, Tm.size, iha, ihb]
  | app3 o a b c iha ihb ihc => simp only [Tm.wk_app3, Tm.size, iha, ihb, ihc]

/-- Both copies of the base term and every quantifier/connective/comparison
wrapper are counted. This does not count a whole call-family leaf. -/
theorem clause_size (inputName resultName : Var)
    (t : Tm C (.val .uint :: Γ) (.val .uint)) :
    (clause inputName resultName t).tmSize = 2 * t.size + 24 := by
  simp only [clause, resultTerm, inputTerm, CallFunctionGraph.equalZ, Fml.tmSize,
    Tm.size, term_size_wk]
  omega

end Solidity.CallFunctionBase
