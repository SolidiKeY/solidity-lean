import Solidity.Calculus.RuleSyntax

/-!
# Sequents: the rule sets, fresh indices, the sequent notation

What the scoped judgement `H ⊢ φ` (`Calculus/Proves.lean`) is indexed by
and written with: the rule sets a derivation may use (`RuleSet`), the
fresh index above every name in sight (`maxIdx`), and the sequent's
arrows and keywords (`sequent[C]{ Γ ⟹ φ }`, `sequentFml`).
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-! ## Fresh names -/

/-- The largest index of a list of variables. -/
def maxIdx : List Var → Nat
  | [] => 0
  | x :: xs => max x.idx (maxIdx xs)

/-- Every variable's index is at most the largest index in the list.

Example: after Step 2 on `alice.account.balance = 10; uint x = alice.account.balance;`
the formula mentions `sp1`, so `maxIdx` is at least `1`, and the read's
receiver is captured as `sp2`, not as `sp1` again. -/
theorem le_maxIdx {x : Var} : ∀ {xs : List Var}, x ∈ xs → x.idx ≤ maxIdx xs
  | _ :: _, .head _ => Nat.le_max_left _ _
  | _ :: _, .tail _ h => Nat.le_trans (le_maxIdx h) (Nat.le_max_right _ _)

/-- A list whose variables all occur in another has no larger `maxIdx`. -/
theorem maxIdx_le {xs ys : List Var} (h : ∀ x ∈ ys, x ∈ xs) : maxIdx ys ≤ maxIdx xs := by
  induction ys with
  | nil => exact Nat.zero_le _
  | cons y ys ih =>
    simp only [maxIdx]
    exact Nat.max_le.2 ⟨le_maxIdx (h y (.head _)), ih (fun x hx => h x (.tail _ hx))⟩

/-- The largest index of two lists is the larger of theirs: `[x, se1] ++ [sp2]`
has `2`.  With it the fresh index of a line whose postcondition `φ` names no
fresh variable is computed without knowing `φ` (`Chains.lean`). -/
theorem maxIdx_append (xs ys : List Var) : maxIdx (xs ++ ys) = max (maxIdx xs) (maxIdx ys) := by
  induction xs with
  | nil => exact (Nat.zero_max _).symm
  | cons x xs ih => simp only [List.cons_append, maxIdx, ih, Nat.max_assoc]


/-- Which rules a derivation may use: solkey's (`Taclet`), or all of them
(`LeanTaclet` too). -/
inductive RuleSet where
  | solkey
  | all
  deriving DecidableEq, Repr

/-! ## Reading a sequent

The arrow and the keywords of `sequent[C]{ Γ ⟹ φ }`, which
`Calculus/Sequents.lean` reads on a scoped goal, and the sequent's formula
written (`sequentFml`). -/

section Sequent
open Lean

/-- The arrow of a sequent: `⟹` for the whole calculus (`⊢`), `⟹ₖ` for
solkey's rules alone (`⊢ₖ`). -/
declare_syntax_cat seq_arrow
syntax " ⟹ " : seq_arrow
syntax " ⟹ₖ " : seq_arrow

/-- `sequent[C]{ Γ ⟹ φ }`: the sequent `Γ ⊢ φ` (with `⟹ₖ`, `Γ ⊢ₖ φ`), read
against the contract `C`. -/
syntax (name := sequentStx) "sequent[" term "]{ " sepBy(dl_hyp, ", ") seq_arrow dl_fml " }" :
  term
/-- `sequent[C, m]{ Γ ⟹ φ }`: `sequent[C]{ … }` at the modality `m`. -/
syntax "sequent[" term ", " term "]{ " sepBy(dl_hyp, ", ") seq_arrow dl_fml " }" : term
/-- `sequent!{ Γ ⟹ φ }`: `sequent[C]{ … }` for the file's `InContract` contract. -/
syntax "sequent!{ " sepBy(dl_hyp, ", ") seq_arrow dl_fml " }" : term
/-- `sequent![m]{ Γ ⟹ φ }`: `sequent[C, m]{ … }` for the file's `InContract` contract. -/
syntax "sequent![" term "]{ " sepBy(dl_hyp, ", ") seq_arrow dl_fml " }" : term

section Expand

/-- The sequent's formula, its context in front, written: `a → …` for a
precondition, `{U} …` for an update. -/
def sequentFml (hs : Array (TSyntax `dl_hyp)) (φ : TSyntax `dl_fml) : MacroM (TSyntax `dl_fml) :=
  hs.foldrM (init := φ) fun h acc => do
    match h with
    | `(dl_hyp| { havoc }) =>
      Macro.throwErrorAt h "`{ havoc }` is what a callback rule leaves, not an entry to write"
    | `(dl_hyp| $U:dl_upd) => `(dl_fml| $U:dl_upd ($acc))
    | `(dl_hyp| $a:dl_fml) => `(dl_fml| ($a) → ($acc))
    | _ => Macro.throwUnsupported

end Expand


end Sequent

end Solidity
