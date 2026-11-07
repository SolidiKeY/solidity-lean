import Solidity.Frontend.LiteralGrammarH28.Classification
import Lean

/-! # Exhaustive word-table return classes

The proof uses closure under the existing matcher's primitive list cases,
conditionals and constant-type equality transports. The proof tactic emits
ordinary kernel-checked applications of those lemmas; it never evaluates a
native decision oracle or changes an elaboration budget.
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def wordNonliteral : WordClass → Bool
  | .tok (.str _) | .tok (.hexStr _) | .tok (.unicodeStr _) => false
  | _ => true

theorem word_cases (raw : Bytes) (empty : WordClass) (cons : UInt8 → Bytes → WordClass)
    (hn : wordNonliteral empty = true) (hc : ∀ b tail, wordNonliteral (cons b tail) = true) :
    wordNonliteral (List.casesOn raw empty cons) = true := by
  cases raw with
  | nil => exact hn
  | cons b tail => exact hc b tail

theorem word_dite (p : Prop) [Decidable p] (yes : p → WordClass) (no : ¬p → WordClass)
    (hy : ∀ h, wordNonliteral (yes h) = true) (hn : ∀ h, wordNonliteral (no h) = true) :
    wordNonliteral (dite p yes no) = true := by
  by_cases h : p
  · rw [dif_pos h]; exact hy h
  · rw [dif_neg h]; exact hn h

theorem word_transport {α : Sort u} {a b : α} (h : a = b) (value : WordClass)
    (hv : wordNonliteral value = true) :
    wordNonliteral (@Eq.rec α a (fun _ _ => WordClass) value b h) = true := by
  cases h
  exact hv

open Lean Elab Tactic in
elab "word_range_step" : tactic => withMainContext do
  let target ← getMainTarget
  match target with
  | .forallE .. => evalTactic (← `(tactic| intro))
  | _ =>
    unless target.isAppOfArity ``Eq 3 do throwError "expected a range equality"
    let lhs := target.getAppArgs[1]!
    unless lhs.isAppOfArity ``wordNonliteral 1 do throwError "expected wordNonliteral"
    let value := lhs.getAppArgs[0]!.headBeta
    let head := value.getAppFn.constName?
    if head == some ``List.casesOn || head == some ``List.rec then
      evalTactic (← `(tactic| apply word_cases))
    else if head == some ``dite then
      evalTactic (← `(tactic| apply word_dite))
    else if head == some ``Eq.rec || head == some ``Eq.ndrec then
      let saved ← saveState
      try
        evalTactic (← `(tactic| apply word_transport))
      catch _ =>
        saved.restore
        let reduced ← Meta.whnf value
        if reduced != value then
          let changedTarget ← Meta.mkEq (mkApp (mkConst ``wordNonliteral) reduced) (toExpr true)
          let changed ← (← getMainGoal).change changedTarget
          replaceMainGoal [changed]
        else
          let proof := value.getAppArgs[5]!
          let proofSyntax ← PrettyPrinter.delab proof
          let before ← getMainTarget
          evalTactic (← `(tactic| cases ($proofSyntax)))
          unless (← getGoals).isEmpty do
            if (← getMainTarget) == before then throwError "transport step made no progress"
    else if head == some ``WordClass.tok || head == some ``WordClass.other || head == some ``WordClass.reserved then
      evalTactic (← `(tactic| rfl))
    else throwError "unsupported range-proof node: {value.getAppFn}"

open Lean Elab Tactic in
elab "word_range_all" : tactic => do
  for _ in List.range 8192 do
    if (← getGoals).isEmpty then return
    evalTactic (← `(tactic| word_range_step))
  throwError "range proof did not finish its finite structural traversal"

theorem solWordTable_nonliteral (raw : Bytes) : wordNonliteral (solWordTable raw) = true := by
  unfold solWordTable solWordTable.match_1
  word_range_all

end Solidity.Frontend.LiteralGrammarH28
