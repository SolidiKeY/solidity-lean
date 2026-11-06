import Solidity.Yul.OccurrenceCheck
import Solidity.Yul.WordSyntax

/-! Actual existing closed-word preparation with an independent original-source
occurrence certificate. Input name provenance is still explicit: these must be
original spellings whose first outside lookup selects a local Solidity variable.
This does not supply Source/JSON IDs, general external typing, safety or dispatch. -/
namespace Solidity.Yul.OccurrenceSyntax
open Solidity.Source (Syn)
open Solidity.Frontend.Checked

structure Prepared (outside localNames : List String) (body : Syn (.list .yulStmt)) where
  occurrences : OccurrenceCheck.D localNames false body
  words : WordSyntax.Prepared outside body

inductive Error where
  | occurrences (reason : OccurrenceCheck.Error)
  | words (reason : WordSyntax.Error)
  | grammar
  deriving Repr

def prepare (outside localNames : List String) (body : Syn (.list .yulStmt)) :
    Except Error (Prepared outside localNames body) := do
  let occurrences ← (OccurrenceCheck.check localNames false body).mapError Error.occurrences
  let words ← (WordSyntax.prepare outside body).mapError Error.words
  pure ⟨occurrences, words⟩

theorem Prepared.complete {outside localNames body} (p : Prepared outside localNames body) :
    prepare outside localNames body = .ok p := by
  cases p with
  | mk occurrences words =>
    unfold prepare
    rw [occurrences.complete]
    change ((WordSyntax.prepare outside body).mapError Error.words).bind _ = _
    rw [words.complete]
    rfl

/-- Fixed original syntax and supplied namespace/local-name lists determine
the entire certificate. This does not authenticate those supplied names or IDs. -/
theorem Prepared.unique {outside localNames body}
    (first second : Prepared outside localNames body) : first = second := by
  exact Except.ok.inj (first.complete.symm.trans second.complete)

theorem prepare_iff (outside localNames : List String) (body : Syn (.list .yulStmt)) :
    (prepare outside localNames body).isOk = true ↔ Nonempty (Prepared outside localNames body) := by
  constructor
  · intro h
    cases actual : prepare outside localNames body with
    | error reason => rw [actual] at h; cases h
    | ok p => exact ⟨p⟩
  · rintro ⟨p⟩
    rw [p.complete]
    rfl

/-- Execution is the ACTUAL existing word program, with no execution substitute
or Source/state refinement hypothesis. This is closed-word execution only. -/
def Prepared.run {outside localNames body} (p : Prepared outside localNames body) (fuel : Nat) :=
  p.words.run fuel

/-- The same preparation inputs determine the full closed-word result at
each fixed fuel, including noncompletion; termination is not asserted. -/
theorem Prepared.run_unique {outside localNames body}
    (first second : Prepared outside localNames body) (fuel : Nat) :
    first.run fuel = second.run fuel := by
  exact congrArg (fun p => Prepared.run p fuel)
    (Except.ok.inj (first.complete.symm.trans second.complete))

theorem Prepared.old_result {outside localNames body} (p : Prepared outside localNames body) :
    WordSyntax.prepare outside body = .ok p.words := p.words.complete

end Solidity.Yul.OccurrenceSyntax
