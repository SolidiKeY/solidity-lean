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

theorem Prepared.old_result {outside localNames body} (p : Prepared outside localNames body) :
    WordSyntax.prepare outside body = .ok p.words := p.words.complete

structure Parsed (outside localNames : List String) (src : Bytes) where
  parsed : AssemblyParse src
  prepared : Prepared outside localNames parsed.body

def parse (outside localNames : List String) (src : Bytes) :
    Except Error (Parsed outside localNames src) :=
  match parseAssembly src with
  | none => .error .grammar
  | some parsed => (prepare outside localNames parsed.body).map
      (fun prepared => ⟨parsed, prepared⟩)

theorem Parsed.complete {outside localNames src} (p : Parsed outside localNames src) :
    parse outside localNames src = .ok p := by
  cases p with
  | mk parsed prepared =>
    unfold parse
    rw [parsed.complete]
    change (prepare outside localNames parsed.body).map _ = _
    rw [prepared.complete]
    rfl

theorem parse_iff (outside localNames : List String) (src : Bytes) :
    (parse outside localNames src).isOk = true ↔ Nonempty (Parsed outside localNames src) := by
  constructor
  · intro h
    cases actual : parse outside localNames src with
    | error reason => rw [actual] at h; cases h
    | ok p => exact ⟨p⟩
  · rintro ⟨p⟩
    rw [p.complete]
    rfl

end Solidity.Yul.OccurrenceSyntax
