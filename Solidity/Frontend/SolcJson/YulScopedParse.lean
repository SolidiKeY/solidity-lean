import Solidity.Frontend.SolcJson.YulWords
import Solidity.Frontend.Yul.ScopedParse

/-!
# Guarded scoped source preparation

Uses the ACTUAL existing checked parser, combined static/tier preparation and
metadata safety recognizer. Unknown flags are retained (warnings upstream);
duplicate memory-safe flags refuse. Supplied documentation must still be
attached to this source block by the importer: a recognized supplied string
does not prove Source/JSON provenance or MemOK. Original namespace/ID/
occurrence provenance and concrete Source/dirty semantics remain separate.
The canonical rethrow's existing Body exception is unchanged and is not routed
through this preparation function.
-/
namespace Solidity.Frontend.YulJson.ScopedParse
open Solidity.Yul
open Solidity.Yul.BlockScope (Scope)
open Solidity.Frontend.Checked

structure Checked {X} (scope : Scope X) (tier : Tier) (outside localNames : List String)
    (documentation : Option String) (src : Bytes) where
  parsed : AssemblyParse src
  uniqueFlag : (parsed.flags.filter (· == "memory-safe")).length ≤ 1
  safe : SafetyCertificate parsed.flags documentation
  prepared : ScopedSyntax.Prepared scope tier outside localNames parsed.body

inductive Error where
  | grammar
  | duplicateMemorySafeFlag
  | safety (reason : Refusal)
  | syntax (reason : ScopedSyntax.Error)
  deriving Repr

def check {X} (scope : Scope X) (tier : Tier) (outside localNames : List String)
    (documentation : Option String) (src : Bytes) :
    Except Error (Checked scope tier outside localNames documentation src) :=
  match parseAssembly src with
  | none => .error .grammar
  | some parsed =>
    if uniqueFlag : (parsed.flags.filter (· == "memory-safe")).length ≤ 1 then do
      let safe ← (checkMetadataSafety parsed.flags documentation).mapError Error.safety
      let prepared ← (ScopedSyntax.prepare scope tier outside localNames parsed.body).mapError Error.syntax
      pure ⟨parsed, uniqueFlag, safe, prepared⟩
    else .error .duplicateMemorySafeFlag

theorem Checked.complete {X scope tier outside localNames documentation src}
    (c : @Checked X scope tier outside localNames documentation src) :
    check scope tier outside localNames documentation src = .ok c := by
  cases c with
  | mk parsed uniqueFlag safe prepared =>
    unfold check
    rw [parsed.complete]
    dsimp only
    rw [dif_pos uniqueFlag]
    simp only [Words.safety_complete safe, prepared.complete,
      bind, Except.bind, Except.mapError, pure, Except.pure]

theorem check_iff {X} (scope : Scope X) (tier : Tier) (outside localNames : List String)
    (documentation : Option String) (src : Bytes) :
    (check scope tier outside localNames documentation src).isOk = true ↔
      Nonempty (Checked scope tier outside localNames documentation src) := by
  constructor
  · intro h
    cases actual : check scope tier outside localNames documentation src with
    | error reason => rw [actual] at h; cases h
    | ok c => exact ⟨c⟩
  · rintro ⟨c⟩
    rw [c.complete]
    rfl

def Checked.coreParsed {X scope tier outside localNames documentation src}
    (c : @Checked X scope tier outside localNames documentation src) :
    ScopedSyntax.Parsed scope tier outside localNames src :=
  ⟨c.parsed, c.prepared⟩

theorem Checked.core_result {X scope tier outside localNames documentation src}
    (c : @Checked X scope tier outside localNames documentation src) :
    ScopedSyntax.parse scope tier outside localNames src = .ok c.coreParsed :=
  c.coreParsed.complete

/-- A real annotation-recognition certificate from the same actual flags/doc;
not a memory preservation, Source attachment or compiler refinement theorem. -/
theorem Checked.annotation {X scope tier outside localNames documentation src}
    (c : @Checked X scope tier outside localNames documentation src) :
    MetadataSafetyD c.parsed.flags documentation :=
  c.safe.derivation

def Checked.closedRun {outside localNames documentation src}
    (c : Checked .closed .A outside localNames documentation src) (fuel : Nat) :=
  c.prepared.closedRun fuel


def Checked.wordRun {scope : Scope []} {outside localNames documentation src}
    (c : Checked scope .A outside localNames documentation src) (fuel : Nat) :=
  c.prepared.wordRun fuel

end Solidity.Frontend.YulJson.ScopedParse
