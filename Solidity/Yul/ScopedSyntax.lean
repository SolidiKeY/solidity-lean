import Solidity.Yul.BlockExtract
import Solidity.Yul.ClosedSyntax
import Solidity.Yul.OccurrenceCheck
import Solidity.Yul.WordSyntax

/-!
# Combined scoped static and tier preparation

This composes actual original-source shape, declaration visibility/NoShadow,
placement, Solidity-local occurrence isolation, shared typing/extraction and
whole-AST tier policy. Supplied original namespaces/local-name sets still need
actual Source/JSON provenance and coherence. Parser flags are retained, not
admitted: memory-safe flag/NatSpec evidence belongs to the frontend adapter.
This is not general frontend admission or open-world/dirty execution.
-/
namespace Solidity.Yul.ScopedSyntax
open Solidity.Source (Syn)
open Solidity.Frontend.Checked
open Solidity.Yul.BlockScope (Scope)

structure Prepared {X} (scope : Scope X) (tier : Tier) (outside localNames : List String)
    (body : Syn (.list .yulStmt)) where
  shape : body.prec = true
  finalNames : List String
  declarations : DeclarationScope.BlockD outside [] body finalNames
  placement : Placement.Derivation Placement.rootContext body
  occurrences : OccurrenceCheck.D localNames false body
  typing : ScopedBlockTyping.BlockD scope ClosedSyntax.rootEnv ClosedSyntax.rootControl body
  policy : Policy.StmtP tier typing.code

inductive Error where
  | grammar | shape | declarations | typing
  | placement (reason : Placement.Error)
  | occurrences (reason : OccurrenceCheck.Error)
  | policy (reason : Refusal)
  deriving Repr

def prepare {X} (scope : Scope X) (tier : Tier) (outside localNames : List String)
    (body : Syn (.list .yulStmt)) : Except Error (Prepared scope tier outside localNames body) :=
  if shape : body.prec = true then do
    let ⟨finalNames, declarations⟩ ←
      match DeclarationScope.checkBlock outside [] body with
      | none => .error .declarations
      | some result => .ok result
    let placement ← (Placement.checkBlock body).mapError Error.placement
    let occurrences ← (OccurrenceCheck.check localNames false body).mapError Error.occurrences
    let typing ← match ScopedBlockTyping.checkBlock scope ClosedSyntax.rootEnv ClosedSyntax.rootControl body with
      | none => .error .typing
      | some result => .ok result
    match checked : Policy.checkStmt tier typing.code with
    | .error reason => .error (.policy reason)
    | .ok () => .ok ⟨shape, finalNames, declarations, placement, occurrences, typing,
        (Policy.stmt_iff tier typing.code).mp checked⟩
  else .error .shape

theorem Prepared.complete {X scope tier outside localNames body}
    (p : @Prepared X scope tier outside localNames body) :
    prepare scope tier outside localNames body = .ok p := by
  cases p with
  | mk shape finalNames declarations placement occurrences typing policy =>
    have placementEq : Placement.checkBlock body = .ok placement := placement.complete
    have policyEq : Policy.checkStmt tier typing.code = .ok () :=
      (Policy.stmt_iff tier typing.code).mpr policy
    simp only [prepare, dif_pos shape, declarations.complete, placementEq,
      occurrences.complete, typing.complete, bind, Except.bind, Except.mapError]
    split
    · next reason failed => cases (failed.symm.trans policyEq)
    · rfl

theorem prepare_iff {X} (scope : Scope X) (tier : Tier) (outside localNames : List String)
    (body : Syn (.list .yulStmt)) :
    (prepare scope tier outside localNames body).isOk = true ↔
      Nonempty (Prepared scope tier outside localNames body) := by
  constructor
  · intro h
    cases actual : prepare scope tier outside localNames body with
    | error reason => rw [actual] at h; cases h
    | ok p => exact ⟨p⟩
  · rintro ⟨p⟩
    rw [p.complete]
    rfl

def Prepared.code {X scope tier outside localNames body}
    (p : @Prepared X scope tier outside localNames body) :
    Stmt [] X ClosedSyntax.rootControl 0 :=
  p.typing.code

/-- The concrete closed tier-A instance constructs the ACTUAL existing word
program/profile, not a parameterized promise about later semantics. -/
def Prepared.closedWords {outside localNames body}
    (p : Prepared .closed .A outside localNames body) : WordSyntax.Prepared outside body :=
  ⟨⟨p.shape, p.finalNames, p.declarations, p.placement, p.typing⟩, p.policy⟩

theorem Prepared.closed_old_result {outside localNames body}
    (p : Prepared .closed .A outside localNames body) :
    WordSyntax.prepare outside body = .ok p.closedWords :=
  p.closedWords.complete

def Prepared.closedRun {outside localNames body}
    (p : Prepared .closed .A outside localNames body) (fuel : Nat) :=
  p.closedWords.run fuel


/-- Every ACTUAL empty external context has a concrete closed-word program,
including external namespaces projected from nonempty original declarations.
The scope constructor need not be closed. The no-member premise is discharged
here; no caller model/closure/success agreement is assumed. -/
def Prepared.wordProgram {scope : Scope []} {outside localNames body}
    (p : Prepared scope .A outside localNames body) :
    Logic.Program [] ClosedSyntax.rootControl 0 :=
  ⟨p.code, Closed.stmt_policy_words p.code (fun _ index => by cases index) p.policy⟩

def Prepared.wordRun {scope : Scope []} {outside localNames body}
    (p : Prepared scope .A outside localNames body) (fuel : Nat) :=
  Closed.evalStmt fuel WordSyntax.emptyModel.environment WordSyntax.emptyModel.words
    p.wordProgram.code p.wordProgram.words Fin.elim0

theorem Prepared.word_rule_exists {scope : Scope []} {outside localNames body}
    (p : Prepared scope .A outside localNames body) (mode : Solidity.Modality)
    (post : Closed.Flow ClosedSyntax.rootControl → Logic.Fml 0) :
    ∃ premise, Nonempty (Logic.Rule (.modal mode WordSyntax.emptyModel p.wordProgram post) premise) :=
  Logic.program_rule_exists mode WordSyntax.emptyModel p.wordProgram post

theorem Prepared.word_rule_sound {scope : Scope []} {outside localNames body}
    (p : Prepared scope .A outside localNames body) (mode : Solidity.Modality)
    (post : Closed.Flow ClosedSyntax.rootControl → Logic.Fml 0) :
    ∃ premise : Logic.Fml 0, ∀ vars,
      (.modal mode WordSyntax.emptyModel p.wordProgram post : Logic.Fml 0).holds vars ↔
        premise.holds vars :=
  Logic.sound_program_rule_exists mode WordSyntax.emptyModel p.wordProgram post

theorem Prepared.wordRun_closed {outside localNames body}
    (p : Prepared .closed .A outside localNames body) (fuel : Nat) :
    p.wordRun fuel = p.closedRun fuel := rfl

structure Parsed {X} (scope : Scope X) (tier : Tier) (outside localNames : List String)
    (src : Bytes) where
  parsed : AssemblyParse src
  prepared : Prepared scope tier outside localNames parsed.body

def parse {X} (scope : Scope X) (tier : Tier) (outside localNames : List String) (src : Bytes) :
    Except Error (Parsed scope tier outside localNames src) :=
  match parseAssembly src with
  | none => .error .grammar
  | some parsed => (prepare scope tier outside localNames parsed.body).map
      (fun prepared => ⟨parsed, prepared⟩)

theorem Parsed.complete {X scope tier outside localNames src}
    (p : @Parsed X scope tier outside localNames src) :
    parse scope tier outside localNames src = .ok p := by
  cases p with
  | mk parsed prepared =>
    unfold parse
    rw [parsed.complete]
    change (prepare scope tier outside localNames parsed.body).map _ = _
    rw [prepared.complete]
    rfl

theorem parse_iff {X} (scope : Scope X) (tier : Tier) (outside localNames : List String)
    (src : Bytes) :
    (parse scope tier outside localNames src).isOk = true ↔
      Nonempty (Parsed scope tier outside localNames src) := by
  constructor
  · intro h
    cases actual : parse scope tier outside localNames src with
    | error reason => rw [actual] at h; cases h
    | ok p => exact ⟨p⟩
  · rintro ⟨p⟩
    rw [p.complete]
    rfl

end Solidity.Yul.ScopedSyntax
