import Solidity.Frontend.SolcJson.YulMetadataWords
import Solidity.Frontend.SolcJson.YulWords
import Solidity.Yul.OpenScoped

/-! Actual InlineAssembly JSON to an explicitly supplied typed namespace and
pure execution. Retains decoder equations and uses actual metadata safety.
Declaration/Source provenance and AST external-reference occurrence attachment
remain separate obligations; this certificate deliberately does not assert them.
No general Body admission or compiler/physical semantics is installed. -/
namespace Solidity.Frontend.YulJson.ScopedJson
open Lean (Json)
open Solidity.Yul

inductive Error where
  | json (reason : YulJson.Error)
  | safety (reason : Refusal)
  | syntax (reason : ScopedSyntax.Error)
  deriving Repr

structure Checked {X table original} (input : @MetadataWords.Input X table original)
    (outside localNames : List String) (bound : Nat) (node : Json) where
  imported : Metadata table
  imported_eq : metadata table node = .ok imported
  rawSpan : String
  rawSpan_eq : string node "src" = .ok rawSpan
  span : SourceSpan
  span_eq : sourceSpan rawSpan = .ok span
  ast : Json
  ast_eq : field node "AST" = .ok ast
  shaped : ShapedBlock bound ast
  safe : SafetyCertificate imported.flags imported.documentation
  prepared : ScopedSyntax.Prepared input.scope .A outside localNames shaped.tree

private def witnessed {α : Type} (result : Except YulJson.Error α) :
    Except Error {value : α // result = .ok value} :=
  match result with
  | .error reason => .error (.json reason)
  | .ok value => .ok ⟨value,rfl⟩

def check {X table original} (input : @MetadataWords.Input X table original)
    (outside localNames : List String) (bound : Nat) (node : Json) :
    Except Error (Checked input outside localNames bound node) := do
  let ⟨imported,imported_eq⟩ ← witnessed (metadata table node)
  let ⟨rawSpan,rawSpan_eq⟩ ← witnessed (string node "src")
  let ⟨span,span_eq⟩ ← witnessed (sourceSpan rawSpan)
  let ⟨ast,ast_eq⟩ ← witnessed (field node "AST")
  let shaped ← (checkBlockShape bound ast).mapError Error.json
  let safe ← (checkMetadataSafety imported.flags imported.documentation).mapError Error.safety
  let prepared ← (ScopedSyntax.prepare input.scope .A outside localNames shaped.tree).mapError Error.syntax
  pure ⟨imported,imported_eq,rawSpan,rawSpan_eq,span,span_eq,ast,ast_eq,shaped,safe,prepared⟩

/-- Raw JSON boundary retains the existing input-byte-derived decoder bound.
No decoder-bound sufficiency or Source text attachment theorem is asserted. -/
def checkText {X table original} (input : @MetadataWords.Input X table original)
    (outside localNames : List String) (raw : String) :
    Except Error ((node : Json) × Checked input outside localNames (raw.toUTF8.size+1) node) := do
  let node ← (Json.parse raw).mapError (fun reason => Error.json (.json reason))
  pure ⟨node, ← check input outside localNames (raw.toUTF8.size+1) node⟩

private theorem witnessed_complete {α : Type} (result : Except YulJson.Error α)
    (value : α) (actual : result = .ok value) :
    witnessed result = .ok ⟨value,actual⟩ := by subst result; rfl

/-- Exact reconstruction against the real decoder equations and intrinsic
certificates, not an independent Source/JSON provenance or admission theorem. -/
theorem Checked.complete {X table original input outside localNames bound node}
    (checked : @Checked X table original input outside localNames bound node) :
    check input outside localNames bound node = .ok checked := by
  cases checked with
  | mk imported imported_eq rawSpan rawSpan_eq span span_eq ast ast_eq shaped safe prepared =>
      simp only [check,witnessed_complete _ _ imported_eq,
        witnessed_complete _ _ rawSpan_eq,witnessed_complete _ _ span_eq,
        witnessed_complete _ _ ast_eq,Words.shaped_complete shaped,Words.safety_complete safe,
        prepared.complete,bind,Except.bind,Except.mapError,pure,Except.pure]

theorem check_iff {X table original} (input : @MetadataWords.Input X table original)
    (outside localNames : List String) (bound : Nat) (node : Json) :
    (check input outside localNames bound node).isOk = true ↔
      Nonempty (Checked input outside localNames bound node) := by
  constructor
  · intro valid
    cases actual : check input outside localNames bound node with
    | error reason => rw [actual] at valid; cases valid
    | ok checked => exact ⟨checked⟩
  · rintro ⟨checked⟩
    rw [checked.complete]
    rfl

def Checked.run {X table original input outside localNames bound node}
    (checked : @Checked X table original input outside localNames bound node)
    (fuel : Nat) (cells : WordCells X) :=
  checked.prepared.openRun fuel cells

/-- Actual independent pure execution equals the existing word runner at every
horizon, supplied raw state and real imported/prepared program. -/
theorem Checked.run_agrees {X table original input outside localNames bound node}
    (checked : @Checked X table original input outside localNames bound node)
    (fuel : Nat) (cells : WordCells X) :
    checked.run fuel cells = checked.prepared.rawRun fuel cells :=
  checked.prepared.openRun_eq_rawRun fuel cells

theorem Checked.rule_sound {X table original input outside localNames bound node}
    (checked : @Checked X table original input outside localNames bound node)
    (mode : Solidity.Modality) (post : WordAdapter.Outcome X ClosedSyntax.rootControl 0 → Prop) :
    ∃ premise : Logic.Fml (0 + wordCellCount X), ∀ cells : WordCells X,
      OpenRun.holds mode checked.prepared.typing.code checked.prepared.policy post
        ⟨Fin.elim0,cells⟩ ↔
      premise.holds (WordState.pack (X := X) (n := 0) ⟨Fin.elim0,cells⟩) :=
  checked.prepared.openState_rule_sound mode post

end Solidity.Frontend.YulJson.ScopedJson
