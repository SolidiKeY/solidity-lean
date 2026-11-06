import Solidity.Frontend.SolcJson.YulScopedJson
import Solidity.Frontend.SolcJson.YulReferenceCover

/-! Concrete typed JSON import + actual AST role collection + unique FORWARD
attachment of every provided metadata reference. Backward/free-reference
accounting, function-scope/provenance alignment and Body admission are not
claimed. The actual parser/static/safety and pure execution remain unchanged. -/
namespace Solidity.Frontend.YulJson.ForwardJson
open Lean (Json)
open Solidity.Yul

inductive Error where
  | imported (reason : ScopedJson.Error)
  | occurrences (reason : YulJson.Error)
  | references (reason : ReferenceCover.AllError)
  deriving Repr

structure Checked {X table original} (input : @MetadataWords.Input X table original)
    (outside localNames : List String) (bound : Nat) (node : Json) where
  imported : ScopedJson.Checked input outside localNames bound node
  collected : Occurrences.Collected imported.ast false
  collected_eq : Occurrences.collect bound imported.ast false = .ok collected
  references : ReferenceCover.All table original imported.ast imported.imported.references.entries

private def witnessed {α : Type} (result : Except YulJson.Error α) :
    Except Error {value : α // result = .ok value} :=
  match result with
  | .error reason => .error (.occurrences reason)
  | .ok value => .ok ⟨value,rfl⟩

def check {X table original} (input : @MetadataWords.Input X table original)
    (outside localNames : List String) (bound : Nat) (node : Json) :
    Except Error (Checked input outside localNames bound node) := do
  let imported ← (ScopedJson.check input outside localNames bound node).mapError Error.imported
  let ⟨collected,collected_eq⟩ ← witnessed (Occurrences.collect bound imported.ast false)
  let references ← (ReferenceCover.checkAll (original := original)
    collected imported.imported.references.entries).mapError Error.references
  pure ⟨imported,collected,collected_eq,references⟩

def checkText {X table original} (input : @MetadataWords.Input X table original)
    (outside localNames : List String) (raw : String) :
    Except Error ((node : Json) × Checked input outside localNames (raw.toUTF8.size+1) node) := do
  let node ← (Json.parse raw).mapError (fun reason => Error.imported (.json (.json reason)))
  pure ⟨node, ← check input outside localNames (raw.toUTF8.size+1) node⟩

private theorem witnessed_complete {α : Type} (result : Except YulJson.Error α)
    (value : α) (actual : result = .ok value) :
    witnessed result = .ok ⟨value,actual⟩ := by subst result; rfl

/-- Final concrete composition of actual decoder/static/safety, complete
position collection and provided-reference accounting. No helper law is assumed. -/
theorem Checked.complete {X table original input outside localNames bound node}
    (checked : @Checked X table original input outside localNames bound node) :
    check input outside localNames bound node = .ok checked := by
  cases checked with
  | mk imported collected collected_eq references =>
      simp only [check,imported.complete,witnessed_complete _ _ collected_eq,
        references.complete collected,bind,Except.bind,Except.mapError,pure,Except.pure]

theorem check_iff {X table original} (input : @MetadataWords.Input X table original)
    (outside localNames : List String) (bound : Nat) (node : Json) :
    (check input outside localNames bound node).isOk = true ↔
      Nonempty (Checked input outside localNames bound node) := by
  constructor
  · intro valid
    cases actual : check input outside localNames bound node with
    | error reason => rw [actual] at valid; cases valid
    | ok result => exact ⟨result⟩
  · rintro ⟨checked⟩
    rw [checked.complete]
    rfl

/-- An index in ACTUAL imported externalReferences returns the matching actual
AST position/role, original binding and intrinsic read/write capability. -/
def Checked.reference {X table original input outside localNames bound node}
    (checked : @Checked X table original input outside localNames bound node)
    (index : Fin checked.imported.imported.references.entries.length) :
    ReferenceCover.Unique table original checked.imported.ast
      (checked.imported.imported.references.entries.get index) :=
  checked.references.get index

def Checked.run {X table original input outside localNames bound node}
    (checked : @Checked X table original input outside localNames bound node)
    (fuel : Nat) (cells : WordCells X) :=
  checked.imported.run fuel cells

theorem Checked.run_agrees {X table original input outside localNames bound node}
    (checked : @Checked X table original input outside localNames bound node)
    (fuel : Nat) (cells : WordCells X) :
    checked.run fuel cells = checked.imported.prepared.rawRun fuel cells :=
  checked.imported.run_agrees fuel cells

end Solidity.Frontend.YulJson.ForwardJson
