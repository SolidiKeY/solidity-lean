import Solidity.Yul.BuiltinUse
import Solidity.Frontend.SolcJson.YulScopedParse
import Solidity.Frontend.SolcJson.YulForwardJson
/-! Additive builtin-use validation over the ACTUAL existing preparation APIs.
Old namespace/static certificates retain their narrower contracts unchanged.
This layer is not general Body admission, reverse provenance or MemOK. -/
namespace Solidity.Frontend.YulJson.BuiltinGuard
open Lean (Json)
open Solidity.Yul
open Solidity.Yul.BlockScope (Scope)
open Solidity.Frontend.Checked (Bytes)

inductive ParseError where
  | prior (reason : ScopedParse.Error)
  | builtin (reason : BuiltinUse.Failure)
  deriving Repr

structure Parsed {X} (scope : Scope X) (tier : Tier) (outside localNames : List String)
    (documentation : Option String) (src : Bytes) where
  original : ScopedParse.Checked scope tier outside localNames documentation src
  uses : BuiltinUse.Checked original.parsed.body

def parse {X} (scope : Scope X) (tier : Tier) (outside localNames : List String)
    (documentation : Option String) (src : Bytes) :
    Except ParseError (Parsed scope tier outside localNames documentation src) := do
  let original ← (ScopedParse.check scope tier outside localNames documentation src).mapError ParseError.prior
  let uses ← (BuiltinUse.check original.parsed.body).mapError ParseError.builtin
  pure ⟨original,uses⟩

theorem Parsed.complete {X scope tier outside localNames documentation src}
    (checked : @Parsed X scope tier outside localNames documentation src) :
    parse scope tier outside localNames documentation src = .ok checked := by
  cases checked with
  | mk original uses =>
      simp only [parse,original.complete,uses.complete,Except.mapError,bind,Except.bind,pure,Except.pure]

theorem parse_iff {X} (scope : Scope X) (tier : Tier) (outside localNames : List String)
    (documentation : Option String) (src : Bytes) :
    (parse scope tier outside localNames documentation src).isOk = true ↔
      Nonempty (Parsed scope tier outside localNames documentation src) := by
  constructor
  · intro accepted
    cases actual : parse scope tier outside localNames documentation src with
    | error reason => rw [actual] at accepted; cases accepted
    | ok checked => exact ⟨checked⟩
  · rintro ⟨checked⟩
    rw [checked.complete]
    rfl

/-- The additional guard does not change the SAME actual prepared execution. -/
def Parsed.closedRun {outside localNames documentation src}
    (checked : Parsed .closed .A outside localNames documentation src) (fuel : Nat) :=
  checked.original.closedRun fuel

theorem Parsed.closedRun_eq {outside localNames documentation src}
    (checked : Parsed .closed .A outside localNames documentation src) (fuel : Nat) :
    checked.closedRun fuel = checked.original.closedRun fuel := rfl

inductive JsonError where
  | prior (reason : ForwardJson.Error)
  | builtin (reason : BuiltinUse.Failure)
  deriving Repr

structure JsonChecked {X table names} (input : @MetadataWords.Input X table names)
    (outside localNames : List String) (bound : Nat) (node : Json) where
  original : ForwardJson.Checked input outside localNames bound node
  uses : BuiltinUse.Checked original.imported.shaped.tree

def checkJson {X table names} (input : @MetadataWords.Input X table names)
    (outside localNames : List String) (bound : Nat) (node : Json) :
    Except JsonError (JsonChecked input outside localNames bound node) := do
  let original ← (ForwardJson.check input outside localNames bound node).mapError JsonError.prior
  let uses ← (BuiltinUse.check original.imported.shaped.tree).mapError JsonError.builtin
  pure ⟨original,uses⟩

theorem JsonChecked.complete {X table names input outside localNames bound node}
    (checked : @JsonChecked X table names input outside localNames bound node) :
    checkJson input outside localNames bound node = .ok checked := by
  cases checked with
  | mk original uses =>
      simp only [checkJson,original.complete,uses.complete,Except.mapError,bind,Except.bind,pure,Except.pure]

theorem checkJson_iff {X table names} (input : @MetadataWords.Input X table names)
    (outside localNames : List String) (bound : Nat) (node : Json) :
    (checkJson input outside localNames bound node).isOk = true ↔
      Nonempty (JsonChecked input outside localNames bound node) := by
  constructor
  · intro accepted
    cases actual : checkJson input outside localNames bound node with
    | error reason => rw [actual] at accepted; cases accepted
    | ok checked => exact ⟨checked⟩
  · rintro ⟨checked⟩
    rw [checked.complete]
    rfl

def checkJsonText {X table names} (input : @MetadataWords.Input X table names)
    (outside localNames : List String) (raw : String) :
    Except JsonError ((node : Json) × JsonChecked input outside localNames (raw.toUTF8.size+1) node) := do
  let ⟨node,original⟩ ← (ForwardJson.checkText input outside localNames raw).mapError JsonError.prior
  let uses ← (BuiltinUse.check original.imported.shaped.tree).mapError JsonError.builtin
  pure ⟨node,⟨original,uses⟩⟩

def JsonChecked.run {X table names input outside localNames bound node}
    (checked : @JsonChecked X table names input outside localNames bound node)
    (fuel : Nat) (cells : WordCells X) :=
  checked.original.run fuel cells

/-- Concrete final run composition through the SAME actual checked JSON tree,
not a caller-supplied parser/static/execution agreement law. -/
theorem JsonChecked.run_agrees {X table names input outside localNames bound node}
    (checked : @JsonChecked X table names input outside localNames bound node)
    (fuel : Nat) (cells : WordCells X) :
    checked.run fuel cells = checked.original.imported.prepared.rawRun fuel cells :=
  checked.original.run_agrees fuel cells

end Solidity.Frontend.YulJson.BuiltinGuard
