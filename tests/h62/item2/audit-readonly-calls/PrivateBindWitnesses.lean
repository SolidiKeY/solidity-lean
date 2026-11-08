import Lean
import Solidity.Lowering.Readonly.PrimitiveReads

/-! Guard private bind identities and discarded success/failure states. Exact
private constants are applied to the same nonempty locals, effectful action and
continuation. A failure retains its preceding effect and skips the continuation;
an early halt leaves the initial state untouched. SDK name macros are test-only,
never core imports. No callee/compiler/physical-frame adequacy is inferred. -/
namespace Solidity.H62.ReadonlyAudit.PrivateBindWitnesses
open Solidity.Source
macro "original_halt_bind" : term =>
  return Lean.mkIdent (Lean.mkPrivateNameCore `Solidity.Backend.Passes.SourceCallBoundary
    `Solidity.Backend.Passes.SourceCallBoundary.halt_bind)
macro "original_typed_bind" : term =>
  return Lean.mkIdent (Lean.mkPrivateNameCore `Solidity.Backend.Passes.SourceTypedCall
    `Solidity.Backend.Passes.SourceTypedCall.run_bind)
macro "original_read_bind" : term =>
  return Lean.mkIdent (Lean.mkPrivateNameCore `Solidity.Lowering.Readonly.PrimitiveReads
    `Solidity.Lowering.Readonly.PrimitiveReads.run_bind)

def environment : Env := ⟨[]⟩
def state : St environment :=
  { ex := { world := ⟨fun a => Account.empty (D := environment.layout) (environment.lay a)⟩,
            transient := ⟨fun _ => Storage.empty⟩, journal := [] }
    heap := Solidity.Source.Heap.empty, events := [], logs := [], fnLocals := ⟨[], .nil⟩ }
def before : Locals environment.layout [.bool] × St environment := (.cons (.bool true) .nil, state)
def firstEvent : Solidity.Roadmap.Event := .answer (.success [9]) none
def secondEvent : Solidity.Roadmap.Event := .answer (.success [7]) none
def reached : St environment := { state with events := [firstEvent] }
def continued : St environment := { state with events := [firstEvent, secondEvent] }
def first : EM environment [.bool] Bool := do
  EM.modSt (fun s => { s with events := s.events ++ [firstEvent] })
  pure true
def next (value : Bool) : EM environment [.bool] Bool := do
  EM.modSt (fun s => { s with events := s.events ++ [secondEvent] })
  pure (!value)
def failed : EM environment [.bool] Bool := do
  EM.modSt (fun s => { s with events := s.events ++ [firstEvent] })
  EM.halt (.revert [5])

theorem halt_joint :
    (EM.halt (.revert [5]) >>= next : EM environment [.bool] Bool) = EM.halt (.revert [5]) :=
  original_halt_bind (.revert [5]) next

theorem typed_joint : (first >>= next).run before = match first.run before with
    | (.ok value, after) => (next value).run after
    | (.error error, after) => (.error error, after) :=
  original_typed_bind first next before

theorem read_joint : (first >>= next).run before = match first.run before with
    | (.ok value, after) => (next value).run after
    | (.error error, after) => (.error error, after) :=
  original_read_bind first next before

theorem success_observed : (first >>= next).run before =
    (.ok false, (.cons (.bool true) .nil, continued)) := rfl

theorem failure_joint : (failed >>= next).run before = match failed.run before with
    | (.ok value, after) => (next value).run after
    | (.error error, after) => (.error error, after) :=
  original_typed_bind failed next before

theorem failure_observed : (failed >>= next).run before =
    (.error (.revert [5]), (.cons (.bool true) .nil, reached)) := rfl

theorem halt_observed :
    (EM.halt (.revert [5]) >>= next : EM environment [.bool] Bool).run before =
      (.error (.revert [5]), before) := by
  rw [halt_joint]
  rfl

/-- The continuation cannot be replaced by the first action alone. -/
theorem dropped_continuation_refused : (first >>= next).run before ≠ first.run before := by
  intro same
  have values := congrArg Prod.fst same
  change (Except.ok false : Except Halt Bool) = .ok true at values
  cases values

/-- An error retains the first event, rather than restoring the old empty state. -/
theorem discarded_failure_state_refused :
    ((failed >>= next).run before).2.2.events ≠ state.events := by decide

end Solidity.H62.ReadonlyAudit.PrivateBindWitnesses
