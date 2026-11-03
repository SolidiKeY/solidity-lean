import Solidity.Backend.Passes.SourceTypedCall

/-! G22.02: transport actual dispatched child outcomes through the source
frame wrapper. The premises are executions of `dispatch`, not an assumed
storage frame. No invariant or typed intrinsic projection is inferred. -/
namespace Solidity.Backend.Passes.SourceCallFrame
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)

variable {E : Env}

private theorem run_modSt {α : Type} (f : St E → St E) (k : Unit → EM E [] α)
    (x : Locals E.layout [] × St E) :
    (EM.modSt f >>= k).run x = (k ()).run (x.1, f x.2) := rfl

private theorem run_attempt {α β : Type} (m : EM E [] α)
    (k : Except Halt α → EM E [] β) (x : Locals E.layout [] × St E) :
    (EM.attempt m >>= k).run x =
      (let (r, y) := m.run x; (k r).run y) := by
  rw [ExceptT.run_bind]
  show StateT.bind (ExceptT.run (EM.attempt m)) _ x = _
  simp only [StateT.bind, EM.attempt, ExceptT.run]
  rcases m.run x with ⟨r, y⟩
  rfl

def childFrame (a sender : Address) (v : Word) (input : Bytes) (static : Bool) (c : String) (depth : Nat) : Fr :=
  { this := a, sender := sender, value := v, static := static, contract := c, depth := depth, cd := input }

/-- The same rollback update used by the source wrapper, applied after
restoring the supplied mark's memory. Events remain observable. -/
def rolledBack (dirty : St E) (mark : Nat × Nat × Heap E.layout) : St E :=
  { dirty with
    heap := mark.2.2
    ex := dirty.ex.undoN (dirty.ex.journal.length - mark.1)
    logs := dirty.logs.drop (dirty.logs.length - mark.2.1) }

/-- A reverted actual child dispatch applies exactly its supplied mark,
retaining its raw data and all recorded events. -/
theorem enter_revert (G : Glob E) (n : Nat) (a sender : Address) (v : Word)
    (input data : Bytes) (static : Bool) (c : String) (depth : Nat)
    (mark : Nat × Nat × Heap E.layout) (before dirty : St E) (locals : Locals E.layout [])
    (execution : (dispatch G (childFrame a sender v input static c depth) n input).run
      (L0 E, { before with heap := Heap.empty }) = (.error (.revert data), (locals, dirty))) :
    (enterInstance G (n + 1) a sender v input static c depth mark).run (L0 E, before) =
      (.ok (.revert data), (locals, rolledBack dirty mark)) := by
  rw [enterInstance, run_modSt, run_attempt]
  dsimp only [childFrame] at execution
  dsimp only
  rw [execution]
  rfl

/-- Successful child execution keeps its writes, restores the supplied mark memory,
and returns the exact bytes; static restrictions belong to dispatch. -/
theorem enter_success (G : Glob E) (n : Nat) (a sender : Address) (v : Word)
    (input data : Bytes) (static : Bool) (c : String) (depth : Nat)
    (mark : Nat × Nat × Heap E.layout) (before dirty : St E) (locals : Locals E.layout [])
    (execution : (dispatch G (childFrame a sender v input static c depth) n input).run
      (L0 E, { before with heap := Heap.empty }) = (.ok data, (locals, dirty))) :
    (enterInstance G (n + 1) a sender v input static c depth mark).run (L0 E, before) =
      (.ok (.success data), (locals, { dirty with heap := mark.2.2 })) := by
  rw [enterInstance, run_modSt, run_attempt]
  dsimp only [childFrame] at execution
  dsimp only
  rw [execution]
  rfl

/-- Non-revert halts (including horizon exhaustion) are not turned into
successful bytes or catchable child reverts by the frame wrapper. -/
theorem enter_halt (G : Glob E) (n : Nat) (a sender : Address) (v : Word)
    (input : Bytes) (static : Bool) (c : String) (depth : Nat)
    (mark : Nat × Nat × Heap E.layout) (before dirty : St E) (locals : Locals E.layout [])
    (h : Halt) (notRevert : ∀ data, h ≠ .revert data)
    (execution : (dispatch G (childFrame a sender v input static c depth) n input).run
      (L0 E, { before with heap := Heap.empty }) = (.error h, (locals, dirty))) :
    (enterInstance G (n + 1) a sender v input static c depth mark).run (L0 E, before) =
      (.error h, (locals, { dirty with heap := mark.2.2 })) := by
  rw [enterInstance, run_modSt, run_attempt]
  dsimp only [childFrame] at execution
  dsimp only
  rw [execution]
  cases h with
  | revert data => exact False.elim (notRevert data rfl)
  | stuck why => rfl
  | timeout => rfl

/-- The actual source mark operation records the live checkpoint, including
argument effects already present in `before`. -/
theorem live_mark (before : St E) :
    (Solidity.Source.mark (Γ := [])).run (L0 E, before) =
      (.ok (before.ex.journal.length, before.logs.length, before.heap), (L0 E, before)) := rfl

end Solidity.Backend.Passes.SourceCallFrame
