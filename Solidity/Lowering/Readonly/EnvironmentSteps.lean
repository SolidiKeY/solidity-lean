import Solidity.Source.Eval

/-! Actual environment callback-loop step transport. These equations expose
the exact source child execution boundary; they do not manufacture child
histories, deployed-code linkage, intrinsic frames or compiler adequacy. -/
namespace Solidity.Lowering.Readonly.EnvironmentSteps
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open EM
variable {E : Env}
private theorem run_bind {α β : Type} (m : EM E Γ α) (k : α → EM E Γ β)
    (x : Locals E.layout Γ × St E) :
    (m >>= k).run x = match m.run x with
      | (.ok a, y) => (k a).run y
      | (.error e, y) => (.error e, y) := by
  rw [ExceptT.run_bind]
  show StateT.bind (ExceptT.run m) _ x = _
  simp only [StateT.bind]
  rcases m.run x with ⟨r, y⟩
  cases r <;> rfl


def entered (state : St E) (t sender : Address) (v : Word) (input : Bytes) (requested : Bool) : St E :=
  { state with events := state.events ++ [.reenter t sender v input requested] }
def completed (state : St E) (out : Outcome) : St E :=
  { state with events := state.events ++ [.reentered out] }
def checkpoint (state : St E) : Nat × Nat × Heap E.layout :=
  (state.ex.journal.length, state.logs.length, state.heap)

private theorem run_st (state : St E) :
    (st : EM E [] (St E)).run (L0 E, state) = (.ok state, (L0 E, state)) := rfl
private theorem run_emit (event : Solidity.Roadmap.Event) (state : St E) :
    (emitEvent event : EM E [] Unit).run (L0 E, state) =
      (.ok (), (L0 E, {state with events := state.events ++ [event]})) := rfl
private theorem run_pure {α : Type} (value : α) (state : St E) :
    (pure value : EM E [] α).run (L0 E, state) = (.ok value, (L0 E, state)) := rfl
private theorem run_mark (state : St E) :
    (mark : EM E [] _).run (L0 E, state) = (.ok (checkpoint state), (L0 E, state)) := rfl

/-- Answers retain their exact success/revert bytes and append the answer event. -/
theorem answer (global : Glob E) (n depth : Nat) (mode : Bool) (state : St E) (out : Outcome)
    (choice : global.callee state.events = .answer out) :
    (envLoop global (n + 1) depth mode).run (L0 E, state) =
      (.ok out, (L0 E, {state with events := state.events ++ [.answer out none]})) := by
  rw [envLoop]
  simp only [run_bind, run_st, choice, run_emit, run_pure]

/-- A forbidden value/depth attempt is recorded as a failed callback; the
strategy continues. This does not forbid permitted read-only reentry. -/
theorem refused (global : Glob E) (n depth : Nat) (mode requested : Bool)
    (state : St E) (t sender : Address) (v : Word) (input : Bytes)
    (choice : global.callee state.events = .reenter t sender v input requested)
    (guard : (decide (depth ≥ 1024) || (mode && decide (v.val ≠ 0))) = true) :
    (envLoop global (n + 1) depth mode).run (L0 E, state) =
      (envLoop global n depth mode).run
        (L0 E, completed (entered state t sender v input requested) (.revert [])) := by
  rw [envLoop]
  simp only [run_bind, run_st, choice, run_emit, guard, ↓reduceIte, run_pure]
  rfl

/-- A real admitted child returning an Outcome (success or revert) resumes the same environment strategy with
its exact child-final state, bytes and inherited static mode. -/
theorem child_success (global : Glob E) (n depth : Nat) (mode requested : Bool)
    (state credited final : St E) (t sender : Address) (v : Word) (input : Bytes)
    (code : String) (out : Outcome)
    (choice : global.callee state.events = .reenter t sender v input requested)
    (guard : (decide (depth ≥ 1024) || (mode && decide (v.val ≠ 0))) = false)
    (instanceRun : (instanceAt global t : EM E [] _).run
      (L0 E, entered state t sender v input requested) =
        (.ok (some code), (L0 E, entered state t sender v input requested)))
    (creditRun : (credit t v : EM E [] Unit).run
      (L0 E, entered state t sender v input requested) = (.ok (), (L0 E, credited)))
    (childRun : (enterInstance global n t sender v input (requested || mode) code (depth + 1)
      (checkpoint state)).run (L0 E, credited) = (.ok out, (L0 E, final))) :
    (envLoop global (n + 1) depth mode).run (L0 E, state) =
      (envLoop global n depth mode).run (L0 E, completed final out) := by
  rw [envLoop]
  simp only [run_bind, run_st, choice, run_emit, guard, Bool.false_eq_true, ↓reduceIte]
  change _ = (envLoop global n depth mode).run (L0 E, completed final out)
  dsimp only [entered] at instanceRun creditRun
  rw [instanceRun]
  simp only [run_bind, run_mark, checkpoint]
  dsimp only [checkpoint] at childRun
  change _ = (envLoop global n depth mode).run (L0 E, completed final out)
  simp only [creditRun, childRun, run_emit, completed]

/-- A real child halt bypasses this enclosing step's completion event and
strategy continuation, retaining its exact final state (including any nested
events). Timeout or stuck outcomes are never converted into success. -/
theorem child_halt (global : Glob E) (n depth : Nat) (mode requested : Bool)
    (state credited final : St E) (t sender : Address) (v : Word) (input : Bytes)
    (code : String) (halt : Halt)
    (choice : global.callee state.events = .reenter t sender v input requested)
    (guard : (decide (depth ≥ 1024) || (mode && decide (v.val ≠ 0))) = false)
    (instanceRun : (instanceAt global t : EM E [] _).run
      (L0 E, entered state t sender v input requested) =
        (.ok (some code), (L0 E, entered state t sender v input requested)))
    (creditRun : (credit t v : EM E [] Unit).run
      (L0 E, entered state t sender v input requested) = (.ok (), (L0 E, credited)))
    (childRun : (enterInstance global n t sender v input (requested || mode) code (depth + 1)
      (checkpoint state)).run (L0 E, credited) = (.error halt, (L0 E, final))) :
    (envLoop global (n + 1) depth mode).run (L0 E, state) =
      (.error halt, (L0 E, final)) := by
  rw [envLoop]
  simp only [run_bind, run_st, choice, run_emit, guard, Bool.false_eq_true, ↓reduceIte]
  change _ = ((Except.error halt : Except Halt Outcome), (L0 E, final))
  dsimp only [entered] at instanceRun creditRun
  rw [instanceRun]
  simp only [run_bind, run_mark, checkpoint]
  dsimp only [checkpoint] at childRun
  change _ = ((Except.error halt : Except Halt Outcome), (L0 E, final))
  simp only [creditRun, childRun]

/-- No deployed instance at the requested callback receiver is a failed
callback attempt, not suppression of the remaining environment behavior. -/
theorem missing_instance (global : Glob E) (n depth : Nat) (mode requested : Bool)
    (state : St E) (t sender : Address) (v : Word) (input : Bytes)
    (choice : global.callee state.events = .reenter t sender v input requested)
    (guard : (decide (depth ≥ 1024) || (mode && decide (v.val ≠ 0))) = false)
    (instanceRun : (instanceAt global t : EM E [] _).run
      (L0 E, entered state t sender v input requested) =
        (.ok none, (L0 E, entered state t sender v input requested))) :
    (envLoop global (n + 1) depth mode).run (L0 E, state) =
      (envLoop global n depth mode).run
        (L0 E, completed (entered state t sender v input requested) (.revert [])) := by
  rw [envLoop]
  simp only [run_bind, run_st, choice, run_emit, guard, Bool.false_eq_true, ↓reduceIte]
  dsimp only [entered] at instanceRun
  rw [instanceRun]
  simp only [run_bind, run_pure, run_emit, completed, entered]


end Solidity.Lowering.Readonly.EnvironmentSteps
