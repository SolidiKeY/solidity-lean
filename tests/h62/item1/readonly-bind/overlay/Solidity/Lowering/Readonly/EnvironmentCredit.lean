import Solidity.Source.Hoare
import Solidity.Lowering.Readonly.EnvironmentSteps

/-! Exact source environment-credit and callback-credit failure equations.
Credits remain permitted while static. These statements transport actual
operation runs, not payment rules or a whole-world preservation claim. -/
namespace Solidity.Lowering.Readonly.EnvironmentCredit
open Solidity.Source
open Solidity.Roadmap (Address Word Outcome)
open EM EnvironmentSteps
variable {E : Env}


private theorem run_st (state : St E) :
    (st : EM E [] (St E)).run (L0 E, state) = (.ok state, (L0 E, state)) := rfl
private theorem run_emit (event : Solidity.Roadmap.Event) (state : St E) :
    (emitEvent event : EM E [] Unit).run (L0 E, state) =
      (.ok (), (L0 E, {state with events := state.events ++ [event]})) := rfl
private theorem run_pure {α : Type} (value : α) (state : St E) :
    (pure value : EM E [] α).run (L0 E, state) = (.ok value, (L0 E, state)) := rfl
private theorem run_mark (state : St E) :
    (mark : EM E [] _).run (L0 E, state) = (.ok (checkpoint state), (L0 E, state)) := rfl


def recorded (state : St E) (target : Address) (value : Word) : St E :=
  {state with events := state.events ++ [.credit target value]}

theorem known (global : Glob E) (n depth : Nat) (mode : Bool)
    (state final : St E) (target : Address) (value : Word) (code : String)
    (choice : global.callee state.events = .credit target value)
    (instanceRun : (instanceAt global target : EM E [] _).run (L0 E, recorded state target value) =
      (.ok (some code), (L0 E, recorded state target value)))
    (creditRun : (credit target value : EM E [] Unit).run (L0 E, recorded state target value) =
      (.ok (), (L0 E, final))) :
    (envLoop global (n + 1) depth mode).run (L0 E, state) =
      (envLoop global n depth mode).run (L0 E, final) := by
  rw [envLoop]
  simp only [Solidity.Source.Hoare.run_bind, run_st, choice, run_emit]
  dsimp only [recorded] at instanceRun creditRun
  rw [instanceRun]
  simp only [Option.isSome, ↓reduceIte, Solidity.Source.Hoare.run_bind, creditRun]

theorem unknown (global : Glob E) (n depth : Nat) (mode : Bool)
    (state : St E) (target : Address) (value : Word)
    (choice : global.callee state.events = .credit target value)
    (instanceRun : (instanceAt global target : EM E [] _).run (L0 E, recorded state target value) =
      (.ok none, (L0 E, recorded state target value))) :
    (envLoop global (n + 1) depth mode).run (L0 E, state) =
      (envLoop global n depth mode).run (L0 E, recorded state target value) := by
  rw [envLoop]
  simp only [Solidity.Source.Hoare.run_bind, run_st, choice, run_emit]
  dsimp only [recorded] at instanceRun
  rw [instanceRun]
  simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte, Solidity.Source.Hoare.run_bind, run_pure, recorded]

theorem failed (global : Glob E) (n depth : Nat) (mode : Bool)
    (state final : St E) (target : Address) (value : Word) (code : String) (halt : Halt)
    (choice : global.callee state.events = .credit target value)
    (instanceRun : (instanceAt global target : EM E [] _).run (L0 E, recorded state target value) =
      (.ok (some code), (L0 E, recorded state target value)))
    (creditRun : (credit target value : EM E [] Unit).run (L0 E, recorded state target value) =
      (.error halt, (L0 E, final))) :
    (envLoop global (n + 1) depth mode).run (L0 E, state) = (.error halt, (L0 E, final)) := by
  rw [envLoop]
  simp only [Solidity.Source.Hoare.run_bind, run_st, choice, run_emit]
  dsimp only [recorded] at instanceRun creditRun
  rw [instanceRun]
  simp only [Option.isSome, ↓reduceIte, Solidity.Source.Hoare.run_bind, creditRun]

/-- Credit failure precedes entering the callback and bypasses this enclosing
step's completion/continuation, keeping any existing nested events unchanged. -/
theorem callback_credit_failed (global : Glob E) (n depth : Nat) (mode requested : Bool)
    (state final : St E) (target sender : Address) (value : Word) (input : Solidity.Roadmap.Bytes)
    (code : String) (halt : Halt)
    (choice : global.callee state.events = .reenter target sender value input requested)
    (guard : (decide (depth ≥ 1024) || (mode && decide (value.val ≠ 0))) = false)
    (instanceRun : (instanceAt global target : EM E [] _).run
      (L0 E, entered state target sender value input requested) =
        (.ok (some code), (L0 E, entered state target sender value input requested)))
    (creditRun : (credit target value : EM E [] Unit).run
      (L0 E, entered state target sender value input requested) = (.error halt, (L0 E, final))) :
    (envLoop global (n + 1) depth mode).run (L0 E, state) = (.error halt, (L0 E, final)) := by
  rw [envLoop]
  simp only [Solidity.Source.Hoare.run_bind, run_st, choice, run_emit, guard, Bool.false_eq_true, ↓reduceIte]
  dsimp only [entered] at instanceRun creditRun
  rw [instanceRun]
  simp only [Solidity.Source.Hoare.run_bind, run_mark, checkpoint, creditRun]

end Solidity.Lowering.Readonly.EnvironmentCredit
