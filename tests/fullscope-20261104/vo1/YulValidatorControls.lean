import Solidity.Optimizer.Laws
import Solidity.Yul.ClosedRun

/-!
# Interpreter-backed Yul branch controls

One existing intrinsic function-context statement reads a literal guard, leaves
when nonzero, otherwise writes its sole local. Existing owner effect-profile
proofs justify running this concrete example. This is not source admission,
world/physical/gas adequacy, a whole-program validator or an O02/O03 pass.
-/
namespace Solidity.Optimizer.YulValidatorControls
open Solidity.Yul

/-- Original intrinsic syntax, with fixed function/loop context and one local. -/
def branchProgram (condition : Word) : Solidity.Yul.Stmt [] [] ⟨true, false⟩ 1 :=
  .seq (.if_ (.literal condition) .leave)
    (.assign (fun _ : Fin 1 => .local 0) (.literal (word 7)))

/-- Erased owner profile evidence for this example, not a new language filter. -/
def profile (condition : Word) : Closed.StmtWordP (branchProgram condition) :=
  ⟨⟨True.intro, True.intro⟩, ⟨fun _ => True.intro, True.intro⟩⟩

/-- The actual owner interpreter, finite horizon and initialized local. -/
def runAt (fuel : Nat) (condition : Word) : Option (Closed.Outcome ⟨true, false⟩ 1) :=
  Closed.evalStmt fuel .nil True.intro (branchProgram condition) (profile condition)
    (fun _ => word 0)

/-- Selected local/control observations for this fixture only, not D6. -/
abbrev Observation := Option (Word × Bool)

def observed (fuel : Nat) (condition : Word) : Observation :=
  (runAt fuel condition).map (fun out => (out.vars 0, out.flow.isNormal))

/-- Zero guard reaches the actual following assignment. -/
theorem zero_guard_writes : observed 8 (word 0) = some (word 7, true) := rfl

/-- Nonzero guard leaves and prevents the following assignment. -/
theorem nonzero_guard_leaves : observed 8 (word 1) = some (word 0, false) := rfl

/-- An exhausted horizon is retained; it is not a successful zero result. -/
theorem zero_horizon : observed 0 (word 1) = none := rfl

/-- An initialized nontrivial typed Yul program has a real observed result. -/
theorem inhabited : ∃ condition : Word, observed 8 condition = some (word 7, true) :=
  ⟨word 0, rfl⟩

/-- A concrete bad candidate: erase the reached leave, not its guard. -/
def erasedProgram : Solidity.Yul.Stmt [] [] ⟨true, false⟩ 1 :=
  .seq (.if_ (.literal (word 1)) .skip)
    (.assign (fun _ : Fin 1 => .local 0) (.literal (word 7)))

def erasedProfile : Closed.StmtWordP erasedProgram :=
  ⟨⟨True.intro, True.intro⟩, ⟨fun _ => True.intro, True.intro⟩⟩

def erasedObservation (fuel : Nat) : Observation :=
  (Closed.evalStmt fuel .nil True.intro erasedProgram erasedProfile (fun _ => word 0)).map
    (fun out => (out.vars 0, out.flow.isNormal))

theorem erased_program_writes : erasedObservation 8 = some (word 7, true) := rfl

/-- Equality checker is instantiated at actual returned fixture data. -/
def resultValidator : Validator (fun a b : Observation => a = b) :=
  Validator.equality Observation

/-- Positive result-level control uses the actual interpreter output. -/
theorem correct_result_accepted :
    resultValidator.validate (observed 8 (word 0)) (some (word 7, true)) = true := rfl

/-- Changing the reached guard changes these actual observations. -/
theorem erased_leave_rejected :
    resultValidator.validate (observed 8 (word 1)) (observed 8 (word 0)) = false := rfl

/-- The actual bad AST candidate differs from the original interpreter run. -/
theorem actual_erase_rejected :
    resultValidator.validate (observed 8 (word 1)) (erasedObservation 8) = false := rfl

/-- Replacing a reached result with a horizon failure is also rejected. -/
theorem dropped_result_rejected :
    resultValidator.validate (observed 8 (word 0)) (observed 0 (word 0)) = false := rfl

#print axioms profile
#print axioms zero_guard_writes
#print axioms nonzero_guard_leaves
#print axioms zero_horizon
#print axioms inhabited
#print axioms erasedProfile
#print axioms erased_program_writes
#print axioms resultValidator
#print axioms correct_result_accepted
#print axioms erased_leave_rejected
#print axioms actual_erase_rejected
#print axioms dropped_result_rejected

end Solidity.Optimizer.YulValidatorControls
