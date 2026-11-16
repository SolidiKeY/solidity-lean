import Solidity.Frontend.Admission.ProgramRoots
import Solidity.Frontend.Admission.ProgramObservationControls

/-! Actual carried-field inventory controls. The underlying Program fixture is synthetic, not an Elaborated or execution witness. -/
namespace Solidity.Frontend.Admission.RootControls
open Solidity.Source ProgramControls

def expected : List (ProgramRoot program) :=
  [.body functionDecl body, .constant constantDecl init,
   .body modifierDecl modifierBody, .constructor "C" body,
   .initializer "C" init, .baseArguments "C" base]

theorem exact_inventory : programRoots program = expected := rfl

/-- Removing a contract from the roster refuses its root even when its body lookup still returns a value. -/
theorem omitted_constructor_refused :
    (ProgramRoot.constructor "C" body : ProgramRoot omitted) ∉ programRoots omitted := by
  intro h
  have hc := ((programRoots_exact omitted _).mp h).1
  exact List.not_mem_nil hc

theorem omission_changes_cardinality :
    (programRoots omitted).length ≠ (programRoots program).length := by decide +kernel

theorem body_constant_distinct :
    (ProgramRoot.body functionDecl body : ProgramRoot program) ≠
      ProgramRoot.constant constantDecl init := by
  intro h
  cases h

/-- info: 'Solidity.Frontend.Admission.RootControls.exact_inventory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exact_inventory
/-- info: 'Solidity.Frontend.Admission.RootControls.omitted_constructor_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms omitted_constructor_refused
/-- info: 'Solidity.Frontend.Admission.RootControls.omission_changes_cardinality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms omission_changes_cardinality
/-- info: 'Solidity.Frontend.Admission.RootControls.body_constant_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_constant_distinct
end Solidity.Frontend.Admission.RootControls
