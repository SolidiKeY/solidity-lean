import Solidity.Frontend.Admission.NameResolutionRoots
import Solidity.Frontend.Admission.ProgramObservationControls

/-! Inhabited source resolver controls. The synthetic declaration roster is not a SourceSpec, Elaborated witness or solc import/correctness claim. -/
namespace Solidity.Frontend.Admission.NameResolutionControls
open Solidity.Source ProgramControls

def context : Ctx := {env := env, scope := some "C", locals := []}
def shadowed : Ctx := context.push "run" (.int IntTy.u256)

/-- Populated selection, local precedence, unknown-name refusal and rejection of a constant as a function all use the actual resolver. -/
theorem resolver_controls :
    context.functions "run" = [functionDecl] ∧
    shadowed.resolve "run" = some (.loc 0) ∧
    shadowed.functions "run" = [] ∧
    context.functions "missing" = [] ∧
    context.functions "seed" = [] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- info: 'Solidity.Frontend.Admission.NameResolutionControls.resolver_controls' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms resolver_controls
end Solidity.Frontend.Admission.NameResolutionControls
