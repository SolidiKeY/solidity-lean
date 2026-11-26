import Solidity.Goals.Headline
import Solidity.Goals.Endpoint

/-!
# Trust audit of the registered headline and endpoint

Check the exact registered propositions as well as the transitive dependencies
of their proofs. These checks concern the intrinsic model and instruction-list
endpoint; they establish no claim about solc, assembled bytes, or native verdicts.
-/
namespace Solidity.Examples.RedTeam.Trust.HeadlineAxioms

#check (Solidity.Main.compiler_correct_v2 : Solidity.Goals.compilerCorrectNoPaymentRevert)
#check (Solidity.Main.compiler_correct : Solidity.Goals.headlineIsNoPaymentRevert)
#check (Solidity.Backend.compiler_endpoint_correct : Solidity.Goals.compilerEndpointCorrect)

#print axioms Solidity.Main.compiler_correct_v2
#print axioms Solidity.Main.compiler_correct
#print axioms Solidity.Backend.compiler_endpoint_correct
#print axioms Solidity.Backend.compiler_endpoint_of_stages
#print axioms Solidity.Backend.static_stage

-- Reject any dependency outside Lean's three standard logical axioms.
open Lean Elab Command in
run_elab do
  for target in [``Solidity.Main.compiler_correct_v2,
      ``Solidity.Main.compiler_correct,
      ``Solidity.Backend.compiler_endpoint_correct,
      ``Solidity.Backend.compiler_endpoint_of_stages,
      ``Solidity.Backend.static_stage] do
    let dependencies ← collectAxioms target
    unless dependencies.all (fun name =>
        [``propext, ``Classical.choice, ``Quot.sound].contains name) do
      throwError "unexpected logical dependencies for {target}: {dependencies}"

end Solidity.Examples.RedTeam.Trust.HeadlineAxioms
