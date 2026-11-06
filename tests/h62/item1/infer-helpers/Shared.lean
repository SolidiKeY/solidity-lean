import Solidity.Source.Types

/-!
Candidate shared definitions for the mechanically copied inference helpers.
This additive, unregistered module changes neither existing inferencer. Its
location and namespace are provisional pending owner review. It has not been
Lean checked and is not evidence of production compatibility.
-/

namespace Solidity.H62.InferHelpers.Shared

open Solidity.Source

/-- The top-level mapping test used by the source delete rule. -/
def isMapping (τ : STy) : Bool := τ matches .mapping _ _

/-- The payable-argument test used by the source payable rule. -/
def payableArg (σ : STy) : Bool :=
  match σ with
  | .address _ => true
  | .contract _ => true
  | _ => false

/-- The argument location retained by an elementary conversion. -/
def convLoc (σ : STy) : DataLoc :=
  match σ with
  | .bytes l => l
  | .string l => l
  | _ => .memory

/-- The helper is the existing inline delete test. -/
theorem isMapping_rule (τ : STy) : isMapping τ = (τ matches .mapping _ _) := rfl

/-- The helper is the existing inline payable test. -/
theorem payableArg_rule (σ : STy) :
    payableArg σ = (match σ with | .address _ => true | .contract _ => true | _ => false) := rfl

/-- The helper is the existing inline elementary-conversion location. -/
theorem convLoc_rule (σ : STy) :
    convLoc σ = (match σ with | .bytes l => l | .string l => l | _ => .memory) := rfl

end Solidity.H62.InferHelpers.Shared
