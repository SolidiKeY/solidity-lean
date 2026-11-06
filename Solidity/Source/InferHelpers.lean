import Solidity.Source.Types

/-!
Guarded regression: source and static inference must agree on the shallow mapping
check, address/contract payable arguments, and bytes/string conversion locations.
The common definitions retain the memory fallback and the original rule shapes.
The original inferencer definitions remain unchanged, including their generated
equations. Pointwise agreement lemmas provide the canonical migration interface.
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

/-! Witnesses distinguish the actual helper outcomes and location behavior. -/

example (key value : STy) : isMapping (.mapping key value) = true := rfl
example (key value : STy) (loc : DataLoc) :
    isMapping (.array loc (.mapping key value) none) = false := rfl
example (payable : Bool) : payableArg (.address payable) = true := rfl
example (name : DeclName) : payableArg (.contract name) = true := rfl
example : payableArg .bool = false := rfl
example (loc : DataLoc) : convLoc (.bytes loc) = loc := rfl
example (loc : DataLoc) : convLoc (.string loc) = loc := rfl
example (loc : DataLoc) (elem : STy) (len : Option Nat) :
    convLoc (.array loc elem len) = .memory := rfl

end Solidity.H62.InferHelpers.Shared
