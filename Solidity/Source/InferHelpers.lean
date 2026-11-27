import Solidity.Source.Types


namespace Solidity.H62.InferHelpers.Shared

open Solidity.Source

def isMapping (τ : STy) : Bool := τ matches .mapping _ _

def payableArg (σ : STy) : Bool :=
  match σ with
  | .address _ => true
  | .contract _ => true
  | _ => false

def convLoc (σ : STy) : DataLoc :=
  match σ with
  | .bytes l => l
  | .string l => l
  | _ => .memory

theorem isMapping_rule (τ : STy) : isMapping τ = (τ matches .mapping _ _) := rfl

theorem payableArg_rule (σ : STy) :
    payableArg σ = (match σ with | .address _ => true | .contract _ => true | _ => false) := rfl

theorem convLoc_rule (σ : STy) :
    convLoc σ = (match σ with | .bytes l => l | .string l => l | _ => .memory) := rfl


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
