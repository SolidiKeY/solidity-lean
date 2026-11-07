import Solidity.Stipend.Rule

/-! Isolated migration controls. These preserve the rule's constants and
exercise accepted/rejected witnesses and gas-boundary sensitivity. They do
not prove the compiler's Fitted/Enforced obligations. -/
namespace Solidity.Stipend.MigrationControls
open Solidity.Stipend
variable {C : Contract}

/-- Ten checks attain exactly the 2300-gas boundary. -/
example : progCost (requires 10 : Prog C [] []) = some 40 := requires_cost 10

/-- Eleven checks exceed it, rather than becoming an admitted witness. -/
example : ¬(rule C).fits ⟨(requires 11 : Prog C [] [])⟩ := requires_eleven_not_fits

/-- One less gas rejects the 40-unit boundary body. -/
example : fitsWith osakaCold 2299 ⟨(requires 10 : Prog C [] [])⟩ = false := rfl

/-- The exact boundary is admitted. -/
example : fitsWith osakaCold 2300 ⟨(requires 10 : Prog C [] [])⟩ = true := rfl

/-- Increasing the reserve by one rejects that same body. -/
example : fitsWith ⟨50, 301⟩ 2300 ⟨(requires 10 : Prog C [] [])⟩ = false := rfl

/-- A rejected storage statement stays rejected even with a huge gas limit. -/
example {T : Ty} (l : Loc C [] T) (r : Src C [] T) :
    fitsWith osakaCold 1000000 ⟨(.cons (.assign l r) .nil : Prog C [] [])⟩ = false := rfl

/-- A rejected nested cost cannot be hidden by addition. -/
example (n : Nat) : addC (some n) none = none := rfl

/-- A rejected branch cannot be hidden by maximum. -/
example (n : Nat) : maxC (some n) none = none := rfl

/-- Empty value arguments have no cost. -/
example : argsCost (.nil : Args C [] []) = some 0 := rfl

/-- Empty revert data has no cost. -/
example : revListCost ([] : List (RevPart C [])) = some 0 := rfl

/-- Literal revert bytes use a word boundary, including the empty case. -/
example : revPartCost (.bytes [] : RevPart C []) = some 1 := rfl

/-- Word-size literal revert data crosses a cost boundary. -/
example : revPartCost (.bytes (List.replicate 32 0) : RevPart C []) = some 2 := rfl

/-- Returning no values is admitted independently of the contract. -/
example : retOk (CallRet.none : CallRet [] [] []) = true := rfl

/-- Wrapping exponentiation is rejected as checked exponentiation is. -/
example {p : PrimTy} (a b : Val C [] p) (h : BinOp.powW.accepts p = true)
    (hq : BinOp.powW.ret p = .uint) : valCost (.binop .powW h hq a b) = none := by
  simp only [valCost, or_true, if_true]

end Solidity.Stipend.MigrationControls
