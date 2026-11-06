import Solidity.Calculus.DecisionNumericTwoPrefixFormula
import Solidity.Examples.DecisionNumericTwoPrefix

/-! # Non-reflexive two-prefix equality producer client
A term using both actual inputs is compared with a distinct literal. The broad
source-producer theorem is separate from these finite coverage/verdict controls.
-/
namespace Solidity.Examples.DecisionNumericTwoPrefixFormula
open Solidity.Decide Solidity.Examples.Decision
open Solidity.Examples.DecisionNumericTwoPrefix (input positive)
set_option Elab.async false

def right (C : Contract) : Tm C [.val .uint, .val .uint] (.val .uint) :=
  .app0 (.lit (uintOfNat 5))
def body (C : Contract) : Fml C [.val .uint, .val .uint] :=
  .eq (input C).val (right C)

/-- The producer is inhabited by two different arithmetic operands, for any contract. -/
theorem source_client (C : Contract) :
    ∃ ψ : LFml C,
      (body C).toLS true (((SymS.init (C := C)).pushQ .uint).pushQ .uint) = some ψ ∧
      (body C).toLS false (((SymS.init (C := C)).pushQ .uint).pushQ .uint) = some ψ ∧
      ψ.UIntQF (fun q => q = ⟨.uint, 0⟩ ∨ q = ⟨.uint, 1⟩) (fun _ => False) ∧
      ψ.elim = ψ ∧ ψ.condSimp = ψ ∧
      ψ.nodes ≤ 7 * ((input C).val.size + (right C).size) + 13 :=
  uintTwoPrefix_eq_sourceBound (input C).property (.lit (uintOfNat 5))

def forallEqualsFive : Fml Gaps [] :=
  .all (.user "x") .uint (.all (.user "y") .uint (body Gaps))

/-- The separate concrete leaf lies in the frozen target and coverage tests. -/
theorem concrete_classification :
    forallEqualsFive.inTarget {} = true ∧ forallEqualsFive.Covered = true := by
  decide +kernel

/-- info: [some 5, some 5] -/
#guard_msgs in
#eval [((body Gaps).toLS true (((SymS.init (C := Gaps)).pushQ .uint).pushQ .uint)).map LFml.nodes,
       ((body Gaps).toLS false (((SymS.init (C := Gaps)).pushQ .uint).pushQ .uint)).map LFml.nodes]

/-- info: ["proved", "refuted", "unknown"] -/
#guard_msgs in
#eval [verdict positive, verdict forallEqualsFive, verdict gapHashNegForall]

end Solidity.Examples.DecisionNumericTwoPrefixFormula
