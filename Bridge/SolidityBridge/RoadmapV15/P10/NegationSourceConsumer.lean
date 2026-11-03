import SolidityBridge.RoadmapV15.P10.NegationBody

/-! Typed source result for the fetched negation body. The intrinsic minimum
is classified separately; native checked guard/panic execution is not supplied. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem negation_source_range (a : PrimTy.int.Denote) (notMinimum : a ≠ Scalar.minimumInt) :
    PrimTy.int.inRange (-a.val) = true := by
  have bounds := Scalar.int_range a
  have different : a.val ≠ Scalar.minimumInt.val := by
    intro equal
    exact notMinimum (Subtype.ext equal)
  change a.val ≠ -((2^255 : Nat) : Int) at different
  simp only [PrimTy.inRange,decide_eq_true_eq]
  omega

def negationSourceResult (a : PrimTy.int.Denote) (notMinimum : a ≠ Scalar.minimumInt) :
    PrimTy.int.Denote := ⟨-a.val,negation_source_range a notMinimum⟩

theorem negation_source_value (a : PrimTy.int.Denote) (notMinimum : a ≠ Scalar.minimumInt) :
    UnOp.evalT .neg (p := .int) rfl a = some (negationSourceResult a notMinimum) := by
  simp only [UnOp.evalT,PrimTy.ofInt?,negation_source_range a notMinimum,dite_true,
    negationSourceResult]

/-- No source evaluation/run premise: the result is calculated from the typed operand. -/
theorem negation_source_execution (valid : Array UInt256) (seed : EVM.State)
    (before after : Backend.Program) (a : PrimTy.int.Denote) (tail : Scalar.Stack)
    (notMinimum : a ≠ Scalar.minimumInt)
    (fits : (Backend.encode (before ++ [Scalar.pushWord 0])).length < UInt256.size)
    (room : tail.length+2 ≤ 1024) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    UnOp.evalT .neg (p := .int) rfl a = some (negationSourceResult a notMinimum) ∧
    Assembly.driverSteps 2 (fuel+3) valid (negationBodyInput seed before after a tail) =
      .ok (negationBodyOutput seed before after a tail) ∧
    (negationBodyOutput seed before after a tail).stack =
      (Scalar.encodeValue .int (negationSourceResult a notMinimum)::tail).map
        (fun w => UInt256.mk w.toFin) ∧
    EVM.X (fuel+3) valid (negationBodyInput seed before after a tail) =
      EVM.X (fuel+1) valid (negationBodyOutput seed before after a tail) := by
  have execution := negation_body_execution valid seed before after a tail fits room gas fuel
  exact ⟨negation_source_value a notMinimum,execution.2.1,rfl,execution.2.2⟩

theorem negation_source_minimum :
    UnOp.evalT .neg (p := .int) rfl Scalar.minimumInt = none := by
  rfl

#print axioms negation_source_range
#print axioms negation_source_value
#print axioms negation_source_execution
#print axioms negation_source_minimum
end SolidityBridge.RoadmapV15.P10
