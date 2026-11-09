import Solidity.Source.PowerV2Correct
import Solidity.Lowering.V07.Scalar
import Solidity.Semantics.Run

/-!
# Explicit V2 power operator consumer

Consumes the H263/H57 operator pair published at
136a2531d04f5b2a431258d1b83fa2792ee27b31. It relates the named V2 operation
to the existing intrinsic word operation and actual value AST evaluation.
The exponent word is the existing target operand type, not a restriction on
Source isAmount or the owner's unrestricted Nat API. Operand observations are
local inputs which a statement association must derive, not certificates of
whole execution. Narrow/sign casts and general Source amount association remain.

The live Source evaluator/shiftVal remain V1. This module changes neither that
evaluator nor its checked-callee, panic/journal, pipeline or resource obligations.
It is not H250 endpoint migration, PassCorrect, or full H263 production acceptance.
The frozen V1 cutoff controls remain in PowerBoundControls.
-/
namespace Solidity.Correctness.Lowering.Unchecked.PowerV2Arithmetic

open Solidity.Lowering.V07

/-- Arithmetic residue agrees with the repaired helper at an actual word
exponent. No independent exponent bound or successful-result premise is added. -/
theorem word_powW (base : Int) (exponent : PrimTy.uint.Denote) :
    BinOp.arithInt .powW base exponent.val =
      some (Source.PowerV2.powMod base exponent.val.toNat (2 ^ 256) %
        Semantics.uintBound) := by
  have range := exponent.property
  simp only [PrimTy.inRange, decide_eq_true_eq] at range
  rw [BinOp.arithInt, if_neg (by omega : ¬ exponent.val < 0)]
  exact congrArg some (Source.PowerV2.powMod_residue base exponent.val.toNat (2 ^ 256)).symm

private theorem word_eval (base exponent : PrimTy.uint.Denote) :
    BinOp.evalT .powW rfl base exponent =
      some (integerValue Source.IntTy.u256
        (Source.IntTy.u256.wrap (base.val ^ exponent.val.toNat))
        (Source.IntTy.u256.wrap_mem _)) := by
  have range := exponent.property
  simp only [PrimTy.inRange, decide_eq_true_eq] at range
  have hr := integer_range Source.IntTy.u256
    (Source.IntTy.u256.wrap (base.val ^ exponent.val.toNat))
    (Source.IntTy.u256.wrap_mem _)
  change PrimTy.uint.inRange ((base.val ^ exponent.val.toNat) % Semantics.uintBound) = true at hr
  change (BinOp.arithInt .powW base.val exponent.val).bind PrimTy.uint.ofInt? = some ⟨_, hr⟩
  simp only [BinOp.arithInt, if_neg (by omega : ¬ exponent.val < 0),
    Option.bind_some, PrimTy.ofInt?, dif_pos hr]

/-- A shared typed-value ingredient using the repaired implementation. The
actual supplied intrinsic powW AST evaluates to a value related to V2 Source
power. This does not associate a raw producer output or a Source evaluator. -/
theorem value_power {D : Source.Layout} {C : Contract} {Γ : Ctx}
    (target : State C Γ) (base exponent : Val C Γ .uint)
    (x y : PrimTy.uint.Denote)
    (left : base.evalT target = .ok x) (right : exponent.evalT target = .ok y) :
    ∃ (sourceResult : Source.Val D (.int Source.IntTy.u256))
      (modelResult : PrimTy.uint.Denote),
      Source.PowerV2.intPow Source.IntTy.u256 false x.val y.val.toNat = .ok sourceResult ∧
      (Val.binop .powW rfl rfl base exponent).evalT target = .ok modelResult ∧
      IntValueRel Source.IntTy.u256 sourceResult modelResult := by
  refine ⟨Source.intWrap Source.IntTy.u256 (x.val ^ y.val.toNat),
    integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap (x.val ^ y.val.toNat))
      (Source.IntTy.u256.wrap_mem _),
    Source.PowerV2.intPow_unchecked Source.IntTy.u256 x.val y.val.toNat,
    ?_, integer_related _ _ _⟩
  rw [Val.evalT, left]
  change (do let b ← exponent.evalT target; TRes.ofOpt (BinOp.evalT .powW rfl x b)) = _
  rw [right]
  change TRes.ofOpt (BinOp.evalT .powW rfl x y) = _
  rw [word_eval]
  rfl

#print axioms word_powW
#print axioms value_power

end Solidity.Correctness.Lowering.Unchecked.PowerV2Arithmetic
