import Solidity.Lowering.V08.LiteralFailureOverflowReason
import Solidity.Backend.Scalar.Checked

/-! Source uint256 addition overflow consumes the actual checked scalar test.
The numeric slice and guarded boundary are not fetched EVM execution. -/
namespace Solidity.Lowering.V08.LiteralFailureScalarOverflow
open Solidity Source Backend

theorem source_bound (a : PrimTy.uint.Denote) :
 IntTy.u256.lo≤a.val ∧ a.val≤IntTy.u256.hi := by
 have bound := Scalar.uint_range a
 change 0≤a.val ∧ a.val≤((2^256-1 : Nat) : Int)
 omega

theorem failure_bytes : Scalar.overflowFailure=panicData .arithmetic := by decide +kernel

theorem range_false (a b : PrimTy.uint.Denote) (overflow : ((2^256 : Nat) : Int)≤a.val+b.val) :
 PrimTy.uint.inRange (a.val+b.val)=false := by
 apply Bool.eq_false_iff.mpr
 simp only [PrimTy.inRange,decide_eq_true_eq]
 intro within
 have bad : 0≤a.val+b.val ∧ a.val+b.val<((2^256 : Nat) : Int) := by
  exact of_decide_eq_true within
 omega

theorem target_failure (a b : PrimTy.uint.Denote) (tail : Scalar.Stack)
 (overflow : ((2^256 : Nat) : Int)≤a.val+b.val) :
 Scalar.guarded Scalar.checkedUintAdd.test Scalar.checkedUintAdd.body Scalar.overflowFailure
 (Scalar.encodeValue .uint a :: Scalar.encodeValue .uint b :: tail)=
 some (.error (panicData .arithmetic)) := by
 have result := Scalar.checkedUintAdd.correct a b tail
 simpa only [Solidity.BinOp.evalT,Solidity.BinOp.evalNum,Solidity.BinOp.arithInt,
  Option.bind_some,PrimTy.ofInt?,range_false a b overflow,Bool.false_eq_true,dite_false,
  Scalar.checkedOutcome,Option.elim_none,failure_bytes] using result

/-- The actual numeric test retains both encoded operands below its flag. -/
theorem test_flag (a b : PrimTy.uint.Denote) (tail : Scalar.Stack)
 (overflow : ((2^256 : Nat) : Int)≤a.val+b.val) :
 Scalar.run Scalar.unsignedAddTest (Scalar.encodeValue .uint a :: Scalar.encodeValue .uint b :: tail)=
 some (Scalar.flag true :: Scalar.encodeValue .uint a :: Scalar.encodeValue .uint b :: tail) := by
 simpa only [range_false a b overflow,Bool.not_false] using Scalar.unsignedAddTest_typed a b tail

/-- The raw arithmetic body wraps; Solidity failure comes from the checked test. -/
theorem raw_body (a b : PrimTy.uint.Denote) (tail : Scalar.Stack) :
 Scalar.run Scalar.checkedUintAdd.body (Scalar.encodeValue .uint a :: Scalar.encodeValue .uint b :: tail)=
 some (BitVec.ofInt 256 (a.val+b.val) :: tail) := by
 change some ((BitVec.ofInt 256 a.val + BitVec.ofInt 256 b.val) :: tail)=_
 rw [← BitVec.ofInt_add]

/-- Actual source operands and actual scalar guard share the same failure bytes.
No local-read lowering, joint memory/frame relation or payload emission is assumed. -/
theorem agreement {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 (a b : PrimTy.uint.Denote) (older : Locals E.layout Γ) (state : St E)
 (tail : Scalar.Stack) (overflow : ((2^256 : Nat) : Int)≤a.val+b.val) :
 (evalE G {F with checked:=true} (n+5) (LiteralFailureOverflowReason.addition IntTy.u256)).run
 (LiteralFailureOverflowReason.caller IntTy.u256 a.val b.val (source_bound a) (source_bound b) older,state)=
 (.error (.revert (panicData .arithmetic)),
 (LiteralFailureOverflowReason.caller IntTy.u256 a.val b.val (source_bound a) (source_bound b) older,state)) ∧
 Scalar.guarded Scalar.checkedUintAdd.test Scalar.checkedUintAdd.body Scalar.overflowFailure
 (Scalar.encodeValue .uint a :: Scalar.encodeValue .uint b :: tail)=
 some (.error (panicData .arithmetic)) := by
 refine ⟨LiteralFailureOverflowReason.checked_overflow G F n IntTy.u256 a.val b.val
  (source_bound a) (source_bound b) ?_ older state,target_failure a b tail overflow⟩
 change ¬(0≤a.val+b.val ∧ a.val+b.val≤((2^256-1 : Nat) : Int))
 omega
end Solidity.Lowering.V08.LiteralFailureScalarOverflow
