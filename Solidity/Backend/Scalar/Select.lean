import Solidity.Backend.Scalar.SignedGuards
import Solidity.Backend.Scalar.Capacity
import Solidity.Backend.Scalar.Shifts
import Solidity.Backend.Scalar.SignedShift

/-! Selection uses the existing intrinsic operators and their accepted types.
Pure slices and checked slices expose different certificates. Division and
remainder use the separately proved universal observation contracts because
their failure classes differ; no new opcode or source operation IR is used. -/
namespace Solidity.Backend.Scalar

def selectUnary (op : UnOp) (p : PrimTy) (h : op.accepts p = true) :
    Option (UnaryCertificate op p h) :=
  match op, p with
  | .not, .bool => some booleanNot
  | .bnot, .uint => some uintNot
  | .toInt, .uint => some toInt
  | .toUint, .int => some toUint
  | _, _ => none

def selectBinary (op : BinOp) (p : PrimTy) (h : op.accepts p = true) :
    Option (BinaryCertificate op p h) :=
  match op, p with
  | .eqB, p => some (scalarEq p)
  | .neB, p => some (scalarNe p)
  | .and, .bool => some booleanAnd
  | .or, .bool => some booleanOr
  | .lt, .uint => some uintLt
  | .gt, .uint => some uintGt
  | .le, .uint => some uintLe
  | .ge, .uint => some uintGe
  | .lt, .int => some intLt
  | .gt, .int => some intGt
  | .le, .int => some intLe
  | .ge, .int => some intGe
  | .band, .uint => some uintAnd
  | .bor, .uint => some uintOr
  | .bxor, .uint => some uintXor
  | .band, .int => some intAnd
  | .bor, .int => some intOr
  | .bxor, .int => some intXor
  | .shl, .uint => some uintShl
  | .shr, .uint => some uintShr
  | .shr, .int => some intShr
  | .addW, .uint => some wrappingAdd
  | .subW, .uint => some wrappingSub
  | .mulW, .uint => some wrappingMul
  | .powW, .uint => some wrappingPow
  | _, _ => none

def selectChecked (op : BinOp) (p : PrimTy) (h : op.accepts p = true) :
    Option (CheckedCertificate op p h) :=
  match op, p with
  | .add, .uint => some checkedUintAdd
  | .sub, .uint => some checkedUintSub
  | .mul, .uint => some checkedUintMul
  | .pow, .uint => some checkedUintPow
  | .add, .int => some checkedIntAdd
  | .sub, .int => some checkedIntSub
  | .mul, .int => some checkedIntMul
  | _, _ => none

/-- Every accepted binary constructor has either a pure certificate, a checked
certificate, or one of the explicitly named universal division contracts. -/
theorem binary_selection_coverage (op : BinOp) (p : PrimTy) (h : op.accepts p = true) :
    (selectBinary op p h).isSome || (selectChecked op p h).isSome ||
      decide (op = .div ∨ op = .mod) = true := by
  cases op <;> cases p <;> first | rfl | cases h

structure CheckedUnaryCertificate (op : UnOp) (p : PrimTy) (h : op.accepts p = true) where
  test : Program
  body : Program
  correct : ∀ (a : p.Denote) (tail : Stack),
    guarded test body overflowFailure (encodeValue p a::tail) =
      some (checkedOutcome (op.ret p) (op.evalT h a) tail)

def checkedIntNeg : CheckedUnaryCertificate .neg .int rfl where
  test := negationTest
  body := negationBody
  correct := checked_negation_correct

def selectCheckedUnary (op : UnOp) (p : PrimTy) (h : op.accepts p = true) :
    Option (CheckedUnaryCertificate op p h) :=
  match op, p with
  | .neg, .int => some checkedIntNeg
  | _, _ => none

theorem unary_selection_coverage (op : UnOp) (p : PrimTy) (h : op.accepts p = true) :
    (selectUnary op p h).isSome || (selectCheckedUnary op p h).isSome = true := by
  cases op <;> cases p <;> first | rfl | cases h


structure ModularCertificate (op : ModOp) where
  test : Program
  body : Program
  correct : ∀ (a b k : PrimTy.uint.Denote) (tail : Stack),
    guarded test body divisionFailure
      (encodeValue .uint a::encodeValue .uint b::encodeValue .uint k::tail) =
      some (modularOutcome op a b k tail)

def selectModular : (op : ModOp) → ModularCertificate op
  | .addmod => ⟨zeroTest ⟨2, by decide⟩, modularBody .addmod, addmod_correct⟩
  | .mulmod => ⟨zeroTest ⟨2, by decide⟩, modularBody .mulmod, mulmod_correct⟩

#print axioms selectModular
#print axioms selectUnary
#print axioms selectBinary
#print axioms selectChecked
#print axioms selectCheckedUnary

#print axioms binary_selection_coverage
#print axioms unary_selection_coverage
#print axioms checkedIntNeg
end Solidity.Backend.Scalar
