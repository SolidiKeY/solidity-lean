import Solidity.Backend.AbiEntry.TailGuardInterface
import Solidity.Backend.AbiEntry.OffsetChecks
import Solidity.Backend.AbiEntry.LengthCheck

/-! Compose existing emitted checks in the same numeric execution framework.
Every failed predicate has the same lazy-reference revert class; evaluating
these pure numeric predicates together does not certify native load ordering. -/
namespace Solidity.Backend.AbiEntry.TailGuard
open Scalar
private def rotate : Program := [.op (.SWAP 3),.op (.SWAP 2),.op (.SWAP 1),.op (.SWAP 0)]
private def duplicate : Program := [.op (.DUP 0)]
private def finish : Program := [.op .AND,.op .AND]

def code : Program := OffsetChecks.tailCode++rotate++duplicate++LengthCheck.code++
  rotate++OffsetChecks.regionCode++finish

private theorem rotate_run (a b c d e : Scalar.Word) (suffix : Stack) :
    run rotate (a::b::c::d::e::suffix)=some (b::c::d::e::a::suffix) := by
  simp only [rotate,run,step,swap,exchange,Option.map_some,Option.bind_some]

private theorem duplicate_run (a : Scalar.Word) (suffix : Stack) :
    run duplicate (a::suffix)=some (a::a::suffix) := rfl

private theorem finish_run (tail length region : Bool) (suffix : Stack) :
    run finish (flag region::flag length::flag tail::suffix)=
      some (flag (tail && length && region)::suffix) := by
  cases tail <;> cases length <;> cases region <;> rfl

theorem correct (size base relative extent length stride address : Scalar.Word) (suffix : Stack) :
    run code (extent::size::base::relative::length::stride::size::address::suffix)=
      some (flag (Solidity.AbiEntry.tailFits size.toNat base.toNat relative.toNat extent.toNat &&
        decide (length.toNat≤Solidity.AbiEntry.lim) &&
        Solidity.AbiEntry.regionFits size.toNat address.toNat length.toNat stride.toNat)::suffix) := by
  simp only [code,run_append,OffsetChecks.tail_correct,rotate_run,duplicate_run,
    LengthCheck.correct,OffsetChecks.region_correct,finish_run,Option.bind_some]

theorem capacity (suffix : Stack) (room : suffix.length+9≤1024) :
    stackBound code ((suffix.length+8 : Nat) : Int)=true := by
  simp only [code,OffsetChecks.tailCode,OffsetChecks.regionCode,LengthCheck.code,
    WordValidation.belowCode,if_pos (by decide : Solidity.AbiEntry.lim+1<2^256),
    rotate,duplicate,finish,
    List.cons_append,List.nil_append]
  simp only [stackBound,heightTrace,stackDelta,pushWord,pushByte,numericDelta,
    unary,binary,Option.isSome_some,Option.isSome_none,ite_true,ite_false,Bool.false_eq_true,
    List.all_cons,List.all_nil,Bool.and_true,safeHeight,Bool.and_eq_true,decide_eq_true_eq]
  omega

/-- Exact lazy-reference result once runtime operands represent the actual
input. These are initial representation facts, not a successful decode premise. -/
theorem reference (input : Solidity.AbiEntry.Input) (shape : Solidity.AbiEntry.Shape)
    (pointer : Nat) (size base relative extent length stride address : Scalar.Word)
    (sizeSame : size.toNat=input.size) (relativeSame : relative.toNat=Solidity.AbiEntry.load input.data pointer)
    (extentSame : extent.toNat=shape.tailSize) (strideSame : stride.toNat=shape.stride)
    (addressSame : address.toNat=Solidity.AbiEntry.wrap (base.toNat+relative.toNat))
    (lengthSame : length.toNat=Solidity.AbiEntry.load input.data address.toNat)
    (prefixed : shape.lengthPrefixed=true) :
    Solidity.AbiEntry.tailRef input shape base.toNat pointer=
      if (Solidity.AbiEntry.tailFits size.toNat base.toNat relative.toNat extent.toNat &&
        decide (length.toNat≤Solidity.AbiEntry.lim) &&
        Solidity.AbiEntry.regionFits size.toNat address.toNat length.toNat stride.toNat)=true
      then .ok (Solidity.AbiEntry.wrap (address.toNat+32),length.toNat) else .error .revert := by
  simp only [Solidity.AbiEntry.tailRef,←relativeSame,←sizeSame,←extentSame,
    prefixed,if_true,←addressSame,←lengthSame,←strideSame]
  by_cases small : length.toNat≤Solidity.AbiEntry.lim
  · have notLarge : ¬Solidity.AbiEntry.lim<length.toNat := Nat.not_lt.mpr small
    cases tail : Solidity.AbiEntry.tailFits size.toNat base.toNat relative.toNat extent.toNat <;>
      cases region : Solidity.AbiEntry.regionFits size.toNat address.toNat length.toNat stride.toNat <;>
      simp only [if_neg notLarge,decide_eq_true small,Bool.and_true,Bool.and_false,if_true,if_false,Bool.false_eq_true]
  · have large : Solidity.AbiEntry.lim<length.toNat := Nat.lt_of_not_ge small
    cases tail : Solidity.AbiEntry.tailFits size.toNat base.toNat relative.toNat extent.toNat <;>
      cases region : Solidity.AbiEntry.regionFits size.toNat address.toNat length.toNat stride.toNat <;>
      simp only [if_pos large,decide_eq_false small,Bool.and_true,Bool.and_false,if_true,if_false,Bool.false_eq_true]

def frameCertificate (size base relative extent length stride address : Scalar.Word) :
    Selection.V2.FrameCertificate [extent,size,base,relative,length,stride,size,address]
      [flag (Solidity.AbiEntry.tailFits size.toNat base.toNat relative.toNat extent.toNat &&
        decide (length.toNat≤Solidity.AbiEntry.lim) &&
        Solidity.AbiEntry.regionFits size.toNat address.toNat length.toNat stride.toNat)] where
  code := code
  peak := 1
  inputRoom := by change (8 : Nat)+1≤1024;decide
  frame := correct size base relative extent length stride address
  capacity := by
    intro suffix room
    simp only [List.cons_append,List.nil_append,List.length_cons] at room ⊢
    exact capacity suffix room

def certificate : Interface.TailGuardCertificate code where
  correct := correct
  capacity := capacity

/-- info: 'Solidity.Backend.AbiEntry.TailGuard.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms correct
/-- info: 'Solidity.Backend.AbiEntry.TailGuard.reference' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms reference
/-- info: 'Solidity.Backend.AbiEntry.TailGuard.capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capacity
/-- info: 'Solidity.Backend.AbiEntry.TailGuard.frameCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frameCertificate
/-- info: 'Solidity.Backend.AbiEntry.TailGuard.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.TailGuard
