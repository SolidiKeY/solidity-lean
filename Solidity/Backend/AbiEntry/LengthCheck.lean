import Solidity.Backend.Selection.InterfaceV2
import Solidity.Backend.AbiEntry.LengthCheckInterface
import Solidity.Backend.AbiEntry.WordValidation

/-! Dynamic length admission reuses the existing numeric compiler. Eager
memory decoding and lazy calldata references retain distinct failure classes. -/
namespace Solidity.Backend.AbiEntry.LengthCheck
open Scalar

def code : Program := WordValidation.belowCode (Solidity.AbiEntry.lim+1)

theorem correct (length : Scalar.Word) (suffix : Stack) :
    run code (length::suffix)=
      some (flag (decide (length.toNat≤Solidity.AbiEntry.lim))::suffix) := by
  simp only [code,WordValidation.below_correct,Nat.lt_succ_iff]

theorem capacity (suffix : Stack) (room : suffix.length+2≤1024) :
    stackBound code ((suffix.length+1 : Nat) : Int)=true :=
  WordValidation.below_capacity _ suffix room

theorem lazy_revert (input : Solidity.AbiEntry.Input) (shape : Solidity.AbiEntry.Shape)
    (base pointer : Nat)
    (tail : Solidity.AbiEntry.tailFits input.size base
      (Solidity.AbiEntry.load input.data pointer) shape.tailSize=true)
    (prefixed : shape.lengthPrefixed=true)
    (oversized : Solidity.AbiEntry.lim<Solidity.AbiEntry.load input.data
      (Solidity.AbiEntry.wrap (base+Solidity.AbiEntry.load input.data pointer))) :
    Solidity.AbiEntry.tailRef input shape base pointer=.error .revert := by
  simp only [Solidity.AbiEntry.tailRef,tail,prefixed,if_true,if_pos oversized]

theorem eager_bytes_panic (input : Solidity.AbiEntry.Input) (fuel pointer allocated : Nat)
    (head : pointer+31<input.size)
    (oversized : Solidity.AbiEntry.lim<Solidity.AbiEntry.load input.data pointer) :
    Solidity.AbiEntry.mdec input (fuel+1) .bytes pointer allocated=.error .panic := by
  simp only [Solidity.AbiEntry.mdec,if_pos head,if_pos oversized]

theorem eager_array_panic (input : Solidity.AbiEntry.Input) (element : Solidity.AbiEntry.Shape)
    (fuel pointer allocated : Nat) (head : pointer+31<input.size)
    (oversized : Solidity.AbiEntry.lim<Solidity.AbiEntry.load input.data pointer) :
    Solidity.AbiEntry.mdec input (fuel+1) (.array element) pointer allocated=.error .panic := by
  simp only [Solidity.AbiEntry.mdec,if_pos head,if_pos oversized]

def frameCertificate (length : Scalar.Word) : Selection.V2.FrameCertificate [length]
    [flag (decide (length.toNat≤Solidity.AbiEntry.lim))] where
  code := code
  peak := 1
  inputRoom := by change (1 : Nat)+1≤1024;decide
  frame := correct length
  capacity := by
    intro suffix room
    simp only [List.cons_append,List.nil_append,List.length_cons] at room ⊢
    exact capacity suffix room

def certificate : Interface.LengthCheckCertificate code where
  correct := correct
  capacity := capacity
  lazy_revert := lazy_revert

/-- info: 'Solidity.Backend.AbiEntry.LengthCheck.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms correct
/-- info: 'Solidity.Backend.AbiEntry.LengthCheck.capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capacity
/-- info: 'Solidity.Backend.AbiEntry.LengthCheck.lazy_revert' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms lazy_revert
/-- info: 'Solidity.Backend.AbiEntry.LengthCheck.eager_bytes_panic' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms eager_bytes_panic
/-- info: 'Solidity.Backend.AbiEntry.LengthCheck.eager_array_panic' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms eager_array_panic
/-- info: 'Solidity.Backend.AbiEntry.LengthCheck.frameCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frameCertificate
/-- info: 'Solidity.Backend.AbiEntry.LengthCheck.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.LengthCheck
