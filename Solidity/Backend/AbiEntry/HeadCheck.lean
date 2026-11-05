import Solidity.Backend.Selection.InterfaceV2
import Solidity.Backend.AbiEntry.HeadCheckInterface
import Solidity.Backend.AbiEntry.WordValidation

/-! Actual short-head predicate in the existing numeric bytecode slice.
Unbounded semantic head extents are not truncated into a PUSH immediate.
Native size loading, conditional revert execution and full decoding are open. -/
namespace Solidity.Backend.AbiEntry.HeadCheck
open Scalar

def need (parameters : List Solidity.AbiEntry.Param) : Nat :=
  4+Solidity.AbiEntry.headsOf parameters

def code (parameters : List Solidity.AbiEntry.Param) : Program :=
  WordValidation.belowCode (need parameters)

theorem correct (parameters : List Solidity.AbiEntry.Param) (size : Scalar.Word) (tail : Stack) :
    run (code parameters) (size::tail)=
      some (flag (decide (size.toNat<need parameters))::tail) :=
  WordValidation.below_correct _ size tail

theorem capacity (parameters : List Solidity.AbiEntry.Param) (tail : Stack)
    (room : tail.length+2≤1024) :
    stackBound (code parameters) ((tail.length+1 : Nat) : Int)=true :=
  WordValidation.below_capacity _ tail room

theorem classified (input : Solidity.AbiEntry.Input) (parameters : List Solidity.AbiEntry.Param)
    (size : Scalar.Word) (tail : Stack) (same : size.toNat=input.size) :
    run (code parameters) (size::tail)=
      some (flag (decide (input.size<need parameters))::tail) := by
  rw [correct,same]

theorem early_revert (input : Solidity.AbiEntry.Input) (fuel : Nat)
    (parameters : List Solidity.AbiEntry.Param) (short : input.size<need parameters) :
    Solidity.AbiEntry.entry input fuel parameters=.error .revert := by
  simp only [need] at short
  simp only [Solidity.AbiEntry.entry,if_pos short]

def frameCertificate (parameters : List Solidity.AbiEntry.Param) (size : Scalar.Word) :
    Selection.V2.FrameCertificate [size] [flag (decide (size.toNat<need parameters))] where
  code := code parameters
  peak := 1
  inputRoom := by change (1 : Nat)+1≤1024;decide
  frame := correct parameters size
  capacity := by
    intro tail room
    simp only [List.cons_append,List.nil_append,List.length_cons] at room ⊢
    exact capacity parameters tail room

def certificate : Interface.HeadCheckCertificate code where
  correct := correct
  capacity := capacity
  classified := classified
  early_revert := early_revert

/-- info: 'Solidity.Backend.AbiEntry.HeadCheck.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms correct
/-- info: 'Solidity.Backend.AbiEntry.HeadCheck.capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capacity
/-- info: 'Solidity.Backend.AbiEntry.HeadCheck.classified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms classified
/-- info: 'Solidity.Backend.AbiEntry.HeadCheck.early_revert' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms early_revert
/-- info: 'Solidity.Backend.AbiEntry.HeadCheck.frameCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frameCertificate
/-- info: 'Solidity.Backend.AbiEntry.HeadCheck.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.HeadCheck
