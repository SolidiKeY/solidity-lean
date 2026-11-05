import SolidityBridge.AccessBridge.AbiWordInterface
import SolidityBridge.AccessBridge.Calldata
import Solidity.Backend.AbiEntry.CalldataWord

/-! Exact existing native read and numeric validation against the indexed
semantic word decoder. This does not compose a fetched native validator or
replace entry span checks; raw zero padding remains observable. -/
namespace SolidityBridge.AccessBridge.AbiWord
open Solidity Solidity.Backend EvmYul

theorem semantic (native : EvmYul.State .EVM) (frame : Source.Fr) (offset : UInt256)
    (input : native.executionEnv.calldata.data.toList=frame.cd) :
    (EvmYul.State.calldataload native offset).toNat=Solidity.AbiEntry.load frame.cd offset.toNat :=
  (Calldata.payload native frame offset input).trans
    (Backend.AbiEntry.CalldataWord.load frame offset.toNat).symm

theorem word_nat (native : EvmYul.State .EVM) (frame : Source.Fr) (offset : UInt256)
    (input : native.executionEnv.calldata.data.toList=frame.cd) :
    (BitVec.ofNat 256 (EvmYul.State.calldataload native offset).toNat).toNat=
      Solidity.AbiEntry.load frame.cd offset.toNat := by
  change (EvmYul.State.calldataload native offset).toNat%2^256=_
  rw [semantic native frame offset input]
  apply Nat.mod_eq_of_lt
  rw [←Solidity.AbiEntry.W_eq]
  exact Solidity.AbiEntry.load_lt _ _

theorem validation (native : EvmYul.State .EVM) (frame : Source.Fr) (offset : UInt256)
    (input : native.executionEnv.calldata.data.toList=frame.cd)
    (kind : Solidity.AbiEntry.Kind) (tail : Scalar.Stack) :
    Scalar.run (Backend.AbiEntry.WordValidation.validator kind).code
      (BitVec.ofNat 256 (EvmYul.State.calldataload native offset).toNat::tail)=
      some (Scalar.flag (kind.valid (Solidity.AbiEntry.load frame.cd offset.toNat))::tail) := by
  have checked : Scalar.run (Backend.AbiEntry.WordValidation.validator kind).code
      (BitVec.ofNat 256 (EvmYul.State.calldataload native offset).toNat::tail)=
      some (Scalar.flag (kind.valid (BitVec.ofNat 256
        (EvmYul.State.calldataload native offset).toNat).toNat)::tail) :=
    (Backend.AbiEntry.WordValidation.validator kind).correct _ tail
  rw [word_nat native frame offset input] at checked
  exact checked

theorem rejected (native : EvmYul.State .EVM) (frame : Source.Fr) (offset : UInt256)
    (input : native.executionEnv.calldata.data.toList=frame.cd)
    (kind : Solidity.AbiEntry.Kind) (tail : Scalar.Stack) (fuel length free : Nat) :
    Solidity.AbiEntry.cval {data := frame.cd,free := free} (fuel+1) (.word kind) offset.toNat length=.error .revert ↔
      Scalar.run (Backend.AbiEntry.WordValidation.validator kind).code
        (BitVec.ofNat 256 (EvmYul.State.calldataload native offset).toNat::tail)=
        some (Scalar.flag false::tail) := by
  rw [validation native frame offset input]
  cases value : kind.valid (Solidity.AbiEntry.load frame.cd offset.toNat) <;>
    simp only [Solidity.AbiEntry.cval,value,Bool.false_eq_true,dite_false,
      dite_true,Scalar.flag,ite_true,ite_false,Option.some.injEq,List.cons.injEq,and_true,reduceCtorEq]
  all_goals decide

def certificate : AbiWordCertificate where
  toCalldataLoadCertificate := Calldata.certificate
  semantic := semantic
  validation := validation
  rejected := rejected

/-- info: 'SolidityBridge.AccessBridge.AbiWord.semantic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms semantic
/-- info: 'SolidityBridge.AccessBridge.AbiWord.word_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_nat
/-- info: 'SolidityBridge.AccessBridge.AbiWord.validation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms validation
/-- info: 'SolidityBridge.AccessBridge.AbiWord.rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejected
/-- info: 'SolidityBridge.AccessBridge.AbiWord.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end SolidityBridge.AccessBridge.AbiWord
