import SolidityBridge.AccessBridge.HeadSizeInterface

/-! Reuse the published fetched charged CALLDATASIZE theorem, then consume
its actual result in the existing numeric head-check compiler. These remain
two execution layers; fetched native conditional branching is not proved. -/
namespace SolidityBridge.AccessBridge.HeadSize
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem size_word (length : Nat) :
    (BitVec.ofNat 256 (UInt256.ofNat length).toNat).toNat=length%2^256 := by
  change (length%2^256)%2^256=length%2^256
  exact Nat.mod_mod length _

theorem checked {D : Source.Layout} (site : RoadmapV15.P10.Site .CALLDATASIZE)
    (input : Source.Calldata D) (fuel : Nat)
    (gas : 2≤site.seed.gasAvailable.toNat) (room : site.seed.stack.length+1≤1024)
    (parameters : List Solidity.AbiEntry.Param) (suffix : Scalar.Stack) :
    let start := (RoadmapV15.P10.calldataSite site input).state
    let next := (Assembly.chargedPrepare start 2).replaceStackAndIncrPC
      (UInt256.ofNat input.input.length::start.stack)
    Assembly.driverSteps 1 (fuel+2) #[] start=.ok next ∧
    EVM.X (fuel+2) #[] start=EVM.X (fuel+1) #[] next ∧
    Scalar.run (Backend.AbiEntry.HeadCheck.code parameters)
      (BitVec.ofNat 256 (UInt256.ofNat input.input.length).toNat::suffix)=
      some (Scalar.flag (decide (input.input.length%2^256<Backend.AbiEntry.HeadCheck.need parameters))::suffix) := by
  have execution := RoadmapV15.P10.calldatasize_source_input site input fuel gas room
  refine ⟨execution.1,execution.2,?_⟩
  rw [Backend.AbiEntry.HeadCheck.correct,size_word]

theorem classified {D : Source.Layout} (input : Source.Calldata D)
    (fits : input.input.length<2^256) (parameters : List Solidity.AbiEntry.Param)
    (suffix : Scalar.Stack) :
    Scalar.run (Backend.AbiEntry.HeadCheck.code parameters)
      (BitVec.ofNat 256 (UInt256.ofNat input.input.length).toNat::suffix)=
      some (Scalar.flag (decide (input.input.length<Backend.AbiEntry.HeadCheck.need parameters))::suffix) := by
  rw [Backend.AbiEntry.HeadCheck.correct,size_word,Nat.mod_eq_of_lt fits]

theorem early_revert {D : Source.Layout} (input : Source.Calldata D)
    (parameters : List Solidity.AbiEntry.Param) (free fuel : Nat)
    (short : input.input.length<Backend.AbiEntry.HeadCheck.need parameters) :
    Solidity.AbiEntry.entry {data := input.input,free := free} fuel parameters=.error .revert :=
  Backend.AbiEntry.HeadCheck.early_revert _ fuel parameters short

def certificate : HeadSizeCertificate where
  checked := checked

/-- info: 'SolidityBridge.AccessBridge.HeadSize.size_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms size_word
/-- info: 'SolidityBridge.AccessBridge.HeadSize.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked
/-- info: 'SolidityBridge.AccessBridge.HeadSize.classified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms classified
/-- info: 'SolidityBridge.AccessBridge.HeadSize.early_revert' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms early_revert
/-- info: 'SolidityBridge.AccessBridge.HeadSize.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end SolidityBridge.AccessBridge.HeadSize
