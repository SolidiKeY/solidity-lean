import SolidityBridge.AccessBridge.HeadSize

/-! Inhabited native extent and numeric/semantic boundary controls. The wrap
control is a numeric extent counterexample, not an allocated huge input. -/
namespace SolidityBridge.AccessBridge.HeadSizeControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
private def layout : Source.Layout := ⟨fun _ => [],fun _ => 0,fun _ => .bool⟩
private def input : Source.Calldata layout :=
  {input := [0x11,0x22,0x33],objects := fun _ => none}
private def spill : List UInt256 := [UInt256.ofNat 258,UInt256.ofNat 513]
private def site : RoadmapV15.P10.Site .CALLDATASIZE :=
  ⟨{(default : EVM.State) with
    gasAvailable := UInt256.ofNat 9,stack := spill
    memory := ⟨#[0xaa,0xbb]⟩},[],[.op .STOP],by decide⟩
private def start : EVM.State := (RoadmapV15.P10.calldataSite site input).state
private def next : EVM.State := (Assembly.chargedPrepare start 2).replaceStackAndIncrPC
  (UInt256.ofNat input.input.length::start.stack)

theorem native_and_predicate :
    Assembly.driverSteps 1 2 #[] start=.ok next ∧
    EVM.X 2 #[] start=EVM.X 1 #[] next ∧
    Scalar.run (Backend.AbiEntry.HeadCheck.code [])
      (BitVec.ofNat 256 (UInt256.ofNat input.input.length).toNat::[258,513])=
      some (Scalar.flag true::[258,513]) :=
  HeadSize.checked site input 0 (by decide) (by decide) [] [258,513]

theorem protected_and_charged : next.memory=start.memory ∧
    next.stack=UInt256.ofNat 3::spill ∧ next.gasAvailable.toNat=7 ∧
    next.activeWords=start.activeWords ∧ next.pc.toNat=start.pc.toNat+1 := by decide

theorem semantic_short (fuel free : Nat) :
    Solidity.AbiEntry.entry {data := input.input,free := free} fuel []=.error .revert :=
  HeadSize.early_revert input [] free fuel (by decide)

theorem boundaries :
    Scalar.run (Backend.AbiEntry.HeadCheck.code [])
      (BitVec.ofNat 256 (UInt256.ofNat 0).toNat::[258,513])=some (1::[258,513]) ∧
    Scalar.run (Backend.AbiEntry.HeadCheck.code [])
      (BitVec.ofNat 256 (UInt256.ofNat 4).toNat::[258,513])=some (0::[258,513]) := by decide

theorem representability_matters :
    (BitVec.ofNat 256 (UInt256.ofNat (2^256)).toNat).toNat=0 ∧
    Scalar.run (Backend.AbiEntry.HeadCheck.code [])
      (BitVec.ofNat 256 (UInt256.ofNat (2^256)).toNat::[258,513])=some (1::[258,513]) ∧
    ¬(2^256 : Nat)<Backend.AbiEntry.HeadCheck.need [] := by decide

/-- info: 'SolidityBridge.AccessBridge.HeadSizeControls.native_and_predicate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms native_and_predicate
/-- info: 'SolidityBridge.AccessBridge.HeadSizeControls.protected_and_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_charged
/-- info: 'SolidityBridge.AccessBridge.HeadSizeControls.semantic_short' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms semantic_short
/-- info: 'SolidityBridge.AccessBridge.HeadSizeControls.boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundaries
/-- info: 'SolidityBridge.AccessBridge.HeadSizeControls.representability_matters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms representability_matters
end SolidityBridge.AccessBridge.HeadSizeControls
