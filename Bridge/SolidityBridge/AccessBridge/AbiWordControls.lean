import SolidityBridge.AccessBridge.AbiWord

/-! Raw word controls with a real installed input, unaligned nonempty prefix,
ordered suffix, validators and actual fetched charge. Empty/large accesses
zero-pad; these are not claims that an entry span check accepts short input. -/
namespace SolidityBridge.AccessBridge.AbiWordControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
private def u (n : Nat) : UInt256 := .ofNat n
private def bytes : List UInt8 := [0xaa]++List.replicate 31 0++[5,0xbb]
private def frame : Source.Fr :=
  {this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨0,by decide⟩,
    static := false,contract := "Fixture",cd := bytes}
private def native : EvmYul.State .EVM := Calldata.installed default frame
private theorem input : native.executionEnv.calldata.data.toList=frame.cd := List.toList_toArray
private def tail : Scalar.Stack := [BitVec.ofNat 256 258,BitVec.ofNat 256 513]
private def word : Scalar.Word := BitVec.ofNat 256 (native.calldataload (u 1)).toNat

theorem unaligned : (native.calldataload (u 1)).toNat=5 := by
  rw [AbiWord.semantic native frame (u 1) input]
  rfl

private theorem loaded : Solidity.AbiEntry.load frame.cd 1=5 := by rfl
private theorem flags (kind : Solidity.AbiEntry.Kind) :
    Scalar.run (Backend.AbiEntry.WordValidation.validator kind).code (word::tail)=
      some (Scalar.flag (kind.valid 5)::tail) := by
  have actual : Scalar.run (Backend.AbiEntry.WordValidation.validator kind).code (word::tail)=
      some (Scalar.flag (kind.valid (Solidity.AbiEntry.load frame.cd (u 1).toNat))::tail) :=
    AbiWord.validation native frame (u 1) input kind tail
  have address : (u 1).toNat=1 := by rfl
  rw [address,loaded] at actual
  exact actual

theorem validator_cases :
    Scalar.run (Backend.AbiEntry.WordValidation.validator (.uint 8)).code (word::tail)=some (Scalar.flag true::tail) ∧
    Scalar.run (Backend.AbiEntry.WordValidation.validator .bool).code (word::tail)=some (Scalar.flag false::tail) ∧
    Scalar.run (Backend.AbiEntry.WordValidation.validator (.enumBelow 5)).code (word::tail)=some (Scalar.flag false::tail) ∧
    Scalar.run (Backend.AbiEntry.WordValidation.validator (.fixedBytes 1)).code (word::tail)=some (Scalar.flag false::tail) ∧
    Scalar.run (Backend.AbiEntry.WordValidation.validator (.uint 160)).code (word::tail)=some (Scalar.flag true::tail) :=
  ⟨flags (.uint 8),flags .bool,flags (.enumBelow 5),flags (.fixedBytes 1),flags (.uint 160)⟩

theorem bool_rejected (fuel length free : Nat) :
    Solidity.AbiEntry.cval {data := frame.cd,free := free} (fuel+1) (.word .bool) 1 length=.error .revert :=
  (AbiWord.rejected native frame (u 1) input .bool tail fuel length free).mpr validator_cases.2.1

theorem large_offset : (native.calldataload (u (2^64))).toNat=0 := by
  rw [AbiWord.semantic native frame _ input]
  rfl

private def emptyFrame : Source.Fr := {frame with cd := []}
private def emptyNative : EvmYul.State .EVM := Calldata.installed default emptyFrame
private def zero : Solidity.AbiEntry.Word .bool := ⟨0,by decide,by decide⟩
private theorem emptyLoad : Solidity.AbiEntry.load [] 0=0 := by decide

theorem empty_access (fuel length free : Nat) :
    (emptyNative.calldataload (u 0)).toNat=0 ∧
    Solidity.AbiEntry.cval {data := [],free := free} (fuel+1) (.word .bool) 0 length=.ok (.word zero) := by
  constructor
  · rw [AbiWord.semantic emptyNative emptyFrame _ List.toList_toArray]
    exact emptyLoad
  · simp only [Solidity.AbiEntry.cval,emptyLoad]
    rfl

theorem zero_fuel_not_revert (length free : Nat) :
    Solidity.AbiEntry.cval {data := frame.cd,free := free} 0 (.word .bool) 1 length≠.error .revert := by
  intro wrong
  change (.error .fuel : Except Solidity.AbiEntry.Fail (Solidity.AbiEntry.Val (.word .bool)))=.error .revert at wrong
  cases wrong

private def site : RoadmapV15.P10.Site .CALLDATALOAD where
  seed := {(default : EVM.State) with
    gasAvailable := u 3
    execLength := 41
    stack := [u 1,u 258,u 513]
    executionEnv := {(default : EVM.State).executionEnv with calldata := ⟨bytes.toArray⟩}}
  before := [.op .JUMPDEST]
  after := [.op .STOP]
  pcFits := by decide

theorem fetched : Assembly.driverSteps 1 2 #[] site.state=
    .ok {site.state with
      gasAvailable := u 0
      execLength := 42
      pc := u 2
      stack := site.state.toSharedState.toState.calldataload (u 1)::[u 258,u 513]} := by
  rw [Calldata.charged]
  rfl

theorem fetched_word : (site.state.toSharedState.toState.calldataload (u 1)).toNat=5 := by
  rw [AbiWord.semantic _ frame _ List.toList_toArray]
  rfl

/-- info: 'SolidityBridge.AccessBridge.AbiWordControls.unaligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unaligned
/-- info: 'SolidityBridge.AccessBridge.AbiWordControls.validator_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms validator_cases
/-- info: 'SolidityBridge.AccessBridge.AbiWordControls.bool_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bool_rejected
/-- info: 'SolidityBridge.AccessBridge.AbiWordControls.large_offset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms large_offset
/-- info: 'SolidityBridge.AccessBridge.AbiWordControls.empty_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_access
/-- info: 'SolidityBridge.AccessBridge.AbiWordControls.zero_fuel_not_revert' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms zero_fuel_not_revert
/-- info: 'SolidityBridge.AccessBridge.AbiWordControls.fetched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fetched
/-- info: 'SolidityBridge.AccessBridge.AbiWordControls.fetched_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fetched_word
end SolidityBridge.AccessBridge.AbiWordControls
