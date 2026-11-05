import SolidityBridge.AccessBridge.Interface
import SolidityBridge.ExternalEvm.PaddingInterface

/-! Actual CALLDATALOAD payload and charged execution over the existing pinned
state/driver, reusing its decoder, byte readers and H7 padding. No replacement
evaluator, ABI decoder or Source/world adequacy is introduced. -/
namespace SolidityBridge.AccessBridge.Calldata
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open SolidityBridge.RoadmapV15

/-- The actual pinned reader's clipped segment and bounded zero padding are
exactly the owner's fitBytes operation. No bound is imposed on the offset or
source buffer; only the requested byte count must fit the host padding width. -/
theorem readBytes_source (source : ByteArray) (offset width : Nat)
    (host : width < USize.size) :
    (source.readBytes offset width).data.toList =
      Source.fitBytes width (source.data.toList.drop offset) := by
  let segment : ByteArray := if offset < 2^64 && width < 2^64 then
    source.copySlice offset .empty 0 width else
    ⟨⟨source.toList.drop offset |>.take width⟩⟩
  have raw : segment.data.toList = (source.data.toList.drop offset).take width := by
    dsimp only [segment]
    split
    · simp only [ByteArray.copySlice, ByteArray.empty, ByteArray.emptyWithCapacity,
        Array.extract_empty, Array.empty_append, Array.append_empty,
        Array.toList_extract, List.extract, Nat.add_sub_cancel_left]
    · simp only [Memory.bytes_list]
  have length : segment.size = min width (source.data.toList.drop offset).length := by
    change segment.data.size = _
    rw [← Array.length_toList, raw, List.length_take]
  have limited : segment.size ≤ width := by
    rw [length]
    exact Nat.min_le_left _ _
  have padding := Memory.zeroes_difference width segment.size host limited
  change (segment ++ ffi.ByteArray.zeroes
    (⟨(width : BitVec System.Platform.numBits) -
      (segment.size : BitVec System.Platform.numBits)⟩ : USize)).data.toList = _
  rw [padding, ByteArray.data_append, Array.toList_append]
  simp only [Array.toList_replicate, raw]
  have difference : width - segment.size = width - (source.data.toList.drop offset).length := by
    rw [length]
    omega
  rw [difference]
  simp only [Source.fitBytes, List.take_append, List.take_replicate,
    Nat.min_eq_left (Nat.sub_le width _)]

theorem payload (native : EvmYul.State .EVM) (frame : Source.Fr) (offset : UInt256)
    (input : native.executionEnv.calldata.data.toList = frame.cd) :
    (EvmYul.State.calldataload native offset).toNat = Source.cdWordAt frame offset.toNat := by
  have host : 32 < USize.size := by
    rcases USize.size_eq with bits | bits <;> rw [bits] <;> decide
  change EvmYul.fromBytesBigEndian
    ((native.executionEnv.calldata.readBytes offset.toNat 32).data.toList) % UInt256.size = _
  rw [reference_big_reader, readBytes_source _ _ _ host, input]
  have bounded : ofBytesBE (Source.fitBytes 32 (frame.cd.drop offset.toNat)) < UInt256.size := by
    have bytes := bytes_value_bound (Source.fitBytes 32 (frame.cd.drop offset.toNat))
    simpa only [Source.fitBytes_length] using bytes
  rw [Nat.mod_eq_of_lt bounded]
  rfl

/-- Install exactly the source bytes in the existing native state. -/
def installed (native : EvmYul.State .EVM) (frame : Source.Fr) : EvmYul.State .EVM :=
  {native with executionEnv := {native.executionEnv with calldata := ⟨frame.cd.toArray⟩}}

theorem installed_payload (native : EvmYul.State .EVM) (frame : Source.Fr) (offset : UInt256) :
    (EvmYul.State.calldataload (installed native frame) offset).toNat =
      Source.cdWordAt frame offset.toNat :=
  payload _ frame offset List.toList_toArray

theorem budget_zero (site : P10.Site .CALLDATALOAD) (valid : Array UInt256) :
    Assembly.driverSteps 1 0 valid site.state = .error .OutOfFuel := by rfl

theorem budget_one (site : P10.Site .CALLDATALOAD) (valid : Array UInt256) :
    Assembly.driverSteps 1 1 valid site.state = .error .OutOfFuel := by rfl

private theorem load_step (state : EVM.State) (fuel cost : Nat) :
    EVM.step (fuel+1) cost (some (.CALLDATALOAD, none)) state =
      match state.stack.pop with
      | none => .error .StackUnderflow
      | some (tail, offset) =>
        let prepared := Assembly.chargedPrepare state cost
        .ok (prepared.replaceStackAndIncrPC
          (EvmYul.State.calldataload prepared.toSharedState.toState offset :: tail)) := by
  cases state with
  | mk shared pc stack length => cases stack <;> rfl

theorem charged (site : P10.Site .CALLDATALOAD) (valid : Array UInt256) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) valid site.state =
      match Assembly.driverGate valid site.state .CALLDATALOAD with
      | .error error => .error error
      | .ok (state, cost) =>
        match state.stack.pop with
        | none => .error .StackUnderflow
        | some (tail, offset) =>
          let prepared := Assembly.chargedPrepare state cost
          .ok (prepared.replaceStackAndIncrPC
            (EvmYul.State.calldataload prepared.toSharedState.toState offset :: tail)) := by
  rw [Assembly.driverSteps, P10.DecoderAgreement.decode_all site]
  simp only [P10.DecoderAgreement.referenceOp, Option.option, bind, Except.bind]
  cases gate : Assembly.driverGate valid site.state .CALLDATALOAD with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨state, cost⟩
    dsimp only
    rw [load_step]
    cases state with
    | mk shared pc stack length => cases stack <;> rfl

theorem continuation (site : P10.Site .CALLDATALOAD) (valid : Array UInt256) (fuel : Nat) :
    EVM.X (fuel+2) valid site.state =
      match Assembly.driverSteps 1 (fuel+2) valid site.state with
      | .error error => .error error
      | .ok next => EVM.X (fuel+1) valid next := by
  rw [Assembly.X_unfold, P10.DecoderAgreement.decode_all site,
    Assembly.driverSteps, P10.DecoderAgreement.decode_all site]
  simp only [P10.DecoderAgreement.referenceOp, Option.getD_some, Option.option, bind, Except.bind]
  cases gate : Assembly.driverGate valid site.state .CALLDATALOAD with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨state, cost⟩
    dsimp only
    cases execution : EVM.step (fuel+1) cost (some (.CALLDATALOAD,none)) state with
    | error error => rfl
    | ok next => rfl

/-- All load obligations are discharged against the actual pinned model.
This certifies a primitive access, not ABI validation or Source/world adequacy. -/
def certificate : CalldataLoadCertificate where
  payload := payload
  budget_zero := budget_zero
  budget_one := budget_one
  charged := charged
  continuation := continuation

namespace Checks

def gasSite (gas : Nat) : P10.Site .CALLDATALOAD where
  seed := {(default : EVM.State) with gasAvailable := UInt256.ofNat gas}
  before := []
  after := []
  pcFits := by decide

theorem gas_refused : Assembly.driverSteps 1 2 #[] (gasSite 0).state = .error .OutOfGass := by rfl

theorem stack_refused : Assembly.driverSteps 1 2 #[] (gasSite 3).state = .error .StackUnderflow := by rfl

/-- Low dispatcher fuel must not be silently identified with low X fuel. -/
theorem low_budget_distinct :
    Assembly.driverSteps 1 1 #[] (gasSite 0).state = .error .OutOfFuel ∧
    EVM.X 1 #[] (gasSite 0).state = .error .OutOfGass := by constructor <;> rfl

/-- A successful charged load preserves the old tail and every unmodified field. -/
def populatedSite : P10.Site .CALLDATALOAD where
  seed := {(default : EVM.State) with
    gasAvailable := UInt256.ofNat 3
    execLength := 41
    stack := [UInt256.ofNat 1, UInt256.ofNat 258, UInt256.ofNat 513]
    executionEnv := {(default : EVM.State).executionEnv with calldata := ⟨#[0x12,0x34]⟩}}
  before := []
  after := []
  pcFits := by decide

theorem populated :
    Assembly.driverSteps 1 2 #[] populatedSite.state =
      .ok {populatedSite.state with
        pc := UInt256.ofNat 1
        gasAvailable := UInt256.ofNat 0
        execLength := 42
        stack := EvmYul.State.calldataload populatedSite.state.toSharedState.toState
          (UInt256.ofNat 1) :: [UInt256.ofNat 258, UInt256.ofNat 513]} := by
  rw [charged]
  rfl

theorem populated_word (frame : Source.Fr) :
    (EvmYul.State.calldataload populatedSite.state.toSharedState.toState
      (UInt256.ofNat 1)).toNat = 0x34 * 256^31 := by
  rw [payload _ {frame with cd := [0x12,0x34]} _ rfl]
  simp only [Source.cdWordAt]
  decide +kernel

/-- Ordered bytes, unaligned offset, end padding and the large-offset branch. -/
theorem bytes_offsets (native : EvmYul.State .EVM) (frame : Source.Fr) :
    let input := {frame with cd := [0x12, 0x34]}
    ((installed native input).calldataload (UInt256.ofNat 0)).toNat = 0x1234 * 256^30 ∧
    ((installed native input).calldataload (UInt256.ofNat 1)).toNat = 0x34 * 256^31 ∧
    ((installed native input).calldataload (UInt256.ofNat 2)).toNat = 0 ∧
    ((installed native input).calldataload (UInt256.ofNat (2^64))).toNat = 0 := by
  dsimp only
  simp only [installed_payload, Source.cdWordAt]
  decide +kernel

/-- info: 'SolidityBridge.AccessBridge.Calldata.Checks.populated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms populated
/-- info: 'SolidityBridge.AccessBridge.Calldata.Checks.populated_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms populated_word
/-- info: 'SolidityBridge.AccessBridge.Calldata.Checks.gas_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gas_refused
/-- info: 'SolidityBridge.AccessBridge.Calldata.Checks.stack_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stack_refused
/-- info: 'SolidityBridge.AccessBridge.Calldata.Checks.low_budget_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms low_budget_distinct
/-- info: 'SolidityBridge.AccessBridge.Calldata.Checks.bytes_offsets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bytes_offsets
end Checks

/-- info: 'SolidityBridge.AccessBridge.Calldata.installed_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms installed_payload
/-- info: 'SolidityBridge.AccessBridge.Calldata.readBytes_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readBytes_source
/-- info: 'SolidityBridge.AccessBridge.Calldata.payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms payload
/-- info: 'SolidityBridge.AccessBridge.Calldata.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
/-- info: 'SolidityBridge.AccessBridge.Calldata.budget_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms budget_zero
/-- info: 'SolidityBridge.AccessBridge.Calldata.budget_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms budget_one
/-- info: 'SolidityBridge.AccessBridge.Calldata.charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms charged
/-- info: 'SolidityBridge.AccessBridge.Calldata.continuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms continuation
end SolidityBridge.AccessBridge.Calldata
