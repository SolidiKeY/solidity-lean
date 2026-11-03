import SolidityBridge.AccessBridge.MemoryInterface

/-! Full charged primitive memory outcomes over the existing P10 driver.
Only MSIZE is linked to P6 here. Payload/preservation for other operations and
whole compiler/source/world adequacy remain separate obligations. -/
namespace SolidityBridge.AccessBridge.MemoryCharged
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Evm.TryByteImage

theorem size_payload : ∀ {C : Contract} {Γ : Ctx} (frame : FrameMem C Γ)
    (native : EvmYul.MachineState), FrameImage frame native →
  native.msize.toNat = 32 * frame.highWaterWords := by
  intro C Γ frame native image
  change (native.activeWords.toNat * 32) % UInt256.size = _
  rw [image.active, Nat.mul_comm, Nat.mod_eq_of_lt image.wordFit]

theorem size_charged : ∀ (site : RoadmapV15.P10.Site .MSIZE)
    (valid : Array UInt256) (fuel : Nat),
  Assembly.driverSteps 1 (fuel+2) valid site.state =
    match Assembly.driverGate valid site.state .MSIZE with
    | .error error => .error error
    | .ok (charged,cost) =>
      let prepared := Assembly.chargedPrepare charged cost
      .ok (prepared.replaceStackAndIncrPC (prepared.toMachineState.msize :: charged.stack)) := by
  intro site valid fuel
  rw [Assembly.driverSteps, RoadmapV15.P10.DecoderAgreement.decode_all site]
  simp only [RoadmapV15.P10.DecoderAgreement.referenceOp, Option.option, bind, Except.bind]
  cases gate : Assembly.driverGate valid site.state .MSIZE with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨state,cost⟩
    dsimp only
    cases state with
    | mk shared pc stack count =>
      rfl

theorem load_charged : ∀ (site : RoadmapV15.P10.Site .MLOAD)
    (valid : Array UInt256) (fuel : Nat),
  Assembly.driverSteps 1 (fuel+2) valid site.state =
    match Assembly.driverGate valid site.state .MLOAD with
    | .error error => .error error
    | .ok (charged,cost) =>
      match charged.stack.pop with
      | none => .error .StackUnderflow
      | some (tail,address) =>
        let prepared := Assembly.chargedPrepare charged cost
        let (value,memory) := prepared.toMachineState.mload address
        .ok (({prepared with toMachineState := memory} : EVM.State).replaceStackAndIncrPC
          (value :: tail)) := by
  intro site valid fuel
  rw [Assembly.driverSteps, RoadmapV15.P10.DecoderAgreement.decode_all site]
  simp only [RoadmapV15.P10.DecoderAgreement.referenceOp, Option.option, bind, Except.bind]
  cases gate : Assembly.driverGate valid site.state .MLOAD with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨state,cost⟩
    dsimp only
    cases state with
    | mk shared pc stack count =>
      cases stack <;> rfl

theorem store_charged : ∀ (site : RoadmapV15.P10.Site .MSTORE)
    (valid : Array UInt256) (fuel : Nat),
  Assembly.driverSteps 1 (fuel+2) valid site.state =
    match Assembly.driverGate valid site.state .MSTORE with
    | .error error => .error error
    | .ok (charged,cost) =>
      match charged.stack.pop2 with
      | none => .error .StackUnderflow
      | some (tail,address,value) =>
        let prepared := Assembly.chargedPrepare charged cost
        .ok (({prepared with toMachineState := prepared.toMachineState.mstore address value} :
          EVM.State).replaceStackAndIncrPC tail) := by
  intro site valid fuel
  rw [Assembly.driverSteps, RoadmapV15.P10.DecoderAgreement.decode_all site]
  simp only [RoadmapV15.P10.DecoderAgreement.referenceOp, Option.option, bind, Except.bind]
  cases gate : Assembly.driverGate valid site.state .MSTORE with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨state,cost⟩
    dsimp only
    cases state with
    | mk shared pc stack count =>
      cases stack with
      | nil => rfl
      | cons address tail => cases tail <;> rfl

theorem store8_charged : ∀ (site : RoadmapV15.P10.Site .MSTORE8)
    (valid : Array UInt256) (fuel : Nat),
  Assembly.driverSteps 1 (fuel+2) valid site.state =
    match Assembly.driverGate valid site.state .MSTORE8 with
    | .error error => .error error
    | .ok (charged,cost) =>
      match charged.stack.pop2 with
      | none => .error .StackUnderflow
      | some (tail,address,value) =>
        let prepared := Assembly.chargedPrepare charged cost
        .ok (({prepared with toMachineState := prepared.toMachineState.mstore8 address value} :
          EVM.State).replaceStackAndIncrPC tail) := by
  intro site valid fuel
  rw [Assembly.driverSteps, RoadmapV15.P10.DecoderAgreement.decode_all site]
  simp only [RoadmapV15.P10.DecoderAgreement.referenceOp, Option.option, bind, Except.bind]
  cases gate : Assembly.driverGate valid site.state .MSTORE8 with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨state,cost⟩
    dsimp only
    cases state with
    | mk shared pc stack count =>
      cases stack with
      | nil => rfl
      | cons address tail => cases tail <;> rfl

theorem copy_charged : ∀ (site : RoadmapV15.P10.Site .CALLDATACOPY)
    (valid : Array UInt256) (fuel : Nat),
  Assembly.driverSteps 1 (fuel+2) valid site.state =
    match Assembly.driverGate valid site.state .CALLDATACOPY with
    | .error error => .error error
    | .ok (charged,cost) =>
      match charged.stack.pop3 with
      | none => .error .StackUnderflow
      | some (tail,destination,source,length) =>
        let prepared := Assembly.chargedPrepare charged cost
        .ok (({prepared with toSharedState := (prepared.toSharedState.calldatacopy
          destination source length)} : EVM.State).replaceStackAndIncrPC tail) := by
  intro site valid fuel
  rw [Assembly.driverSteps, RoadmapV15.P10.DecoderAgreement.decode_all site]
  simp only [RoadmapV15.P10.DecoderAgreement.referenceOp, Option.option, bind, Except.bind]
  cases gate : Assembly.driverGate valid site.state .CALLDATACOPY with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨state,cost⟩
    dsimp only
    cases state with
    | mk shared pc stack count =>
      cases stack with
      | nil => rfl
      | cons destination tail =>
        cases tail with
        | nil => rfl
        | cons source rest => cases rest <;> rfl

theorem continuation : ∀ (op : Backend.Op),
  op ∈ [.MSIZE,.MLOAD,.MSTORE,.MSTORE8,.CALLDATACOPY] →
  ∀ (site : RoadmapV15.P10.Site op) (valid : Array UInt256) (fuel : Nat),
  EVM.X (fuel+2) valid site.state =
    match Assembly.driverSteps 1 (fuel+2) valid site.state with
    | .error error => .error error
    | .ok next => EVM.X (fuel+1) valid next := by
  intro op allowed site valid fuel
  have nonhalting : ∀ next : EVM.State,
      Assembly.driverHalt next
        (RoadmapV15.P10.DecoderAgreement.referenceOp op) = none := by
    intro next
    simp only [List.mem_cons, List.not_mem_nil, or_false] at allowed
    rcases allowed with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [Assembly.X_unfold,
    RoadmapV15.P10.DecoderAgreement.decode_all site,
    Assembly.driverSteps,
    RoadmapV15.P10.DecoderAgreement.decode_all site]
  simp only [Option.getD_some, Option.option, bind, Except.bind]
  cases gate : Assembly.driverGate valid site.state
      (RoadmapV15.P10.DecoderAgreement.referenceOp op) with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨state,cost⟩
    dsimp only
    cases execution : EVM.step (fuel+1) cost
        (some (RoadmapV15.P10.DecoderAgreement.referenceOp op,none)) state with
    | error error => rfl
    | ok next => simp only [nonhalting, Assembly.driverSteps]

theorem budget_zero : ∀ (op : Backend.Op) (site : RoadmapV15.P10.Site op) (valid : Array UInt256),
  Assembly.driverSteps 1 0 valid site.state = .error .OutOfFuel := by
  intro op site valid
  rfl

theorem budget_one : ∀ (op : Backend.Op) (site : RoadmapV15.P10.Site op) (valid : Array UInt256),
  Assembly.driverSteps 1 1 valid site.state = .error .OutOfFuel := by
  intro op site valid
  rfl

/-- Arbitrarily increasing reserved capacity preserves the native byte image
and active extent. Reserved bytes are not an admission or gas restriction. -/
theorem reserve {C : Contract} {Γ : Ctx} (frame : FrameMem C Γ)
    (native : EvmYul.MachineState) (image : FrameImage frame native) (words : Nat) :
    FrameImage (expandZero frame words) native := by
  refine ⟨?_, image.active, image.wordFit⟩
  intro address
  rw [MemoryOps.Physical.frameBytes_expandZero]
  exact image.bytes address

def certificate : MemoryAccessCertificate where
  size_payload := size_payload
  size_charged := size_charged
  load_charged := load_charged
  store_charged := store_charged
  store8_charged := store8_charged
  copy_charged := copy_charged
  continuation := continuation
  budget_zero := budget_zero
  budget_one := budget_one

/-- info: 'SolidityBridge.AccessBridge.MemoryCharged.size_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms size_payload
/-- info: 'SolidityBridge.AccessBridge.MemoryCharged.size_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms size_charged
/-- info: 'SolidityBridge.AccessBridge.MemoryCharged.load_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms load_charged
/-- info: 'SolidityBridge.AccessBridge.MemoryCharged.store_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms store_charged
/-- info: 'SolidityBridge.AccessBridge.MemoryCharged.store8_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms store8_charged
/-- info: 'SolidityBridge.AccessBridge.MemoryCharged.copy_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms copy_charged
/-- info: 'SolidityBridge.AccessBridge.MemoryCharged.continuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms continuation
/-- info: 'SolidityBridge.AccessBridge.MemoryCharged.budget_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms budget_zero
/-- info: 'SolidityBridge.AccessBridge.MemoryCharged.budget_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms budget_one
/-- info: 'SolidityBridge.AccessBridge.MemoryCharged.reserve' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reserve
/-- info: 'SolidityBridge.AccessBridge.MemoryCharged.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end SolidityBridge.AccessBridge.MemoryCharged
