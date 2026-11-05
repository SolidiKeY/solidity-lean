import SolidityBridge.AccessBridge.MemoryCharged
import SolidityBridge.ExternalEvm.PaddingInterface
import SolidityBridge.RoadmapV15.P10.MachineObservation

/-! Inhabited/refusal controls for the initial P6 image and actual charged
memory access. MSIZE's successful native client reuses the published theorem.
Store/copy reached memories remain the actual pinned operations; no P6 payload
preservation is inferred from these charged controls. -/
namespace SolidityBridge.AccessBridge.MemoryControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Evm.TryByteImage
open SolidityBridge.RoadmapV15
private def u (n : Nat) : UInt256 := .ofNat n
private def C : Contract := {vars := []}
private def frame (pipeline : Pipeline) : FrameMem C [] where
  st := State.init C
  key := ⟨3,1,pipeline,7,lenU 1 (by decide),lenU 2 (by decide),lenU 4 (by decide)⟩
  scalar := by intro R i; cases i
  capacity := 96
  aligned := ⟨3,rfl⟩
  data := fun _ => 0
  highWaterWords := 2
  resident := by decide
  zeroAbove := by intro i high; rfl
private def native : EvmYul.MachineState :=
  {(default : EvmYul.MachineState) with activeWords := u 2}

theorem inhabited (pipeline : Pipeline) : FrameImage (frame pipeline) native := by
  refine ⟨?_,rfl,by change 64 < UInt256.size; decide⟩
  intro address
  change 0 = (if h : address < 96 then (0 : UInt8) else 0)
  split <;> rfl

theorem reserve_unbounded (pipeline : Pipeline) (words : Nat) :
    FrameImage (expandZero (frame pipeline) words) native :=
  MemoryCharged.reserve _ _ (inhabited pipeline) words

theorem p6_size (pipeline : Pipeline) : native.msize.toNat = 64 :=
  MemoryCharged.size_payload (frame pipeline) native (inhabited pipeline)

theorem size_not_buffer : native.msize.toNat ≠ native.memory.size := by decide +kernel

theorem wrong_active_refused (pipeline : Pipeline) :
    ¬ FrameImage (frame pipeline) {native with activeWords := u 1} := by
  intro image
  have wrong : 1 = 2 := image.active
  exact (by decide : (1 : Nat) ≠ 2) wrong

theorem wrong_byte_refused (pipeline : Pipeline) :
    ¬ FrameImage (frame pipeline) {native with memory := ⟨#[1]⟩} := by
  intro image
  have wrong : (1 : UInt8) = 0 := image.bytes 0
  exact (by decide : (1 : UInt8) ≠ 0) wrong

private def tail : List UInt256 := [u 258,u 513]
private def site (op : Backend.Op) (gas active : Nat) (stack : List UInt256) : P10.Site op where
  seed := {(default : EVM.State) with
    gasAvailable := u gas
    activeWords := u active
    execLength := 41
    stack := stack
    executionEnv := {(default : EVM.State).executionEnv with calldata := ⟨#[0x12,0x34]⟩}}
  before := []
  after := []
  pcFits := by decide

theorem size_success :
    Assembly.driverSteps 1 2 #[] (site .MSIZE 2 2 tail).state =
      .ok {(site .MSIZE 2 2 tail).state with
        gasAvailable := u 0, execLength := 42, pc := u 1, stack := u 64 :: tail} := by
  exact (P10.msize_agreement _ 0 (by decide +kernel) (by decide +kernel)).1

/-- Offset31 touches two words; both expansion6 and opcode3 are charged. -/
theorem load_expanding :
    Assembly.driverSteps 1 2 #[] (site .MLOAD 9 0 (u 31 :: tail)).state =
      .ok {(site .MLOAD 9 0 (u 31 :: tail)).state with
        gasAvailable := u 0, activeWords := u 2, execLength := 42, pc := u 1,
        stack := u 0 :: tail} := by
  rw [MemoryCharged.load_charged]
  rfl

theorem store_expanding :
    let input := (site .MSTORE 9 0 (u 31 :: u 0x1234 :: tail)).state
    Assembly.driverSteps 1 2 #[] input =
      .ok {input with
        toMachineState := ((Assembly.chargedPrepare input 9).toMachineState.mstore (u 31) (u 0x1234)),
        execLength := 42, pc := u 1, stack := tail} := by
  dsimp only
  rw [MemoryCharged.store_charged]
  rfl

theorem store8_expanding :
    let input := (site .MSTORE8 9 0 (u 32 :: u 0x1234 :: tail)).state
    Assembly.driverSteps 1 2 #[] input =
      .ok {input with
        toMachineState := ((Assembly.chargedPrepare input 9).toMachineState.mstore8 (u 32) (u 0x1234)),
        execLength := 42, pc := u 1, stack := tail} := by
  dsimp only
  rw [MemoryCharged.store8_charged]
  rfl

/-- Copy expansion6 plus base/copy6, with unchanged original source bytes. -/
theorem copy_expanding :
    let input := (site .CALLDATACOPY 12 0 (u 31 :: u 1 :: u 2 :: tail)).state
    Assembly.driverSteps 1 2 #[] input =
      .ok {input with
        toSharedState := ((Assembly.chargedPrepare input 12).toSharedState.calldatacopy (u 31) (u 1) (u 2)),
        execLength := 42, pc := u 1, stack := tail} := by
  dsimp only
  rw [MemoryCharged.copy_charged]
  rfl

/-- Empty copies do not validate either largest offset or expand active memory. -/
theorem copy_empty_endpoint :
    let input := (site .CALLDATACOPY 3 2
      (u (UInt256.size-1) :: u (UInt256.size-1) :: u 0 :: tail)).state
    Assembly.driverSteps 1 2 #[] input =
      .ok {input with gasAvailable := u 0, execLength := 42, pc := u 1, stack := tail} := by
  dsimp only
  rw [MemoryCharged.copy_charged]
  rfl

/-- MSTORE8 uses the low byte and zero-fills a newly reached gap. -/
theorem store8_low_byte :
    ((default : EvmYul.MachineState).mstore8 (u 32) (u 0x1234)).memory.data.toList =
      List.replicate 32 0 ++ [0x34] := by
  change (((⟨#[0x34]⟩ : ByteArray) ++ ffi.ByteArray.zeroes (0 : USize)).copySlice 0
    (ByteArray.empty ++ ffi.ByteArray.zeroes (32 : USize)) 32 1).data.toList = _
  have width : (32 : USize).toNat = 32 :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by decide : 32 < 4294967296) USize.le_size)
  rw [ffi.ByteArray.zeroes_zero]
  simp only [ffi.ByteArray.zeroes, width]
  rfl

/-- Expansion is charged before the base operation and is not silently free. -/
theorem expansion_refused :
    Assembly.driverSteps 1 2 #[] (site .MLOAD 5 0 (u 31 :: tail)).state =
      .error .OutOfGass := by rfl

theorem gas_refused (op : Backend.Op)
    (allowed : op ∈ [.MSIZE,.MLOAD,.MSTORE,.MSTORE8,.CALLDATACOPY]) :
    Assembly.driverSteps 1 2 #[] (site op 0 0 []).state = .error .OutOfGass := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem stack_refused (op : Backend.Op)
    (allowed : op ∈ [.MLOAD,.MSTORE,.MSTORE8,.CALLDATACOPY]) :
    Assembly.driverSteps 1 2 #[] (site op 100 0 []).state = .error .StackUnderflow := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with rfl | rfl | rfl | rfl <;> rfl

private theorem size_capacity_error (state : EVM.State) (valid : Array UInt256)
    (gas : state.gasAvailable = UInt256.ofNat 2) (big : 1024 ≤ state.stack.length) :
    Assembly.driverGate valid state .MSIZE = .error .StackOverflow := by
  have expansion : EVM.memoryExpansionCost state .MSIZE = 0 := by
    simp only [EVM.memoryExpansionCost, EVM.memoryExpansionCost.μᵢ', Nat.sub_self]
  have charge : state.gasAvailable-UInt256.ofNat 0=state.gasAvailable := by
    change UInt256.mk (state.gasAvailable.val-0)=state.gasAvailable
    rw [sub_zero]
  have cost : EVM.C' state .MSIZE=2 := rfl
  have enough : ¬state.gasAvailable.toNat<2 := by rw [gas]; decide +kernel
  have capacity : state.stack.length+1>1024 := by omega
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost, EVM.δ, EVM.α, Option.getD_some, reduceCtorEq,
    false_and, if_false, Nat.sub_zero, if_neg (Nat.not_lt_zero _), if_neg enough, if_pos capacity]
  rfl

theorem size_capacity_refused :
    Assembly.driverSteps 1 2 #[] (site .MSIZE 2 0 (List.replicate 1024 (u 0))).state =
      .error .StackOverflow := by
  have length : (site .MSIZE 2 0 (List.replicate 1024 (u 0))).state.stack.length = 1024 :=
    List.length_replicate
  rw [MemoryCharged.size_charged, size_capacity_error _ _ rfl (by rw [length])]

/-- info: 'SolidityBridge.AccessBridge.MemoryControls.size_capacity_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms size_capacity_refused
/-- info: 'SolidityBridge.AccessBridge.MemoryControls.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inhabited
/-- info: 'SolidityBridge.AccessBridge.MemoryControls.reserve_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reserve_unbounded
/-- info: 'SolidityBridge.AccessBridge.MemoryControls.p6_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms p6_size
/-- info: 'SolidityBridge.AccessBridge.MemoryControls.size_not_buffer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms size_not_buffer
/-- info: 'SolidityBridge.AccessBridge.MemoryControls.wrong_active_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_active_refused
/-- info: 'SolidityBridge.AccessBridge.MemoryControls.wrong_byte_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_byte_refused
/-- info: 'SolidityBridge.AccessBridge.MemoryControls.size_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms size_success
/-- info: 'SolidityBridge.AccessBridge.MemoryControls.load_expanding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms load_expanding
/-- info: 'SolidityBridge.AccessBridge.MemoryControls.store_expanding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms store_expanding
/-- info: 'SolidityBridge.AccessBridge.MemoryControls.store8_expanding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms store8_expanding
/-- info: 'SolidityBridge.AccessBridge.MemoryControls.copy_expanding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms copy_expanding
/-- info: 'SolidityBridge.AccessBridge.MemoryControls.copy_empty_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms copy_empty_endpoint
/-- info: 'SolidityBridge.AccessBridge.MemoryControls.store8_low_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms store8_low_byte
/-- info: 'SolidityBridge.AccessBridge.MemoryControls.expansion_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms expansion_refused
/-- info: 'SolidityBridge.AccessBridge.MemoryControls.gas_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gas_refused
/-- info: 'SolidityBridge.AccessBridge.MemoryControls.stack_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stack_refused
end SolidityBridge.AccessBridge.MemoryControls
