import SolidityBridge.AccessBridge.MemoryControls

/-! Negative controls for the pinned writer at host-sized gaps. These are
logical-model observations, not a replacement writer or a restriction on P6
capacity, calldata admission or the permitted target gas. -/
namespace SolidityBridge.AccessBridge.HostWriteControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Evm.TryByteImage
private def u (n : Nat) : UInt256 := .ofNat n

theorem gap_cast_zero : USize.ofBitVec (BitVec.ofNat System.Platform.numBits (2^64)) = 0 := by
  apply congrArg USize.ofBitVec
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 System.Platform.numBits_le)

private theorem write_gap (gap : Nat) :
    (⟨#[0x34]⟩ : ByteArray).write 0 ByteArray.empty gap 1 =
      ((⟨#[0x34]⟩ : ByteArray) ++ ffi.ByteArray.zeroes (0 : USize)).copySlice 0
        (ByteArray.empty ++ ffi.ByteArray.zeroes
          (USize.ofBitVec (BitVec.ofNat System.Platform.numBits gap))) gap 1 := by
  simp only [ByteArray.write, ByteArray.size, ByteArray.empty, ByteArray.emptyWithCapacity,
    List.size_toArray, List.length_cons, List.length_nil,
    if_neg (by decide : ¬(1 : Nat)=0), if_neg (by decide : ¬(0 : Nat)≥1),
    Nat.sub_zero, Nat.min_self, Nat.zero_min, Nat.zero_sub, Nat.add_zero, BitVec.natCast_eq_ofNat]
  rfl

/-- The pinned logical writer installs the byte at zero after its gap cast wraps. -/
theorem large_gap_write (native : EvmYul.MachineState)
    (empty : native.memory = ByteArray.empty) :
    (native.mstore8 (u (2^64)) (u 0x34)).memory.data.toList =
      [0x34] := by
  have offset : (u (2^64)).toNat = 2^64 := by decide +kernel
  change ((⟨#[0x34]⟩ : ByteArray).write 0 native.memory (u (2^64)).toNat 1).data.toList = _
  rw [empty, offset, write_gap, gap_cast_zero, ffi.ByteArray.zeroes_zero]
  rfl

private def C : Contract := {vars := []}
private def frame (pipeline : Pipeline) : FrameMem C [] where
  st := State.init C
  key := ⟨3,1,pipeline,7,lenU 1 (by decide),lenU 2 (by decide),lenU 4 (by decide)⟩
  scalar := by intro R i; cases i
  capacity := 2^64+32
  aligned := ⟨2^59+1,by decide +kernel⟩
  data := fun _ => 0
  highWaterWords := 0
  resident := by decide +kernel
  zeroAbove := by intro i high; rfl
private def span (pipeline : Pipeline) : ByteSpan (frame pipeline).capacity :=
  ⟨lenU (2^64) (by decide +kernel),lenU 1 (by decide),
    Or.inr (by change (2^64 : Nat)+1≤2^64+32; decide +kernel)⟩
private def native : EvmYul.MachineState :=
  {(default : EvmYul.MachineState) with gasAvailable := u (UInt256.size-1)}

/-- Actual initial P6/native representation, with no capacity admission bound. -/
theorem initial_image (pipeline : Pipeline) : FrameImage (frame pipeline) native := by
  refine ⟨?_,rfl,by change (0 : Nat)<UInt256.size; decide +kernel⟩
  intro address
  change 0 = (if h : address<2^64+32 then (0 : UInt8) else 0)
  split <;> rfl

/-- The P6 write and pinned write cannot satisfy the frozen byte-image relation. -/
theorem post_image_refused (pipeline : Pipeline) (initial : EvmYul.MachineState)
    (empty : initial.memory = ByteArray.empty) :
    ¬ FrameImage
      (Yul.Adapters.P6ByteMemory.writeSpan (frame pipeline) (span pipeline) [0x34] rfl)
      (initial.mstore8 (u (2^64)) (u 0x34)) := by
  intro image
  have mismatch := image.bytes 0
  have exterior : Environment.writeBytes (MemoryOps.Physical.frameBytes (frame pipeline))
      (span pipeline).offset.val.toNat [0x34] 0 =
      MemoryOps.Physical.frameBytes (frame pipeline) 0 :=
    Environment.writeBytes_frame [0x34] _ 0 _
      (Or.inl (by change (0 : Nat)<2^64; decide +kernel))
  rw [large_gap_write _ empty, Yul.Adapters.P6ByteMemory.write_image, exterior] at mismatch
  change (0x34 : UInt8) = 0 at mismatch
  exact (by decide : (0x34 : UInt8) ≠ 0) mismatch

/-- This counterexample's reached active byte extent still fits the EVM word. -/
theorem active_extent_fits :
    32 * (native.mstore8 (u (2^64)) (u 0x34)).activeWords.toNat < UInt256.size := by
  decide +kernel

private def site : RoadmapV15.P10.Site .MSTORE8 where
  seed := {(default : EVM.State) with
    toMachineState := native
    stack := [u (2^64),u 0x34]}
  before := []
  after := []
  pcFits := by decide

theorem charged_initial_image (pipeline : Pipeline) :
    FrameImage (frame pipeline) site.state.toMachineState := initial_image pipeline

/-- The original expansion/gas/stack gate admits this offset with a legal word of gas. -/
theorem charged_accepted :
    (Assembly.driverSteps 1 2 #[] site.state).toOption.isSome = true := by
  rw [MemoryCharged.store8_charged]
  decide +kernel

private def chargedState : EVM.State :=
  {site.state with gasAvailable :=
    (site.state.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost site.state .MSTORE8))}

private theorem site_gate : Assembly.driverGate #[] site.state .MSTORE8 = .ok (chargedState,3) := by
  have first : ¬ site.state.gasAvailable.toNat < EVM.memoryExpansionCost site.state .MSTORE8 := by
    decide +kernel
  have second : ¬ (site.state.gasAvailable -
      UInt256.ofNat (EVM.memoryExpansionCost site.state .MSTORE8)).toNat < 3 := by decide +kernel
  have base : ∀ input : EVM.State, EVM.C' input .MSTORE8 = 3 := by intro input; rfl
  simp only [Assembly.driverGate]
  rw [if_neg first]
  dsimp only [bind, Except.bind, pure, Except.pure]
  simp only [base]
  rw [if_neg second]
  rfl

/-- An actual successful charged reached state fails the P6 post-image relation. -/
theorem charged_post_refused (pipeline : Pipeline) :
    ∃ post : EVM.State,
      Assembly.driverSteps 1 2 #[] site.state = .ok post ∧
      ¬ FrameImage
        (Yul.Adapters.P6ByteMemory.writeSpan (frame pipeline) (span pipeline) [0x34] rfl)
        post.toMachineState := by
  let prepared := Assembly.chargedPrepare chargedState 3
  let post := ({prepared with toMachineState :=
    (prepared.toMachineState.mstore8 (u (2^64)) (u 0x34))} : EVM.State).replaceStackAndIncrPC []
  refine ⟨post,?_,?_⟩
  · rw [MemoryCharged.store8_charged, site_gate]
    rfl
  · exact post_image_refused pipeline prepared.toMachineState rfl

/-- info: 'SolidityBridge.AccessBridge.HostWriteControls.charged_initial_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms charged_initial_image
/-- info: 'SolidityBridge.AccessBridge.HostWriteControls.charged_post_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms charged_post_refused
/-- info: 'SolidityBridge.AccessBridge.HostWriteControls.initial_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial_image
/-- info: 'SolidityBridge.AccessBridge.HostWriteControls.post_image_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms post_image_refused
/-- info: 'SolidityBridge.AccessBridge.HostWriteControls.active_extent_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms active_extent_fits
/-- info: 'SolidityBridge.AccessBridge.HostWriteControls.charged_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms charged_accepted
/-- info: 'SolidityBridge.AccessBridge.HostWriteControls.gap_cast_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms gap_cast_zero
/-- info: 'SolidityBridge.AccessBridge.HostWriteControls.large_gap_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms large_gap_write
end SolidityBridge.AccessBridge.HostWriteControls
