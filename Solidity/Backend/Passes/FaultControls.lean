import Solidity.Backend.Passes.FaultTail
import Solidity.Backend.Passes.RevertControls

/-! Real allocation/capture/typed-loop controls for explicit reached Inputs.
Existing complete ordered vectors and negative controls remain unchanged. -/
namespace Solidity.Backend.Passes.FaultControls
open Solidity.Evm Solidity.Evm.Compiler Solidity.Evm.Memory
open Solidity.Backend.Passes.Controls.Fixture
open Solidity.Backend.Passes.AllocatingControls
open Solidity.Backend.Passes.TripleControls
open Solidity.Backend.Passes.DivergenceControls

/-- Immediate fault uses the typed loop, with no suffix Input or success. -/
theorem immediate (tail : List Word) :
    (Spin.program (C := C) (Γ := [])).run (State.init C) = .error .diverge ∧
    run initialSpin.code {initialMachine with stack := tail} = .fault ∧
    run (initialSpin.code ++ (allocationStage.code ++ captureStage.code))
      {initialMachine with stack := tail} = .fault :=
  ⟨Spin.diverges _, Spin.fault_all_tails initial_input tail, DivergenceControls.immediate tail⟩

/-- The inferred proposition is the complete explicit-map iff RHS,
including the actual reached middle Input and emitted-code fault. -/
def middle_witness (tail : List Word) :=
  (compilation_mapped_fault_reached_iff (.memory allocationStage) middleSpin
    (compilation_input_stack (.memory allocationStage) prefix_input7 tail)
    (middle_link tail) rfl rfl).mp
      (by
        -- Extract the actual middle fault via its typed source divergence.
        obtain ⟨mid, hm, _, hrep⟩ := compilation_success (.memory allocationStage)
          (compilation_input_stack (.memory allocationStage) prefix_input7 tail) rfl
          ReachabilityControls.fresh_state_reaches_fixture
        obtain ⟨mb, ma⟩ := (mapped_output_iff (.memory allocationStage) _ _ _ _ _ _ _).mp hrep
        have hd := middle_link tail _ mid mb ReachabilityControls.fresh_state_reaches_fixture hm ma
        rw [run_append_ok hm]
        exact (compilation_fault_iff middleSpin hd rfl).mpr (Spin.diverges _))

/-- The full triple RHS includes both transported Inputs and the third run. -/
def third_witness (tail : List Word) :=
  (compilation_triple_fault_reached_iff (.memory allocationStage) (.memory captureStage) lastSpin
    (compilation_input_stack (.memory allocationStage) prefix_input7 tail)
    (memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel))
    (last_link tail) rfl rfl rfl).mp (DivergenceControls.third tail)

/-- Earlier divergence is excluded using the independently known source
success, leaving an actual reached middle Input and fault. -/
theorem middle_reached (tail : List Word) :
    ∃ (o : Solidity.Out C (State.init C).H Γ) (mid : Machine) (mb : Nat → Fin W),
      ReachabilityControls.populatedBuilder.run (State.init C) = .ok o ∧
      run allocationStage.code {initialMachine with stack := tail} = .ok mid 0 ∧
      MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
        {initialMachine with stack := tail} o.st mid mb ∧
      middleSpin.Input 1 7 mb o.st mid ∧
      (Spin.program (C := C)).run o.st = .error .diverge ∧
      run middleSpin.code mid = .fault := by
  rcases middle_witness tail with ⟨hs, _⟩ | h
  · rw [ReachabilityControls.fresh_state_reaches_fixture] at hs
    cases hs
  · simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using h

/-- Both independently successful source prefixes exclude the earlier
failure branches. The final Input consumes the second actual map nb. -/
theorem third_reached (tail : List Word) :
    ∃ (o : Solidity.Out C (State.init C).H Γ) (mid : Machine) (mb : Nat → Fin W),
      ReachabilityControls.populatedBuilder.run (State.init C) = .ok o ∧
      run allocationStage.code {initialMachine with stack := tail} = .ok mid 0 ∧
      MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
        {initialMachine with stack := tail} o.st mid mb ∧
      (Compilation.memory captureStage).Input 1 7 mb o.st mid ∧
      ∃ (u : Solidity.Out C o.st.H Γ) (next : Machine) (nb : Nat → Fin W),
        captureProg.run o.st = .ok u ∧ run captureStage.code mid = .ok next 0 ∧
        MappedOutput (.memory captureStage) 1 7 mb o.st mid u.st next nb ∧
        lastSpin.Input 1 7 nb u.st next ∧
        (Spin.program (C := C)).run u.st = .error .diverge ∧
        run lastSpin.code next = .fault := by
  rcases third_witness tail with ⟨hs, _⟩ | ⟨o, mid, mb, hs, hm, ma, di, h⟩
  · rw [ReachabilityControls.fresh_state_reaches_fixture] at hs
    cases hs
  · rcases h with ⟨hc, _⟩ | h
    · have ho : o = ⟨σ, ⟨σ.H, rfl⟩⟩ :=
        Except.ok.inj (hs.symm.trans ReachabilityControls.fresh_state_reaches_fixture)
      cases ho
      rw [capture_source] at hc
      cases hc
    · refine ⟨o, mid, mb, hs, hm, ?_, ?_, ?_⟩
      · simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using ma
      · simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using di
      · simpa only [allocationStage.cert.pushes_zero, captureStage.cert.pushes_zero,
          Nat.add_zero] using h

/-- Both prefix maps are selected before all tails, and the reached Input
consumes that same nb. Source successes are independently inhabited. -/
def shared_third :=
  compilation_third_fault_shared (.memory allocationStage) (.memory captureStage) lastSpin
    prefix_input7
    first_link
    (last_link []) rfl rfl rfl ReachabilityControls.fresh_state_reaches_fixture capture_source
    (Spin.diverges CaptureControls.afterCapture)

/-- Both actual intrinsic source halts and actual target outputs discriminate
loop divergence from ordinary revert and guarded asserting panic. -/
theorem distinct_terminals (tail : List Word) :
    (Spin.program (C := C)).run CaptureControls.afterCapture = .error .diverge ∧
    TripleFailures.badAfterCapture.run CaptureControls.afterCapture = .error .revert ∧
    RevertControls.panicProg.asserts = true ∧
    RevertControls.panicProg.run CaptureControls.afterCapture = .error .panic ∧
    run (allocationStage.code ++ (captureStage.code ++ lastSpin.code))
      {initialMachine with stack := tail} ≠
      run (allocationStage.code ++ (captureStage.code ++ TripleFailures.third.code))
        {initialMachine with stack := tail} ∧
    run (allocationStage.code ++ (captureStage.code ++ lastSpin.code))
      {initialMachine with stack := tail} ≠
      run (allocationStage.code ++ (captureStage.code ++ RevertControls.panicStage.code))
        {initialMachine with stack := tail} := by
  refine ⟨Spin.diverges _, TripleFailures.third_source, RevertControls.panic_source.1,
    RevertControls.panic_source.2, ?_, RevertControls.divergence_separate tail⟩
  rw [DivergenceControls.third tail, TripleFailures.third_reached tail]
  intro h
  cases h

/-- A reached fault cannot be reassigned to either independently successful
source prefix. -/
theorem wrong_stage : ReachabilityControls.populatedBuilder.run (State.init C) ≠ .error .diverge ∧
    captureProg.run σ ≠ .error .diverge := by
  rw [ReachabilityControls.fresh_state_reaches_fixture, capture_source]
  constructor <;> intro h <;> cases h

end Solidity.Backend.Passes.FaultControls
