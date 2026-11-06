import Solidity.Backend.Passes.TripleControls

/-! Distinct actually reached terminal failures. Later stages need source
success only on their reached path. This is the internal coarse boundary. -/
namespace Solidity.Backend.Passes.TripleFailures
open Solidity.Evm Solidity.Evm.Compiler Solidity.Evm.Memory
open Solidity.Backend.Passes.Controls.Fixture
open Solidity.Backend.Passes.AllocatingControls
open Solidity.Backend.Passes.TripleControls

def stop : Prog C [] [] := .cons .revert .nil
def first : CompiledProg 1 (Frag.init []) stop :=
  (compileProg 1 (Frag.init []) stop).get (by decide +kernel)

theorem first_source : stop.run (State.init C) = .error .revert := rfl

/-- No source or Input obligation for the skipped allocating/capture code. -/
theorem first_short_circuit (tail : List Word) :
    run (first.code ++ (allocationStage.code ++ captureStage.code))
      {initialMachine with stack := tail} = .revert := by
  have hi : (Compilation.memory first).Input 1 7 initialBase (State.init C) initialMachine :=
    ⟨initial_repr7.1, by decide +kernel, .inl (by decide +kernel)⟩
  exact run_append_revert ((compilation_revert_iff (.memory first)
    (compilation_input_stack (.memory first) hi tail) rfl).mpr (.inl first_source))

def middleBad : CompiledProg 1 allocationStage.frag CompileExamples.badRhsRead :=
  (compileProg 1 allocationStage.frag CompileExamples.badRhsRead).get (by decide +kernel)
def afterBad : CompiledProg 1 middleBad.frag captureProg :=
  (compileProg 1 middleBad.frag captureProg).get (by decide +kernel)

/-- First source success and second failure; no third source run. -/
theorem second_reached (tail : List Word) :
    run (allocationStage.code ++ (middleBad.code ++ afterBad.code))
      {initialMachine with stack := tail} = .revert := by
  have ad : MappedBoundaryLink (.memory allocationStage) (.memory middleBad)
      1 7 initialBase (State.init C) {initialMachine with stack := tail} :=
    memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel)
  have de : ReachedMappedLink (.memory allocationStage) (.memory middleBad) (.memory afterBad)
      1 7 initialBase (State.init C) {initialMachine with stack := tail} := by
    intro o mid mb _ _ _
    exact memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel)
  exact (compilation_triple_revert_iff (.memory allocationStage) (.memory middleBad)
    (.memory afterBad) (compilation_input_stack (.memory allocationStage) prefix_input7 tail)
    ad de rfl rfl rfl).mpr (.inr ⟨_, ReachabilityControls.fresh_state_reaches_fixture,
      .inl (.inl LinkedControls.right_stage_source_revert)⟩)

def badAfterCapture : Prog C Γ Γ :=
  .cons (.assignLocal .here ExpressionControls.badRead) .nil
def third : CompiledProg 1 captureStage.frag badAfterCapture :=
  (compileProg 1 captureStage.frag badAfterCapture).get (by decide +kernel)

theorem third_source : badAfterCapture.run CaptureControls.afterCapture = .error .revert := by
  with_unfolding_all rfl

/-- Both prefix successes are required before the third failure. The middle
capture has physically occurred, as the ordered prefix control below proves. -/
theorem third_reached (tail : List Word) :
    run (allocationStage.code ++ (captureStage.code ++ third.code))
      {initialMachine with stack := tail} = .revert := by
  have ad : MappedBoundaryLink (.memory allocationStage) (.memory captureStage)
      1 7 initialBase (State.init C) {initialMachine with stack := tail} :=
    memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel)
  have de : ReachedMappedLink (.memory allocationStage) (.memory captureStage) (.memory third)
      1 7 initialBase (State.init C) {initialMachine with stack := tail} := by
    intro o mid mb _ _ _
    exact memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel)
  exact (compilation_triple_revert_iff (.memory allocationStage) (.memory captureStage)
    (.memory third) (compilation_input_stack (.memory allocationStage) prefix_input7 tail)
    ad de rfl rfl rfl).mpr (.inr ⟨_, ReachabilityControls.fresh_state_reaches_fixture,
      .inr ⟨_, capture_source, .inl third_source⟩⟩)

/-- Intrinsic joined executions fail at the reached second/third positions. -/
theorem joined_sources :
    (ReachabilityControls.populatedBuilder.join (CompileExamples.badRhsRead.join captureProg)).run
      (State.init C) = .error .revert ∧
    (ReachabilityControls.populatedBuilder.join (captureProg.join badAfterCapture)).run
      (State.init C) = .error .revert := by
  have hb : (CompileExamples.badRhsRead.join captureProg).run σ = .error .revert := by
    rw [DeferredSource.join_run]
    simp only [TRun.seq, LinkedControls.right_stage_source_revert]
  have hc : (captureProg.join badAfterCapture).run σ = .error .revert := by
    rw [DeferredSource.join_run]
    simp only [TRun.seq, capture_source, third_source, Except.map]
  constructor
  · rw [DeferredSource.join_run]
    simp only [TRun.seq, ReachabilityControls.fresh_state_reaches_fixture, hb, Except.map]
  · rw [DeferredSource.join_run]
    simp only [TRun.seq, ReachabilityControls.fresh_state_reaches_fixture, hc, Except.map]

private def cell (n : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem n with | .val w => some w.val | _ => none
  | _ => none
private def prefixCode := allocationStage.code ++ captureStage.code
private theorem saved : cell 4 (run prefixCode initialMachine) = some 7 := by decide +kernel
private theorem mutated : cell 17 (run prefixCode initialMachine) = some 8 := by decide +kernel
private theorem cursor : cell 0 (run prefixCode initialMachine) = some 21 := by decide +kernel
private theorem alias1 : cell 2 (run prefixCode initialMachine) = some 16 := by decide +kernel
private theorem alias2 : cell 3 (run prefixCode initialMachine) = some 16 := by decide +kernel
private theorem other : cell 1 (run prefixCode initialMachine) = some 19 := by decide +kernel
private theorem otherValue : cell 20 (run prefixCode initialMachine) = some 4 := by decide +kernel

theorem ordered_prefix : [4, 17, 2, 3, 1, 20, 0].mapM
    (fun n => cell n (run prefixCode initialMachine)) = some [7, 8, 16, 16, 19, 4, 21] := by
  simp only [List.mapM_cons, List.mapM_nil, saved, mutated, cursor, alias1, alias2, other, otherValue]
  rfl

end Solidity.Backend.Passes.TripleFailures
