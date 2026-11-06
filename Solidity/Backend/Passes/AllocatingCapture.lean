import Solidity.Backend.Passes.MappedTail
import Solidity.Backend.Passes.CaptureControls
import Solidity.Backend.Passes.AllocatingControls

/-! Actual allocation followed by capture and typed reference-context
extension. Both selected maps and allocator growth are uniform over tails. -/
namespace Solidity.Backend.Passes.AllocatingCapture
open Solidity.Evm Solidity.Evm.Memory Solidity.Evm.Compiler
open Solidity.Backend.Passes.Controls.Fixture
open Solidity.Backend.Passes.AllocatingControls

def captureAlias : Prog C Γ (.mem (.array (.prim .uint)) :: Γ) :=
  .cons CaptureControls.capture (.cons CaptureControls.aliasStmt .nil)

theorem capture_source : captureAlias.run σ =
    .ok ⟨CaptureControls.afterAlias, List.prefix_refl _⟩ := by
  have ha : CaptureControls.aliasStmt.run CaptureControls.afterCapture =
      .ok ⟨CaptureControls.afterAlias, List.prefix_refl _⟩ := by with_unfolding_all rfl
  rw [captureAlias, Prog.run_cons_ok CaptureControls.source_capture,
    Prog.run_cons_ok ha, Prog.run_nil]
  rfl

def suffix : CompiledProg 1 allocationStage.frag captureAlias :=
  (compileProg 1 allocationStage.frag captureAlias).get (by decide +kernel)

theorem actual_link (tail : List Word) :
    MappedBoundaryLink (.memory allocationStage) (.memory suffix) 1 6 initialBase
      (State.init C) {initialMachine with stack := tail} :=
  memory_nonallocating_mapped_link allocationStage suffix (by decide +kernel) (by decide +kernel)

theorem fresh_source :
    (ReachabilityControls.populatedBuilder.join captureAlias).run (State.init C) =
      .ok ⟨CaptureControls.afterAlias, ⟨σ.H, rfl⟩⟩ := by
  rw [DeferredSource.join_run]
  simp only [TRun.seq, ReachabilityControls.fresh_state_reaches_fixture, capture_source, Except.map]

/-- Actual target prefix and suffix executions retain fixed maps, both
complete mapped relations, old live identities and five-cell growth at every
saved tail. Neither intermediate equality nor preservation is a premise. -/
theorem shared_maps :
    ∃ (mid final : Machine) (midBase outBase : Nat → Fin W),
      mid.stack = [] ∧ final.stack = [] ∧
      outBase CompileExamples.r0.id = midBase CompileExamples.r0.id ∧
      outBase CompileExamples.r1.id = midBase CompileExamples.r1.id ∧
      ∀ tail,
        run allocationStage.code {initialMachine with stack := tail} =
          .ok {mid with stack := tail} 0 ∧
        run (allocationStage.code ++ suffix.code) {initialMachine with stack := tail} =
          .ok {final with stack := tail} 0 ∧
        MappedOutput (.memory allocationStage) 1 6 initialBase (State.init C)
          {initialMachine with stack := tail} σ {mid with stack := tail} midBase ∧
        MappedOutput (.memory suffix) 1 6 midBase σ {mid with stack := tail}
          CaptureControls.afterAlias {final with stack := tail} outBase ∧
        GrowsAllocator 1 6 5 (State.init C) initialBase
          {initialMachine with stack := tail} CaptureControls.afterAlias outBase
          {final with stack := tail} := by
  obtain ⟨mb, mid, hp, hmid, hm⟩ :=
    memory_mapped_success allocationStage prefix_input ReachabilityControls.fresh_state_reaches_fixture
  have hi := actual_link [] _ _ _ ReachabilityControls.fresh_state_reaches_fixture hp hm
  obtain ⟨ob, final, ht, hfinal, hr⟩ := memory_mapped_success suffix hi capture_source
  have hmid' : mid.stack = [] := hmid
  have hfinal' : final.stack = [] := hfinal.trans hmid
  have hm' : MappedOutput (.memory allocationStage) 1 6 initialBase (State.init C)
      initialMachine σ mid mb := by
    simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using hm
  have hr' : MappedOutput (.memory suffix) 1 6 mb σ mid CaptureControls.afterAlias final ob := by
    simpa only [allocationStage.cert.pushes_zero, suffix.cert.pushes_zero, Nat.add_zero] using hr
  have hall : run (allocationStage.code ++ suffix.code) initialMachine = .ok final 0 := by
    rw [run_append_ok hp]
    exact ht
  refine ⟨mid, final, mb, ob, hmid', hfinal', hr'.2.1 CompileExamples.r0,
    hr'.2.1 CompileExamples.r1, ?_⟩
  intro tail
  have ep := run_tail allocationStage.code initialMachine tail (by rw [hp]; intro h; cases h)
  have ef := run_tail (allocationStage.code ++ suffix.code) initialMachine tail
    (by rw [hall]; intro h; cases h)
  have ml := mapped_output_stack (.memory allocationStage) hm' tail tail
  have mr := mapped_output_stack (.memory suffix) hr' tail tail
  refine ⟨?_, ?_, ml, mr, ?_⟩
  · simpa only [hp, appendOut, appendTail, hmid', List.nil_append] using ep
  · simpa only [hall, appendOut, appendTail, hfinal', List.nil_append] using ef
  · have hz : suffix.cert.cost σ = 0 := by decide +kernel
    simpa only [reached_cost, hz, Nat.add_zero] using
      GrowsAllocator.comp ml.2.2 mr.2.2

private def cellValue (n : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem n with | .val w => some w.val | _ => none
  | _ => none

theorem ordered_results :
    [4, 5, 17, 0, 20].mapM
      (fun n => cellValue n (run (allocationStage.code ++ suffix.code) initialMachine)) =
      some [7, 16, 8, 21, 4] := by decide +kernel

end Solidity.Backend.Passes.AllocatingCapture
