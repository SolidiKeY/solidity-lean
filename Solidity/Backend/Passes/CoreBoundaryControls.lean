import Solidity.Backend.Passes.CoreBoundary
import Solidity.Backend.Passes.RevertControls

/-! Actual allocation/capture followed by a nonidentity core declaration,
and asserting panic. Complete physical prefix relations remain available. -/
namespace Solidity.Backend.Passes.CoreBoundaryControls
open Solidity.Evm Solidity.Evm.Compiler Solidity.Evm.Memory
open Solidity.Backend.Passes.Controls.Fixture
open Solidity.Backend.Passes.AllocatingControls
open Solidity.Backend.Passes.TripleControls

def suffixProg : Prog C Γ (.val .uint :: Γ) :=
  .cons (.declLocal .uint (.user "coreAfter") (some (.simple (.lit 11 rfl)))) .nil
def suffixCert : inFragP captureStage.frag suffixProg =
    some (captureStage.frag.push (.val .uint) .ok) := by decide +kernel
def suffix : Compilation 1 captureStage.frag suffixProg :=
  .core _ suffixCert

theorem suffix_source : suffixProg.run CaptureControls.afterCapture =
    .ok ⟨CaptureControls.afterCapture.push (t := .val .uint) (CompileExamples.uint 11 (by decide)),
      List.prefix_refl _⟩ := by with_unfolding_all rfl

theorem suffix_run (m : Machine) : run suffix.code m =
    .ok (writeMachine m 5 w[11]) 0 := by rfl

theorem physical_link (tail : List Word) :
    ReachedMappedLink (.memory allocationStage) (.memory captureStage) suffix
      1 7 initialBase (State.init C) {initialMachine with stack := tail} := by
  intro o mid mb _ _ _
  exact compilation_core_mapped_link (.memory captureStage) suffixCert (by decide +kernel)

/-- Both full prefix outputs and the original third Input are retained;
the terminal relation is only the actual core Sim, not heap preservation. -/
theorem reached_success (tail : List Word) :
    ∃ (mb nb : Nat → Fin W) (mid next : Machine),
      run allocationStage.code {initialMachine with stack := tail} = .ok mid 0 ∧
      run captureStage.code mid = .ok next 0 ∧
      MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
        {initialMachine with stack := tail} σ mid mb ∧
      MappedOutput (.memory captureStage) 1 7 mb σ mid CaptureControls.afterCapture next nb ∧
      suffix.Input 1 7 nb CaptureControls.afterCapture next ∧
      run (allocationStage.code ++ (captureStage.code ++ suffix.code))
        {initialMachine with stack := tail} = .ok (writeMachine next 5 w[11]) 0 ∧
      (writeMachine next 5 w[11]).stack = tail ∧
      Sim C 1 1 suffix.frag
        (CaptureControls.afterCapture.push (t := .val .uint) (CompileExamples.uint 11 (by decide)))
        (writeMachine next 5 w[11]) := by
  have ad : MappedBoundaryLink (.memory allocationStage) (.memory captureStage)
      1 7 initialBase (State.init C) {initialMachine with stack := tail} :=
    memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel)
  obtain ⟨mb, nb, ob, mid, next, final, hm, hn, hf, _, hall, hs, ha, hd, he⟩ :=
    compilation_triple_success (.memory allocationStage) (.memory captureStage) suffix
      (compilation_input_stack (.memory allocationStage) prefix_input7 tail) ad (physical_link tail)
      rfl rfl rfl ReachabilityControls.fresh_state_reaches_fixture capture_source suffix_source
  have eq : final = writeMachine next 5 w[11] :=
    (Evm.Out.ok.inj (hf.symm.trans (suffix_run next))).1
  cases eq
  have hi := (physical_link tail) _ _ _ ReachabilityControls.fresh_state_reaches_fixture hm ha
    _ _ _ capture_source hn hd
  exact ⟨mb, nb, mid, next, hm, hn, ha, hd, hi, hall, hs, mapped_output_core suffix he⟩

theorem panic_link (tail : List Word) :
    ReachedMappedLink (.memory allocationStage) (.memory captureStage) RevertControls.panicStage
      1 7 initialBase (State.init C) {initialMachine with stack := tail} := by
  intro o mid mb _ _ _
  exact compilation_core_mapped_link (.memory captureStage)
    (G := captureStage.frag) (by rfl) (by decide +kernel)

theorem reached_asserting_panic (tail : List Word) :
    RevertControls.panicProg.asserts = true ∧
    RevertControls.panicProg.run CaptureControls.afterCapture = .error .panic ∧
    run (allocationStage.code ++ (captureStage.code ++ RevertControls.panicStage.code))
      {initialMachine with stack := tail} = .revert := by
  refine ⟨rfl, rfl, ?_⟩
  exact (compilation_triple_revert_iff (.memory allocationStage) (.memory captureStage)
    RevertControls.panicStage (compilation_input_stack (.memory allocationStage) prefix_input7 tail)
    (memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel))
    (panic_link tail) rfl rfl rfl).mpr (.inr ⟨_, ReachabilityControls.fresh_state_reaches_fixture,
      .inr ⟨_, capture_source, .inr RevertControls.panic_source⟩⟩)

private def cell (n : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem n with | .val w => some w.val | _ => none
  | _ => none
def code : List Instr := allocationStage.code ++ (captureStage.code ++ suffix.code)
private theorem c5 : cell 5 (run code initialMachine) = some 11 := by decide +kernel
private theorem c4 : cell 4 (run code initialMachine) = some 7 := by decide +kernel
private theorem c2 : cell 2 (run code initialMachine) = some 16 := by decide +kernel
private theorem c3 : cell 3 (run code initialMachine) = some 16 := by decide +kernel
private theorem c1 : cell 1 (run code initialMachine) = some 19 := by decide +kernel
private theorem c17 : cell 17 (run code initialMachine) = some 8 := by decide +kernel
private theorem c18 : cell 18 (run code initialMachine) = some 9 := by decide +kernel
private theorem c20 : cell 20 (run code initialMachine) = some 4 := by decide +kernel
private theorem c0 : cell 0 (run code initialMachine) = some 21 := by decide +kernel

theorem ordered_observations : [5,4,2,3,1,17,18,20,0].mapM
    (fun n => cell n (run code initialMachine)) = some [11,7,16,16,19,8,9,4,21] := by
  simp only [List.mapM_cons, List.mapM_nil, c5, c4, c2, c3, c1, c17, c18, c20, c0]
  rfl

/-- Independent joined intrinsic executions, not target-as-source. -/
theorem source_associations :
    ((ReachabilityControls.populatedBuilder.join captureProg).join suffixProg).run (State.init C) =
      .ok ⟨CaptureControls.afterCapture.push (t := .val .uint) (CompileExamples.uint 11 (by decide)),
        ⟨σ.H, rfl⟩⟩ ∧
    (ReachabilityControls.populatedBuilder.join (captureProg.join suffixProg)).run (State.init C) =
      .ok ⟨CaptureControls.afterCapture.push (t := .val .uint) (CompileExamples.uint 11 (by decide)),
        ⟨σ.H, rfl⟩⟩ :=
  triple_source_success (State.init C) ReachabilityControls.fresh_state_reaches_fixture
    capture_source suffix_source

private def skipped : List Instr := allocationStage.code ++ suffix.code
private theorem s5 : cell 5 (run skipped initialMachine) = some 11 := by decide +kernel
private theorem s4 : cell 4 (run skipped initialMachine) = some 0 := by decide +kernel
private theorem s2 : cell 2 (run skipped initialMachine) = some 16 := by decide +kernel
private theorem s3 : cell 3 (run skipped initialMachine) = some 16 := by decide +kernel
private theorem s1 : cell 1 (run skipped initialMachine) = some 19 := by decide +kernel
private theorem s17 : cell 17 (run skipped initialMachine) = some 7 := by decide +kernel
private theorem s18 : cell 18 (run skipped initialMachine) = some 9 := by decide +kernel
private theorem s20 : cell 20 (run skipped initialMachine) = some 4 := by decide +kernel
private theorem s0 : cell 0 (run skipped initialMachine) = some 21 := by decide +kernel

/-- Skipping the actual capture effect changes the COMPLETE observation. -/
theorem skipped_effect : [5,4,2,3,1,17,18,20,0].mapM
    (fun n => cell n (run skipped initialMachine)) = some [11,0,16,16,19,7,9,4,21] ∧
    ([11,0,16,16,19,7,9,4,21] : List Nat) ≠ [11,7,16,16,19,8,9,4,21] := by
  constructor
  · simp only [List.mapM_cons, List.mapM_nil, s5, s4, s2, s3, s1, s17, s18, s20, s0]
    rfl
  · decide

/-- A real accepted typed storage push still requires its original bound;
no malformed instruction or artificial source failure is involved. -/
def ResourceC : Contract := contract!{ uint[] values; }
def resourceProg : Prog ResourceC [] [] :=
  .cons (.push (.loc (.root "values" rfl)) none rfl) .nil
def resourceCert : inFragP (Frag.init []) resourceProg = some (Frag.init []) := rfl
def resourceStage : Compilation 0 (Frag.init []) resourceProg := .core _ resourceCert

theorem resource_guard (m : Machine) :
    ¬ resourceStage.Input Lmax 0 initialBase (State.init ResourceC) m :=
  core_input_refused resourceCert (by change Lmax < Lmax + 1; omega)

/-- The independent intrinsic push succeeds at the actual empty store;
the rejected Input above is its original resource guard, not source failure. -/
theorem resource_source_success :
    (resourceProg.run (State.init ResourceC)).toOption.isSome = true := by decide +kernel

theorem resource_recognized :
    (Compiler.compile 0 (Frag.init []) resourceProg).isSome = true := rfl

end Solidity.Backend.Passes.CoreBoundaryControls
