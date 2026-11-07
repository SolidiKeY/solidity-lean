import Solidity.Backend.Passes.StatefulCaptureControls

/-! Guard a fabricated post-capture representation, skipped capture effects,
or conflating the scalar numeric packet with symbolic expression execution.
Derive the actual declaration Input through the existing generic memory link. -/
namespace Solidity.Backend.Passes.AuditStatefulCapture
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.Passes
open Backend.Passes.Controls.Fixture
open ValueSequenceControls StatefulValueControls StatefulCaptureControls

theorem joint :
    (Compilation.memory captureCompiled).Input 1 6 base σ machine ∧
    captureProgram.run σ = .ok ⟨CaptureControls.afterCapture,List.prefix_refl _⟩ ∧
    declaration.run CaptureControls.afterCapture =
      .ok ⟨CaptureControls.afterCapture.push four,List.prefix_refl _⟩ ∧
    (∃ (mid : Machine) (selected : Nat → Fin W),
      MappedOutput (.memory captureCompiled) 1 6 base σ machine CaptureControls.afterCapture mid selected ∧
      (Compilation.memory declarationCompiled).Input 1 6 selected CaptureControls.afterCapture mid) := by
  refine ⟨StatefulCaptureControls.initial_input, StatefulCaptureControls.capture_source,
    StatefulCaptureControls.declaration_source, ?_⟩
  obtain ⟨mb, ob, mid, final, word, ha, _, _, ma, _⟩ := StatefulCaptureControls.reached_application
  have link : MappedBoundaryLink (.memory captureCompiled) (.memory declarationCompiled)
      1 6 base σ machine :=
    memory_nonallocating_mapped_link captureCompiled declarationCompiled
      (by decide +kernel) (by decide +kernel)
  have input := link ⟨CaptureControls.afterCapture,List.prefix_refl _⟩ mid mb
    StatefulCaptureControls.capture_source ha ma
  refine ⟨mid, mb, ma, ?_⟩
  simpa only [show Evm.Prog.pushes captureProgram = 0 by decide +kernel,Nat.add_zero] using input
def capture_source := @Solidity.Backend.Passes.StatefulCaptureControls.capture_source
def declaration_source := @Solidity.Backend.Passes.StatefulCaptureControls.declaration_source
def initial_input := @Solidity.Backend.Passes.StatefulCaptureControls.initial_input
def reached_application := @Solidity.Backend.Passes.StatefulCaptureControls.reached_application
def ordered_capture := @Solidity.Backend.Passes.StatefulCaptureControls.ordered_capture
def ordered_without_capture := @Solidity.Backend.Passes.StatefulCaptureControls.ordered_without_capture

/-- info: 'Solidity.Backend.Passes.AuditStatefulCapture.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditStatefulCapture.joint

/-- info: 'Solidity.Backend.Passes.AuditStatefulCapture.capture_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditStatefulCapture.capture_source

/-- info: 'Solidity.Backend.Passes.AuditStatefulCapture.declaration_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditStatefulCapture.declaration_source

/-- info: 'Solidity.Backend.Passes.AuditStatefulCapture.initial_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditStatefulCapture.initial_input

/-- info: 'Solidity.Backend.Passes.AuditStatefulCapture.reached_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditStatefulCapture.reached_application

/-- info: 'Solidity.Backend.Passes.AuditStatefulCapture.ordered_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditStatefulCapture.ordered_capture

/-- info: 'Solidity.Backend.Passes.AuditStatefulCapture.ordered_without_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditStatefulCapture.ordered_without_capture
end Solidity.Backend.Passes.AuditStatefulCapture
