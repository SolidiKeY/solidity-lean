import Solidity.Backend.Selection.InterfaceV2Controls

/-! Additive feasibility audit. Frozen interfaces are imported unchanged.
These statements cover only the declarations named below; no G49 instance.
-/
namespace Solidity.H62.BytecodeSelection
open Backend Backend.Selection

/-- All explicit hypotheses of V2.FrameCertificate.prefixes hold together. -/
theorem prefixes_jointWitness :
    ∃ (input output : Scalar.Stack) (c : V2.FrameCertificate input output)
      (tail : Scalar.Stack) (before after : Program) (reached : Scalar.Stack),
      (input ++ tail).length + c.peak ≤ 1024 ∧
      before ++ after = c.code ∧
      Scalar.run before (input ++ tail) = some reached := by
  exact ⟨[], [], V2.identityFrame [] (by decide), [], [], [], [], by decide, rfl, rfl⟩

/-- The premise of no_overfull_output is feasible; its conclusion is negative. -/
theorem no_overfull_output_jointWitness :
    ∃ (_input output : Scalar.Stack), 1024 < output.length := by
  exact ⟨[], List.replicate 1025 0, by simp only [List.length_replicate]; decide⟩

/-- Deliberate negative control: its simultaneous hypothesis domain is empty.
This is an obstruction certificate, never labeled a positive witness. -/
theorem reject_push_program_jointHypotheses_impossible :
    ¬ ∃ (input output : Scalar.Stack) (c : V2.FrameCertificate input output),
      c.code = List.replicate 1025 V2.Controls.zeroPush := by
  rintro ⟨input, output, c, bad⟩
  exact V2.Controls.reject_push_program c bad

/-- A globally inhabited producer AND an actual admitted numeric-height case.
The no-op fixture is not evidence of source-wide coverage or G49 composition. -/
theorem compiler_global_and_input_jointWitness :
    ∃ (_c : V2.CompilerPremise Unit (fun _ => ()) []
        (fun _ initial final => final = initial))
      (_budget : Nat) (m : Evm.Machine) (s t : Scalar.Stack),
      s.length = 0 ∧ m.stack = irStack s ∧
      { m with stack := irStack t } = m ∧
      Evm.run [] m = .ok { m with stack := irStack t } 0 := by
  exact ⟨V2.Controls.identityCompiler, 0, Evm.Machine.init, [], [], rfl, rfl, rfl, rfl⟩

/-- Reproduction of the legacy V1 empty-relation loophole, not a runtime proof.
This is an audit control and must never be used to supply a G49 producer. -/
theorem legacy_runtime_empty_relation (Observation : Type)
    (source : Nat → Observation) (ir : List Evm.Instr) (b : Block)
    (input output : Nat) (composition : CompositionCertificate ir b input output)
    (bridgeStep : LabelExec.State → Option LabelExec.State)
    (bridgeRun : Nat → LabelExec.State → Option LabelExec.State)
    (reachable : LabelExec.State → Prop) :
    RuntimeConsumer Observation source ir (fun _ _ _ => False) b input output
      composition bridgeStep bridgeRun reachable where
  consume := by
    intro _ _ _ _ _ _ _ _ impossible
    exact False.elim impossible

#print axioms legacy_runtime_empty_relation
#print axioms prefixes_jointWitness
#print axioms no_overfull_output_jointWitness
#print axioms reject_push_program_jointHypotheses_impossible
#print axioms compiler_global_and_input_jointWitness
end Solidity.H62.BytecodeSelection
