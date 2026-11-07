import Solidity.Backend.Selection.CompositionControls
import Solidity.Backend.Selection.PremisesV2

/-! Joint global-premise/input witness for the frozen runtime consumer's
antecedents. Uses the published nonidentity 70-byte artifact and actual IR run.
The decoder is the existing local self-adapter, not external Bridge agreement.
The closed consumer below is an audit fixture, not a general G49 theorem or source-wide coverage.
-/
namespace Solidity.H62.BytecodeSelection.RuntimeFixture
open Backend Backend.Selection

def relation (_ : Unit) (initial final : Evm.Machine) : Prop :=
  initial.stack = irStack [23] ∧ final = {initial with stack := irStack [5,23]}

def initial : Evm.Machine := {Evm.Machine.init with stack := irStack [23]}

def compiler : V2.CompilerPremise Unit (fun _ => ()) MixedControls.sampleIR relation where
  inhabited := ⟨0, initial, {initial with stack := irStack [5,23]}, rfl, rfl⟩
  preserves := by
    intro _ start finish related
    have stack : start.stack = irStack [23] := related.1
    rw [related.2]
    exact CompositionControls.source_run start stack

/-- Compiler and decoder structures, composition and all per-input antecedents
coexist for the SAME nonidentity artifact, with actual successful IR execution. -/
theorem runtime_antecedents_jointWitness :
    ∃ (composition : CompositionCertificate MixedControls.sampleIR
          (.code CompositionControls.code.instructions) 1 2)
      (_compiler : V2.CompilerPremise Unit (fun _ => ()) MixedControls.sampleIR relation)
      (_decoder : DecoderPremise (encode composition.assembled.code) 1
        (LabelExec.step (encode composition.assembled.code))
        (fun count => LabelExec.advance count (encode composition.assembled.code))
        (fun _ => True))
      (budget : Nat) (m : Evm.Machine) (s t : Scalar.Stack),
      s.length = 1 ∧ m.stack = irStack s ∧
      relation ((fun _ : Nat => ()) budget) m {m with stack := irStack t} ∧
      Evm.run MixedControls.sampleIR m = .ok {m with stack := irStack t} 0 := by
  exact ⟨CompositionControls.composition, compiler, CompositionControls.identityDecoder,
    0, initial, [23], [5,23], rfl, rfl, ⟨rfl, rfl⟩,
    CompositionControls.source_run initial rfl⟩

/-- Independently observable actual fetched-byte success for the same artifact.
This is finite local execution, not charged gas/fork or source adequacy. -/
theorem actual_nonidentity_bytes :
    LabelExec.advance 6 (encode CompositionControls.composition.assembled.code)
      ⟨0,[23]⟩ = some ⟨70,[5,23]⟩ := CompositionControls.actual_bytes

/-- One closed consumer witnesses the projection self binder. Its unchanged
compiler/decoder antecedents remain quantified; actual behavior is supplied by
the existing fixed-artifact control, not by a new general G49 proof. -/
def consumer : V2.RuntimeConsumer Unit (fun _ => ()) MixedControls.sampleIR relation
    (.code CompositionControls.code.instructions) 1 2 CompositionControls.composition
    (LabelExec.step (encode CompositionControls.composition.assembled.code))
    (fun count => LabelExec.advance count (encode CompositionControls.composition.assembled.code))
    (fun _ => True) where
  inhabited := ⟨0, initial, [23], [5,23], rfl, rfl, ⟨rfl, rfl⟩,
    CompositionControls.source_run initial rfl⟩
  consume := by
    intro _ _ _ m s t _ stack related
    have input : s = [23] := irStack_injective (stack.symm.trans related.1)
    have output : t = [5,23] := irStack_injective (congrArg Evm.Machine.stack related.2)
    subst s
    subst t
    simpa only [CompositionControls.size_seventy] using
      CompositionControls.conditional_transport m related.1

/-- All projection hypotheses, including the consumer self binder, coexist.
This is exactly one closed local-adapter fixture, not an external-EVM result. -/
theorem runtime_projection_jointWitness :
    ∃ (_consumer : V2.RuntimeConsumer Unit (fun _ => ()) MixedControls.sampleIR relation
        (.code CompositionControls.code.instructions) 1 2 CompositionControls.composition
        (LabelExec.step (encode CompositionControls.composition.assembled.code))
        (fun count => LabelExec.advance count (encode CompositionControls.composition.assembled.code))
        (fun _ => True))
      (_compiler : V2.CompilerPremise Unit (fun _ => ()) MixedControls.sampleIR relation)
      (_decoder : DecoderPremise (encode CompositionControls.composition.assembled.code) 1
        (LabelExec.step (encode CompositionControls.composition.assembled.code))
        (fun count => LabelExec.advance count (encode CompositionControls.composition.assembled.code))
        (fun _ => True))
      (budget : Nat) (m : Evm.Machine) (s t : Scalar.Stack),
      s.length = 1 ∧ m.stack = irStack s ∧
      relation ((fun _ : Nat => ()) budget) m {m with stack := irStack t} := by
  exact ⟨consumer, compiler, CompositionControls.identityDecoder,
    0, initial, [23], [5,23], rfl, rfl, ⟨rfl, rfl⟩⟩

#print axioms consumer
#print axioms runtime_projection_jointWitness
#print axioms compiler
#print axioms runtime_antecedents_jointWitness
#print axioms actual_nonidentity_bytes
end Solidity.H62.BytecodeSelection.RuntimeFixture
