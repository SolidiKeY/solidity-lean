import Solidity.Lowering.Readonly.SourceSequenceEffects
import Solidity.Source.SemanticsExamples

/-! Actual ordered local effects under both pipelines, plus an inhabited
smaller-bound induction client. These are Source runs, not target/native runs. -/
namespace Solidity.Lowering.Readonly.SourceSequenceControls
open Solidity.Source Solidity.Source.SemanticsExamples
open SourceHistory

def first : RExpr E0 [uint] uint := .incDec true true (.local .here)
def second : RExpr E0 [uint] uint := .local .here
def arguments : RArgs E0 [uint] [uint,uint] := .cons first (.cons second .nil)
def convertedArguments : RConvArgs E0 [uint] [uint,uint] :=
  .cons first (by decide) (.cons second (by decide) .nil)
def frame : Fr := {F0 with static := true}
def paired (pipeline : Solidity.Roadmap.Pipeline) :=
  (evalPair (G0 pipeline) frame 10 first second).run (l1, (s0 : St E0))
def forward (pipeline : Solidity.Roadmap.Pipeline) :=
  (evalArgs (G0 pipeline) frame 10 arguments).run (l1, (s0 : St E0))
def reverse (pipeline : Solidity.Roadmap.Pipeline) :=
  (evalArgsRev (G0 pipeline) frame 10 arguments).run (l1, (s0 : St E0))
def converted (pipeline : Solidity.Roadmap.Pipeline) :=
  (evalConvArgs (G0 pipeline) frame 10 convertedArguments).run (l1, (s0 : St E0))
def emptyArgs := (evalArgs (G0 .legacy) frame 1 (RArgs.nil : RArgs E0 [uint] [])).run (l1, (s0 : St E0))
def exhausted := (evalArgs (G0 .legacy) frame 1 arguments).run (l1, (s0 : St E0))

theorem observations : (Solidity.Lowering.Readonly.SourceSequenceControls.paired .legacy).1 = .ok (.val (.int 2 (by decide)), .val (.int 1 (by decide))) ∧
 (Solidity.Lowering.Readonly.SourceSequenceControls.paired .viaIR).1 = .ok (.val (.int 2 (by decide)), .val (.int 2 (by decide))) ∧
 (Solidity.Lowering.Readonly.SourceSequenceControls.forward .legacy).1 = .ok (.cons (.val (.int 2 (by decide))) (.cons (.val (.int 2 (by decide))) .nil)) ∧
 (Solidity.Lowering.Readonly.SourceSequenceControls.forward .viaIR).1 = .ok (.cons (.val (.int 2 (by decide))) (.cons (.val (.int 2 (by decide))) .nil)) ∧
 (Solidity.Lowering.Readonly.SourceSequenceControls.reverse .legacy).1 = .ok (.cons (.val (.int 2 (by decide))) (.cons (.val (.int 1 (by decide))) .nil)) ∧
 (Solidity.Lowering.Readonly.SourceSequenceControls.converted .legacy).1 = .ok (.cons (.int 2 (by decide)) (.cons (.int 2 (by decide)) .nil)) ∧
 (Solidity.Lowering.Readonly.SourceSequenceControls.paired .legacy).2.1 = .cons (.int 2 (by decide)) .nil ∧
 (Solidity.Lowering.Readonly.SourceSequenceControls.paired .viaIR).2.1 = .cons (.int 2 (by decide)) .nil ∧
 (Solidity.Lowering.Readonly.SourceSequenceControls.paired .legacy).2.2.ex = (Solidity.Source.SemanticsExamples.s0 : Solidity.Source.St Solidity.Source.SemanticsExamples.E0).ex ∧
 Solidity.Lowering.Readonly.SourceSequenceControls.emptyArgs.1 = .ok .nil ∧
 Solidity.Lowering.Readonly.SourceSequenceControls.emptyArgs.2.1 = Solidity.Source.SemanticsExamples.l1 ∧
 Solidity.Lowering.Readonly.SourceSequenceControls.exhausted.1 = .error .timeout ∧
 Solidity.Lowering.Readonly.SourceSequenceControls.exhausted.2.1 = Solidity.Source.SemanticsExamples.l1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

theorem empty_client : ∀ pipeline, Solidity.Lowering.Readonly.SourceHistory.Effect Solidity.Lowering.Readonly.SourceSequenceControls.frame.static
 (Solidity.Source.evalArgs (Solidity.Source.SemanticsExamples.G0 pipeline) Solidity.Lowering.Readonly.SourceSequenceControls.frame 1
 (Solidity.Source.RArgs.nil : Solidity.Source.RArgs Solidity.Source.SemanticsExamples.E0 [Solidity.Source.SemanticsExamples.uint] [])) := by
  intro pipeline
  exact Solidity.Lowering.Readonly.SourceHistory.evalArgs_succ (Solidity.Source.SemanticsExamples.G0 pipeline)
    Solidity.Lowering.Readonly.SourceSequenceControls.frame 0
    (Solidity.Lowering.Readonly.SourceHistory.at_zero (Solidity.Source.SemanticsExamples.G0 pipeline)) .nil

theorem viaIR_arguments : (Solidity.Lowering.Readonly.SourceSequenceControls.reverse .viaIR).1 = .ok (.cons (.val (.int 2 (by decide))) (.cons (.val (.int 1 (by decide))) .nil)) ∧
 (Solidity.Lowering.Readonly.SourceSequenceControls.converted .viaIR).1 = .ok (.cons (.int 2 (by decide)) (.cons (.int 2 (by decide)) .nil)) := by
  exact ⟨rfl, rfl⟩

end Solidity.Lowering.Readonly.SourceSequenceControls
