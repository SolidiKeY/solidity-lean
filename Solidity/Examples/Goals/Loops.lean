import Solidity.Goals.Loops
import Solidity.Correctness.Lowering.Total.Main

namespace Solidity.Goals

/--
info: unstated Solidity.Goals.lowerLoopsCorrect ← Solidity.Correctness.Lowering.lowerLoops_correct plan e1-loops
-/
#guard_msgs in
#roadmap_goal lowerLoopsCorrect

/--
info: open Solidity.Goals.loweringStudyTarget ← Solidity.Correctness.Lowering.lowerLoops_correct blocked by [Solidity.Goals.lowerLoopsCorrect] plan pa-lowering
-/
#guard_msgs in
#roadmap_goal loweringStudyTarget

/-- The local production contract is exactly the dedicated roadmap goal. -/
example :
    (∀ [FreshNames],
      LowerKernel.Fix lowerList lowerStmt lowerLoop ∧
      (∃ (μL : List RawStmt → Nat) (μS μP : RawStmt → Nat),
        LowerKernel.Contractive μL μS μP) ∧
      LowerKernel.Helpers) = Solidity.Goals.loweringKernelTotal := rfl

example : Solidity.Goals.loweringKernelTotal := Solidity.lowerKernel_total

/--
info: proved Solidity.Goals.loweringKernelTotal ← Solidity.lowerKernel_total plan e2a-lower-total
-/
#guard_msgs in
#roadmap_goal loweringKernelTotal

/-! ### The loop contract (e2b-loops-producer)

`lowerLoopsCorrect` stays unstated: no concrete boundary is bound. These pin
what is proved about the contract at every boundary. -/

section Contract

open Solidity.Correctness.Lowering Solidity.Correctness.Lowering.Total

/-- The production and family conjuncts are discharged at every boundary. -/
example (b : SemanticBoundary) (i : RawSourceInterpretation)
    (decode : Request → Option SourceProgram) :
    LowerLoopsCorrectContract b i decode ↔ Faithful b i ∧ Residual b decode :=
  contract_iff b i decode

example (b : SemanticBoundary) (decode : Request → Option SourceProgram) :
    LowerLoopsCorrectContract b b.reference decode ↔ Residual b decode :=
  contract_reference_iff b decode

/-- Negative control: the contract alone admits an empty boundary. -/
example (b : SemanticBoundary) (decode : Request → Option SourceProgram)
    (empty : ∀ r, ¬ b.reference.entry r) (normal : RelatesNormalFamily b)
    (returns : RelatesReturnFamily b) : LowerLoopsCorrectContract b b.reference decode :=
  (contract_reference_iff b decode).mpr (Residual.of_empty b decode empty normal returns)

/-- With `FullDomain`, a successful top-level pipeline is in `LowersTo` and has
its decoded, associated, related and refined Source program. -/
example (b : SemanticBoundary) (decode : Request → Option SourceProgram)
    (h : LowerLoopsCorrectContract b b.reference decode) (full : FullDomain b)
    (C : Contract) (input : ProductionInput) (o : ProductionOutput) (after : Checker.Snapshot)
    (parts : SProg C) (program : Blk C input.caller.ctx)
    (run : SuccessfulLoopPipeline input o C after parts program) :
    @LowersTo input.names input.returnSlots input.raw o.raw input.scope input.before o.after ∧
    ∃ s, decode ⟨C, input, none⟩ = some s ∧ b.relates s program :=
  have p := production_correct ((contract_reference_iff b decode).mp h) full ⟨C, input, none⟩ o
    after parts program run
  ⟨p.1 rfl, p.2.2.elim fun s q => ⟨s, q.1, q.2.2.1⟩⟩

/-- An admitted request has at most one associated Source program. -/
example (b : SemanticBoundary) (decode : Request → Option SourceProgram)
    (h : Residual b decode) (r : Request) (s s' : SourceProgram) (e : b.reference.entry r)
    (a : b.reference.associated r s) (a' : b.reference.associated r s') : s = s' :=
  h.associated_unique e a a'

end Contract

end Solidity.Goals
