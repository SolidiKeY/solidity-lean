import Solidity.Correctness.Lowering.Total.Contract
import Solidity.Goals.Loops

/-! Interface regression checks. These do not claim production coverage or
bind the legacy goal before E2B. -/
namespace Solidity.Examples.Goals.LoopsProducer

open Solidity.Correctness.Lowering
open Total

/-- E2C does not change the legacy goal or its guard. -/
example : Solidity.Goals.lowerLoopsCorrect = Solidity.Goal.Unstated := rfl

/-- The new production equation agrees exactly with the existing receipt. -/
example [names : FreshNames] {E : Source.Env} {returns : List Source.STy}
    {modifier : Bool} {control : Source.SCtx} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} (input : Checker.Input E returns modifier control srcΓ)
    (output : Checker.Output C Γ) :
    SuccessfulProductionRun
      ⟨names, input.returnSlots, input.raw, input.scope, input.before⟩
      ⟨output.raw, output.afterLower⟩ = Checker.ProducerReceipt input output := rfl

/-- Intrinsic provenance retains the prior receipt's exact state and placement. -/
example [names : FreshNames] {C : Contract} {Γ : Ctx} (output : Checker.Output C Γ) :
    SuccessfulElaboration names C Γ output.elabScope output.beforeElab output.afterElab
      output.raw output.elaborated output.names output.program =
      Checker.ElaborationReceipt output := rfl

/-- Adversarial printer: disjoint strings still parse to one identity. -/
private def aliasNames : FreshNames where
  name _ _ := "brk1"
  parse _ := some ("brk", 1)

/-- A protected caller alias is refused even when its printed string differs. -/
example : ¬ SafeSpellings aliasNames ["caller"] [("brk", 1)] :=
  fun h => h.2.2 ("brk", 1) List.mem_cons_self "caller" List.mem_cons_self rfl

/-- The relational rules reproduce the frozen kernel equations exactly. -/
example [FreshNames] : listStep = Solidity.Goals.loweringKernelList := rfl
example [FreshNames] : stmtStep = Solidity.Goals.loweringKernelStmt := rfl
example [FreshNames] : Solidity.Correctness.Lowering.Total.loopStep = Solidity.Goals.loweringKernelLoop := rfl

/-- Empty input is in the relation at every complete initial state, not just a probe. -/
example [FreshNames] (sc : ElabScope) (st : Checker.Snapshot) : LowersTo none [] [] sc st st := ⟨1, rfl⟩

/-- Callee elaboration uses the actual inlining reader, not the incoming top-level reader. -/
example (C : Contract) (input : ProductionInput) (c : CalleeRequest) (o : ProductionOutput) :
    let sc := (Request.mk C input (some c)).elabScope o
    sc.top = false ∧ sc.unchecked = false ∧
      sc.inlined = List.cons (c.start, o.after.locals.2) input.scope.inlined := ⟨rfl, rfl, rfl⟩

/-- Consume the universal candidate for an arbitrary admitted successful pipeline.
The source is obtained from coverage, not supplied as a sample association.
The full pass certificate retains both forward and backward obligations. -/
theorem contract_pipeline (b : SemanticBoundary) (i : RawSourceInterpretation)
    (decode : Request → Option SourceProgram) (h : LowerLoopsCorrectContract b i decode)
    (r : Request) (o : ProductionOutput) (after : Checker.Snapshot)
    (parts : SProg r.contract) (program : Blk r.contract r.context.ctx)
    (entry : i.entry r) (pipeline : r.pipeline o after parts program) :
    ∃ s, decode r = some s ∧ b.reference.associated r s ∧ b.relates s program ∧
      Nonempty (Solidity.Roadmap.G49Final.PassCorrect
        (i.source s).behaviour (i.target program).behaviour) := by
  obtain ⟨s, associated⟩ := h.2.1.source r entry
  have decoded : decode r = some s := (h.2.1.decoder r s entry).mpr associated
  exact ⟨s, decoded, (h.2.1.association r s).mp associated,
    h.2.1.pipeline r o after parts program s entry decoded pipeline⟩

end Solidity.Examples.Goals.LoopsProducer
