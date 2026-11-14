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

end Solidity.Examples.Goals.LoopsProducer
