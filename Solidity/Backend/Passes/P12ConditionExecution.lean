import Solidity.Backend.Passes.DeferredCondition
import Solidity.Lowering.V07.P12NextInterface

/-! Consume the published request-specific P12 condition contract. The Source
producer, origins and admission remain explicit obligations; no instance is
manufactured here. The receiving compilation reads before dropping temporaries. -/
namespace Solidity.Backend.Passes.P12ConditionExecution
open Evm Evm.Memory Evm.Compiler Lowering.V07 Lowering.V07.P12NextInterface

theorem success {E : Source.Env} {C : Contract} {srcΓ : Source.RCtx} {Γ : Ctx}
    (G : Source.Glob E) (SF : Source.Fr) (m : ContextMap srcΓ Γ)
    (values : ValueRelation E C) (worlds : WorldRelation E C)
    (expr : Source.RExpr E srcΓ .bool)
    (condition : Condition G SF m values worlds expr)
    {b L frame : Nat} {F : Frag Γ}
    (code : CompiledProg b F condition.operand.code)
    (reader : CompiledVal b code.frag (DeferredCondition.expression condition.operand))
    (fuel : Nat) (source after : Source.EMState E srcΓ) (target : State C Γ) (choice : Bool)
    (aligned : Aligned m values worlds source target)
    (evaluated : (Source.evalE G SF fuel expr).run source = (.ok (.val (.bool choice)),after))
    {base : Nat → Fin W} {machine : Machine}
    (input : (Compilation.memory code).Input L frame base target machine)
    (free : Evm.Prog.pays condition.operand.code = false) :
    ∃ (out : Out C target.H Γ) (native : condition.operand.run target = .ok (out,.prim choice)),
      Aligned m values worlds after out.st ∧ type_of%
        (DeferredCondition.shared condition.operand code reader input free out choice native) := by
  obtain ⟨out,native,reached⟩ := condition.success fuel source after target choice aligned evaluated
  exact ⟨out,native,reached,
    DeferredCondition.shared condition.operand code reader input free out choice native⟩

end Solidity.Backend.Passes.P12ConditionExecution

/-- info: 'Solidity.Backend.Passes.P12ConditionExecution.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.P12ConditionExecution.success
