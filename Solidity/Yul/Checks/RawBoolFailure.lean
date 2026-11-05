import Solidity.Yul.RawBoolFailure
import Solidity.Yul.Checks.RawSequenceHorizon
import Solidity.Yul.Checks.RawInitializedForHorizon
/-! Concrete raw Boolean error families, dirty frame effects and retained
break success. The initialized-loop stuck witness prevents promoting these
bounded theorems to general error classification. H30 registration external. -/
namespace Solidity.Yul.Checks.RawBoolFailure
namespace Old
export Solidity.Yul.Checks.RawSequenceHorizon (ctx env dirty initial flag small)
export Solidity.Yul.Checks.RawLoopBodyHorizon (read breakBody breakSelected)
export Solidity.Yul.Checks.RawInitializedForHorizon (refusedBreak breakRefusal)
namespace Expr
export Solidity.Yul.Checks.RawStatementHorizon (expression proof)
end Expr
namespace Items
export Solidity.Yul.Checks.RawSequenceHorizon (items proof partialStages)
end Items
end Old
export Old (ctx env dirty initial flag small read breakBody)
def witness : Nonempty (RawLoopBody.Supported ctx [] false false
 (.ifThen (.local .here) .brk)) := ⟨breakBody⟩
theorem conditionFamily : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawBoolFailure.ctx) (halt : Solidity.Source.Halt), (Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawBoolFailure.read fuel state).1 = .error halt → halt = .timeout := by
  intro fuel state halt failed
  exact Solidity.Yul.RawBoolFailure.condition Solidity.Yul.Checks.RawBoolFailure.ctx _ Solidity.Yul.Checks.RawBoolFailure.read fuel state halt failed

theorem statementFamily : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawBoolFailure.ctx) (halt : Solidity.Source.Halt), (Solidity.Yul.RawCoherent.execS Solidity.Yul.Checks.RawBoolFailure.Old.Expr.proof fuel state).1 = .error halt → halt = .timeout := by
  intro fuel state halt failed
  exact Solidity.Yul.RawBoolFailure.statement Solidity.Yul.Checks.RawBoolFailure.ctx [] false ⟨true,false⟩ _ Solidity.Yul.Checks.RawBoolFailure.Old.Expr.proof fuel state halt failed

theorem sequenceFamily : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawBoolFailure.ctx) (halt : Solidity.Source.Halt), (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawBoolFailure.Old.Items.proof fuel state).1 = .error halt → halt = .timeout := by
  intro fuel state halt failed
  exact Solidity.Yul.RawBoolFailure.sequence Solidity.Yul.Checks.RawBoolFailure.ctx [] false ⟨true,false⟩ _ Solidity.Yul.Checks.RawBoolFailure.Old.Items.proof fuel state halt failed

theorem blockFamily : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawBoolFailure.ctx) (halt : Solidity.Source.Halt), (Solidity.Yul.RawSequence.block Solidity.Yul.Checks.RawBoolFailure.Old.Items.proof fuel state).1 = .error halt → halt = .timeout := by
  intro fuel state halt failed
  exact Solidity.Yul.RawBoolFailure.block Solidity.Yul.Checks.RawBoolFailure.ctx [] false ⟨true,false⟩ _ Solidity.Yul.Checks.RawBoolFailure.Old.Items.proof fuel state halt failed

theorem bodyFamily : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawBoolFailure.ctx) (halt : Solidity.Source.Halt), (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawBoolFailure.breakBody fuel state).1 = .error halt → halt = .timeout := by
  intro fuel state halt failed
  exact Solidity.Yul.RawBoolFailure.body Solidity.Yul.Checks.RawBoolFailure.ctx [] false false _ Solidity.Yul.Checks.RawBoolFailure.breakBody fuel state halt failed

theorem partialDirtySequence : (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawBoolFailure.Old.Items.proof 8 Solidity.Yul.Checks.RawBoolFailure.dirty).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawBoolFailure.Old.Items.proof 8 Solidity.Yul.Checks.RawBoolFailure.dirty).2 Solidity.Yul.Checks.RawBoolFailure.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawBoolFailure.Old.Items.proof 8 Solidity.Yul.Checks.RawBoolFailure.dirty).2 Solidity.Yul.Checks.RawBoolFailure.small).val = 257 := by
  exact ⟨Solidity.Yul.Checks.RawBoolFailure.Old.Items.partialStages.2.2.1,Solidity.Yul.Checks.RawBoolFailure.Old.Items.partialStages.2.2.2.1,Solidity.Yul.Checks.RawBoolFailure.Old.Items.partialStages.2.2.2.2⟩

theorem completedDirtyExpression : (Solidity.Yul.RawCoherent.execS Solidity.Yul.Checks.RawBoolFailure.Old.Expr.proof 7 Solidity.Yul.Checks.RawBoolFailure.dirty).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCoherent.execS Solidity.Yul.Checks.RawBoolFailure.Old.Expr.proof 7 Solidity.Yul.Checks.RawBoolFailure.dirty).2 Solidity.Yul.Checks.RawBoolFailure.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCoherent.execS Solidity.Yul.Checks.RawBoolFailure.Old.Expr.proof 7 Solidity.Yul.Checks.RawBoolFailure.dirty).2 Solidity.Yul.Checks.RawBoolFailure.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem breakSuccess : (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawBoolFailure.breakBody 2 Solidity.Yul.Checks.RawBoolFailure.dirty).1 = .ok (.break_ rfl) ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawBoolFailure.breakBody 2 Solidity.Yul.Checks.RawBoolFailure.dirty).2 Solidity.Yul.Checks.RawBoolFailure.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawBoolFailure.breakBody 2 Solidity.Yul.Checks.RawBoolFailure.dirty).2 Solidity.Yul.Checks.RawBoolFailure.small).val = 257 := by
  exact Solidity.Yul.Checks.RawBoolFailure.Old.breakSelected

theorem initializerCounterexample : (Solidity.Yul.Checks.RawBoolFailure.Old.refusedBreak.run 2 Solidity.Yul.Checks.RawBoolFailure.dirty).1 = .error (.stuck "for initializer") ∧ (Solidity.Source.Halt.stuck "for initializer" ≠ .timeout) := by
  exact ⟨Solidity.Yul.Checks.RawBoolFailure.Old.breakRefusal.1,by intro bad; cases bad⟩

theorem zeroCondition : ∀ state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawBoolFailure.ctx, (Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawBoolFailure.read 0 state).1 = .error .timeout := by
  intro state
  rfl

#print axioms Solidity.Yul.RawBoolFailure.condition
#print axioms Solidity.Yul.RawBoolFailure.statement
#print axioms Solidity.Yul.RawBoolFailure.sequence
#print axioms Solidity.Yul.RawBoolFailure.block
#print axioms Solidity.Yul.RawBoolFailure.body
#print axioms conditionFamily
#print axioms statementFamily
#print axioms sequenceFamily
#print axioms blockFamily
#print axioms bodyFamily
#print axioms partialDirtySequence
#print axioms completedDirtyExpression
#print axioms breakSuccess
#print axioms initializerCounterexample
#print axioms zeroCondition
end Solidity.Yul.Checks.RawBoolFailure
