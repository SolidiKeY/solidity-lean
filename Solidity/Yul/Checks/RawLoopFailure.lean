import Solidity.Yul.RawLoopFailure
import Solidity.Yul.Checks.RawForPostHorizon
import Solidity.Yul.Checks.RawInitializedForHorizon
/-! Concrete restricted loop error/timeout families and dirty reached-state
controls. Break completion shows noBreak is necessary; initialized stuck remains
outside the classifier domain. No broader admission/Source claim. H30 registration external. -/
namespace Solidity.Yul.Checks.RawLoopFailure
namespace Old
export Solidity.Yul.Checks.RawControlledWhileHorizon
 (ctx env dirty initial flag small read breakBody mutatingContinue normalBody)
export Solidity.Yul.Checks.RawForPostHorizon (writeFalse continuation)
export Solidity.Yul.Checks.RawInitializedForHorizon (breakProof refusedBreak breakRefusal)
end Old
export Old (ctx env dirty initial flag small read)
def witness : Nonempty (RawLoopBody.Supported ctx [] false false
 (.ifThen (.unary .not (.assign (.local .here) (.bool false))) .cont)) := ⟨Old.mutatingContinue⟩
theorem whileFamily : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawLoopFailure.ctx) (halt : Solidity.Source.Halt), (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawLoopFailure.read Solidity.Yul.Checks.RawLoopFailure.Old.breakBody fuel state).1 = .error halt → halt = .timeout := by
  intro fuel state halt failed
  exact Solidity.Yul.RawLoopFailure.while_error Solidity.Yul.Checks.RawLoopFailure.ctx [] false false _ Solidity.Yul.Checks.RawLoopFailure.read _ Solidity.Yul.Checks.RawLoopFailure.Old.breakBody fuel state halt failed

theorem doWhileFamily : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawLoopFailure.ctx) (halt : Solidity.Source.Halt), (Solidity.Yul.RawSourceAdapterDoWhile.run Solidity.Yul.Checks.RawLoopFailure.read (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawLoopFailure.Old.mutatingContinue) fuel state).1 = .error halt → halt = .timeout := by
  intro fuel state halt failed
  exact Solidity.Yul.RawLoopFailure.do_while_error Solidity.Yul.Checks.RawLoopFailure.ctx [] false false _ Solidity.Yul.Checks.RawLoopFailure.read _ Solidity.Yul.Checks.RawLoopFailure.Old.mutatingContinue fuel state halt failed

theorem postFamily : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawLoopFailure.ctx) (halt : Solidity.Source.Halt), (Solidity.Yul.RawSourceForPost.run Solidity.Yul.Checks.RawLoopFailure.read Solidity.Yul.Checks.RawLoopFailure.Old.writeFalse (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawLoopFailure.Old.normalBody) fuel state).1 = .error halt → halt = .timeout := by
  intro fuel state halt failed
  exact Solidity.Yul.RawLoopFailure.post_error Solidity.Yul.Checks.RawLoopFailure.ctx [] false false _ Solidity.Yul.Checks.RawLoopFailure.read _ Solidity.Yul.Checks.RawLoopFailure.Old.normalBody _ Solidity.Yul.Checks.RawLoopFailure.Old.writeFalse fuel state halt failed

theorem discardFamily : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawLoopFailure.ctx) (halt : Solidity.Source.Halt), (Solidity.Yul.RawSourceForPost.discard Solidity.Yul.Checks.RawLoopFailure.Old.writeFalse fuel state).1 = .error halt → halt = .timeout := by
  intro fuel state halt failed
  exact Solidity.Yul.RawLoopFailure.discard_error Solidity.Yul.Checks.RawLoopFailure.ctx _ Solidity.Yul.Checks.RawLoopFailure.Old.writeFalse fuel state halt failed

theorem noPostTimeoutFamily : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawLoopFailure.ctx), (Solidity.Yul.RawControlledWhile.run (.base (.literal true)) Solidity.Yul.Checks.RawLoopFailure.Old.mutatingContinue fuel state).1 = .error .timeout := by
  intro fuel state
  exact Solidity.Yul.RawLoopFailure.no_post_timeout Solidity.Yul.Checks.RawLoopFailure.ctx [] false false _ Solidity.Yul.Checks.RawLoopFailure.Old.mutatingContinue (by rfl) fuel state

theorem postTimeoutFamily : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawLoopFailure.ctx), (Solidity.Yul.RawSourceForPost.run (.base (.literal true)) Solidity.Yul.Checks.RawLoopFailure.Old.writeFalse (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawLoopFailure.Old.mutatingContinue) fuel state).1 = .error .timeout := by
  intro fuel state
  exact Solidity.Yul.RawLoopFailure.post_timeout Solidity.Yul.Checks.RawLoopFailure.ctx [] false false _ Solidity.Yul.Checks.RawLoopFailure.Old.mutatingContinue (by rfl) _ Solidity.Yul.Checks.RawLoopFailure.Old.writeFalse fuel state

theorem dirtyNoPostPrefix : (Solidity.Yul.RawControlledWhile.run (.base (.literal true)) Solidity.Yul.Checks.RawLoopFailure.Old.mutatingContinue 5 Solidity.Yul.Checks.RawLoopFailure.dirty).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run (.base (.literal true)) Solidity.Yul.Checks.RawLoopFailure.Old.mutatingContinue 5 Solidity.Yul.Checks.RawLoopFailure.dirty).2 Solidity.Yul.Checks.RawLoopFailure.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run (.base (.literal true)) Solidity.Yul.Checks.RawLoopFailure.Old.mutatingContinue 5 Solidity.Yul.Checks.RawLoopFailure.dirty).2 Solidity.Yul.Checks.RawLoopFailure.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem dirtyPostPrefix : (Solidity.Yul.RawSourceForPost.run (.base (.literal true)) Solidity.Yul.Checks.RawLoopFailure.Old.writeFalse (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawLoopFailure.Old.continuation) 3 Solidity.Yul.Checks.RawLoopFailure.dirty).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSourceForPost.run (.base (.literal true)) Solidity.Yul.Checks.RawLoopFailure.Old.writeFalse (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawLoopFailure.Old.continuation) 3 Solidity.Yul.Checks.RawLoopFailure.dirty).2 Solidity.Yul.Checks.RawLoopFailure.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSourceForPost.run (.base (.literal true)) Solidity.Yul.Checks.RawLoopFailure.Old.writeFalse (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawLoopFailure.Old.continuation) 3 Solidity.Yul.Checks.RawLoopFailure.dirty).2 Solidity.Yul.Checks.RawLoopFailure.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem breakCounterexample : (Solidity.Yul.RawControlledWhile.run (.base (.literal true)) Solidity.Yul.Checks.RawLoopFailure.Old.breakProof 2 Solidity.Yul.Checks.RawLoopFailure.dirty).1 = .ok () ∧ Solidity.Yul.RawNoGuardFailure.noBreak Solidity.Yul.Checks.RawLoopFailure.Old.breakProof = false ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run (.base (.literal true)) Solidity.Yul.Checks.RawLoopFailure.Old.breakProof 2 Solidity.Yul.Checks.RawLoopFailure.dirty).2 Solidity.Yul.Checks.RawLoopFailure.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run (.base (.literal true)) Solidity.Yul.Checks.RawLoopFailure.Old.breakProof 2 Solidity.Yul.Checks.RawLoopFailure.dirty).2 Solidity.Yul.Checks.RawLoopFailure.small).val = 257 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem initializerCounterexample : (Solidity.Yul.Checks.RawLoopFailure.Old.refusedBreak.run 2 Solidity.Yul.Checks.RawLoopFailure.dirty).1 = .error (.stuck "for initializer") ∧ (Solidity.Source.Halt.stuck "for initializer" ≠ .timeout) := by
  exact ⟨Solidity.Yul.Checks.RawLoopFailure.Old.breakRefusal.1,by intro bad; cases bad⟩

#print axioms Solidity.Yul.RawLoopFailure.while_error
#print axioms Solidity.Yul.RawLoopFailure.do_while_error
#print axioms Solidity.Yul.RawLoopFailure.discard_error
#print axioms Solidity.Yul.RawLoopFailure.post_error
#print axioms Solidity.Yul.RawLoopFailure.no_post_timeout
#print axioms Solidity.Yul.RawLoopFailure.post_timeout
#print axioms whileFamily
#print axioms doWhileFamily
#print axioms postFamily
#print axioms discardFamily
#print axioms noPostTimeoutFamily
#print axioms postTimeoutFamily
#print axioms dirtyNoPostPrefix
#print axioms dirtyPostPrefix
#print axioms breakCounterexample
#print axioms initializerCounterexample
end Solidity.Yul.Checks.RawLoopFailure
