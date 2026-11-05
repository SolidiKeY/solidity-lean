import Solidity.Yul.Checks.RawPureInitTimeout
/-! Concrete staged proof of the original initialized fuel-6 dirty-word prefix.
The explicit finite LOCAL tuple is tied to the real initializer by initStep;
guard/body/post equalities retain the entire actual frame. No cleaning/readback
policy or runtime implementation is changed. Registration is coordinator-owned. -/
namespace Solidity.Yul.Checks.RawPureInitPrefix
open Solidity.Yul.Checks.RawPureInitTimeout
def tail : LocalValues env ctx.tys.tail :=
 (.externalFunction [.bool] [.int Solidity.Source.IntTy.u8] (some .view)
    (word 4660) (word 2309737967),
  (.scalar CleanLocals.u8Shape (word 257),
   (.externalFunction [.bool] [.int Solidity.Source.IntTy.u8] (some .view)
     (word 22136) (word 16909060),
    (.scalar CleanLocals.bytesShape (word (171*2^248)),()))))
def locals (b : Bool) : LocalValues env ctx.tys := (.clean (.bool b),tail)
def state (b : Bool) : RawFrame.State ctx :=
 ⟨dirty.clean,fun c => some (localWordCells ctx (locals b) c),dirty.world⟩
theorem initStep : RawSequence.block initProof 5 dirty = (.ok (),state true) := by
 rfl

def rawLocals (b : Bool) : LocalValues env ctx.tys :=
 (.scalar (LocalOperations.boolShape env) (word (if b then 1 else 0)),tail)
def rawState (b : Bool) : RawFrame.State ctx :=
 ⟨dirty.clean,fun c => some (localWordCells ctx (rawLocals b) c),dirty.world⟩
theorem firstGuard : RawCondition.eval (.base (.literal true)) 4 (state true) =
 (.ok true,rawState true) := by
 rfl
theorem firstBody : RawLoopBody.run Old.mutatingContinue 4 (rawState true) =
 (.ok (.continue_ rfl),state false) := by
 rfl
theorem firstPost : RawSourceForPost.discard writeFalse 4 (state false) =
 (.ok (),state false) := by
 rfl
theorem nextGuard : RawCondition.eval (.base (.literal true)) 3 (state false) =
 (.ok true,rawState false) := by
 rfl
theorem nextBody : RawLoopBody.run Old.mutatingContinue 3 (rawState false) =
 (.error .timeout,rawState false) := by
 rfl


theorem loop4 : RawSourceForPost.run (.base (.literal true)) writeFalse
 (RawSourceAdapter.body Old.mutatingContinue) 4 (state false) =
 (.error .timeout,rawState false) := by
 rw [RawSourceForPost.run,nextGuard]
 simp only [RawSourceAdapter.body,nextBody,if_true]
theorem loop5 : RawSourceForPost.run (.base (.literal true)) writeFalse
 (RawSourceAdapter.body Old.mutatingContinue) 5 (state true) =
 (.error .timeout,rawState false) := by
 rw [RawSourceForPost.run,firstGuard]
 simp only [RawSourceAdapter.body,firstBody]
 rw [RawSourceForPost.after,firstPost]
 exact loop4
theorem initialized6 : RawSourceForPost.Initialized.run
 (RawSourceAdapter.body (.plain initProof)) (.base (.literal true)) writeFalse
 (RawSourceAdapter.body Old.mutatingContinue) 6 dirty =
 (.error .timeout,rawState false) := by
 rw [RawSourceForPost.Initialized.run]
 dsimp only [RawSourceAdapter.body,RawLoopBody.run]
 rw [initStep]
 exact loop5
theorem dirtyMutatingPrefix : (Solidity.Yul.RawSourceForPost.Initialized.run (Solidity.Yul.RawSourceAdapter.body (Solidity.Yul.RawLoopBody.Supported.plain Solidity.Yul.Checks.RawPureInitTimeout.initProof)) (.base (.literal true)) Solidity.Yul.Checks.RawPureInitTimeout.writeFalse (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawPureInitTimeout.Old.mutatingContinue) 6 Solidity.Yul.Checks.RawPureInitTimeout.dirty).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSourceForPost.Initialized.run (Solidity.Yul.RawSourceAdapter.body (Solidity.Yul.RawLoopBody.Supported.plain Solidity.Yul.Checks.RawPureInitTimeout.initProof)) (.base (.literal true)) Solidity.Yul.Checks.RawPureInitTimeout.writeFalse (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawPureInitTimeout.Old.mutatingContinue) 6 Solidity.Yul.Checks.RawPureInitTimeout.dirty).2 Solidity.Yul.Checks.RawStatementHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSourceForPost.Initialized.run (Solidity.Yul.RawSourceAdapter.body (Solidity.Yul.RawLoopBody.Supported.plain Solidity.Yul.Checks.RawPureInitTimeout.initProof)) (.base (.literal true)) Solidity.Yul.Checks.RawPureInitTimeout.writeFalse (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawPureInitTimeout.Old.mutatingContinue) 6 Solidity.Yul.Checks.RawPureInitTimeout.dirty).2 Solidity.Yul.Checks.RawStatementHorizon.small).val = 257 := by
  rw [initialized6]
  exact ⟨rfl,rfl,rfl⟩
#print axioms initStep
#print axioms firstGuard
#print axioms firstBody
#print axioms firstPost
#print axioms nextGuard
#print axioms nextBody
#print axioms loop4
#print axioms loop5
#print axioms initialized6
#print axioms dirtyMutatingPrefix
end Solidity.Yul.Checks.RawPureInitPrefix
