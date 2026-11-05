import Solidity.Yul.RawForPostHorizon
import Solidity.Yul.Checks.RawControlledWhileHorizon
/-! Actual for-post driver controls preserve dirty siblings and distinguish
continue executing post from break skipping it. Source correctness is clean-start.
H30 root/module-map registration remains a coordinator integration obligation. -/
namespace Solidity.Yul.Checks.RawForPostHorizon
namespace Old
export Solidity.Yul.Checks.RawControlledWhileHorizon
 (ctx env dirty initial flag small read breakBody normalBody)
end Old
export Old (ctx env dirty initial flag small read)
def deep : LocalBoolControl.Supported env ctx.tys
 (.unary .not (.unary .not (.unary .not (.unary .not (.bool true))))) :=
 .not (.not (.not (.not (.base (.literal true)))))
def writeFalse : LocalBoolControl.Supported env ctx.tys (.assign (.local .here) (.bool false)) :=
 .assign .here (.base (.literal false))
def continuation : RawLoopBody.Supported ctx [] false false .cont := .continue_
def broken (fuel : Nat) (state : RawFrame.State ctx) :=
 RawSourceForPost.run read deep (RawSourceAdapter.body Old.breakBody) fuel state
def continued (fuel : Nat) (state : RawFrame.State ctx) :=
 RawSourceForPost.run read writeFalse (RawSourceAdapter.body continuation) fuel state
def normal (fuel : Nat) (state : RawFrame.State ctx) :=
 RawSourceForPost.run read writeFalse (RawSourceAdapter.body Old.normalBody) fuel state
def witness : Nonempty (RawSourceAdapter.Adapter ctx [] false false .cont) :=
 ⟨RawSourceAdapter.body continuation⟩
theorem breakExit : (Solidity.Yul.Checks.RawForPostHorizon.broken 3 Solidity.Yul.Checks.RawForPostHorizon.dirty).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawForPostHorizon.broken 3 Solidity.Yul.Checks.RawForPostHorizon.dirty).2 Solidity.Yul.Checks.RawForPostHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawForPostHorizon.broken 3 Solidity.Yul.Checks.RawForPostHorizon.dirty).2 Solidity.Yul.Checks.RawForPostHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem continuePost : (Solidity.Yul.Checks.RawForPostHorizon.continued 3 Solidity.Yul.Checks.RawForPostHorizon.dirty).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawForPostHorizon.continued 3 Solidity.Yul.Checks.RawForPostHorizon.dirty).2 Solidity.Yul.Checks.RawForPostHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawForPostHorizon.continued 3 Solidity.Yul.Checks.RawForPostHorizon.dirty).2 Solidity.Yul.Checks.RawForPostHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem normalExit : (Solidity.Yul.Checks.RawForPostHorizon.normal 10 Solidity.Yul.Checks.RawForPostHorizon.dirty).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawForPostHorizon.normal 10 Solidity.Yul.Checks.RawForPostHorizon.dirty).2 Solidity.Yul.Checks.RawForPostHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawForPostHorizon.normal 10 Solidity.Yul.Checks.RawForPostHorizon.dirty).2 Solidity.Yul.Checks.RawForPostHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem breakStable : ∀ extra : Nat, Solidity.Yul.Checks.RawForPostHorizon.broken (3+extra) Solidity.Yul.Checks.RawForPostHorizon.dirty = Solidity.Yul.Checks.RawForPostHorizon.broken 3 Solidity.Yul.Checks.RawForPostHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawForPostHorizon.extension Solidity.Yul.Checks.RawForPostHorizon.ctx [] false false _ Solidity.Yul.Checks.RawForPostHorizon.read _ Solidity.Yul.Checks.RawForPostHorizon.deep _ Solidity.Yul.Checks.RawForPostHorizon.Old.breakBody 3 extra Solidity.Yul.Checks.RawForPostHorizon.dirty (by change (Solidity.Yul.Checks.RawForPostHorizon.broken 3 Solidity.Yul.Checks.RawForPostHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawForPostHorizon.breakExit).1]; intro bad; cases bad)

theorem continueStable : ∀ extra : Nat, Solidity.Yul.Checks.RawForPostHorizon.continued (3+extra) Solidity.Yul.Checks.RawForPostHorizon.dirty = Solidity.Yul.Checks.RawForPostHorizon.continued 3 Solidity.Yul.Checks.RawForPostHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawForPostHorizon.extension Solidity.Yul.Checks.RawForPostHorizon.ctx [] false false _ Solidity.Yul.Checks.RawForPostHorizon.read _ Solidity.Yul.Checks.RawForPostHorizon.writeFalse _ Solidity.Yul.Checks.RawForPostHorizon.continuation 3 extra Solidity.Yul.Checks.RawForPostHorizon.dirty (by change (Solidity.Yul.Checks.RawForPostHorizon.continued 3 Solidity.Yul.Checks.RawForPostHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawForPostHorizon.continuePost).1]; intro bad; cases bad)

theorem normalStable : ∀ extra : Nat, Solidity.Yul.Checks.RawForPostHorizon.normal (10+extra) Solidity.Yul.Checks.RawForPostHorizon.dirty = Solidity.Yul.Checks.RawForPostHorizon.normal 10 Solidity.Yul.Checks.RawForPostHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawForPostHorizon.extension Solidity.Yul.Checks.RawForPostHorizon.ctx [] false false _ Solidity.Yul.Checks.RawForPostHorizon.read _ Solidity.Yul.Checks.RawForPostHorizon.writeFalse _ Solidity.Yul.Checks.RawForPostHorizon.Old.normalBody 10 extra Solidity.Yul.Checks.RawForPostHorizon.dirty (by change (Solidity.Yul.Checks.RawForPostHorizon.normal 10 Solidity.Yul.Checks.RawForPostHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawForPostHorizon.normalExit).1]; intro bad; cases bad)

theorem earlyTimeout : (Solidity.Yul.Checks.RawForPostHorizon.continued 2 Solidity.Yul.Checks.RawForPostHorizon.dirty).1 = .error .timeout := by
  rfl

theorem postWouldTimeout : (Solidity.Yul.RawSourceForPost.discard Solidity.Yul.Checks.RawForPostHorizon.deep 2 Solidity.Yul.Checks.RawForPostHorizon.dirty).1 = .error .timeout := by
  rfl

theorem cleanSource : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawForPostHorizon.env) (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawForPostHorizon.env)), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawForPostHorizon.continued fuel Solidity.Yul.Checks.RawForPostHorizon.initial).2 = true ∧ (Solidity.Source.forIter glob frame fuel nps ph (.some (.local .here)) (.some (.assign (.local .here) (.bool false))) (.cont : Solidity.Source.RStmt Solidity.Yul.Checks.RawForPostHorizon.env [] false ⟨true,false⟩ Solidity.Yul.Checks.RawForPostHorizon.ctx.tys Solidity.Yul.Checks.RawForPostHorizon.ctx.tys) Solidity.Yul.Checks.RawForPostHorizon.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawForPostHorizon.env,Solidity.Yul.Checks.RawForPostHorizon.initial.world) = Solidity.Yul.RawSequence.represented (Solidity.Yul.Checks.RawForPostHorizon.continued fuel Solidity.Yul.Checks.RawForPostHorizon.initial) := by
  intro glob frame fuel nps ph
  exact Solidity.Yul.RawSourceForPost.correct Solidity.Yul.Checks.RawForPostHorizon.read Solidity.Yul.Checks.RawForPostHorizon.writeFalse (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawForPostHorizon.continuation) glob frame fuel nps ph Solidity.Yul.Checks.RawForPostHorizon.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _)

theorem discardWrite : (Solidity.Yul.RawSourceForPost.discard Solidity.Yul.Checks.RawForPostHorizon.writeFalse 2 Solidity.Yul.Checks.RawForPostHorizon.dirty).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSourceForPost.discard Solidity.Yul.Checks.RawForPostHorizon.writeFalse 2 Solidity.Yul.Checks.RawForPostHorizon.dirty).2 Solidity.Yul.Checks.RawForPostHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSourceForPost.discard Solidity.Yul.Checks.RawForPostHorizon.writeFalse 2 Solidity.Yul.Checks.RawForPostHorizon.dirty).2 Solidity.Yul.Checks.RawForPostHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

#print axioms Solidity.Yul.RawForPostHorizon.discardSuccessor
#print axioms Solidity.Yul.RawForPostHorizon.successor
#print axioms Solidity.Yul.RawForPostHorizon.extension
#print axioms breakExit
#print axioms continuePost
#print axioms normalExit
#print axioms breakStable
#print axioms continueStable
#print axioms normalStable
#print axioms earlyTimeout
#print axioms postWouldTimeout
#print axioms cleanSource
#print axioms discardWrite
end Solidity.Yul.Checks.RawForPostHorizon
