import Solidity.Yul.RawDoWhileHorizon
import Solidity.Yul.Checks.RawControlledWhileHorizon
namespace Solidity.Yul.Checks.RawDoWhileHorizon
namespace Old
export Solidity.Yul.Checks.RawControlledWhileHorizon
 (ctx env dirty initial flag small read breakBody mutatingContinue normalBody singleItems stopped)
end Old
export Old (ctx env dirty initial flag small read)
def deep : LocalBoolControl.Supported env ctx.tys
 (.unary .not (.unary .not (.unary .not (.unary .not (.bool true))))) :=
 .not (.not (.not (.not (.base (.literal true)))))
def breakStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .doWhile (.ifThen (.local .here) .brk) (.unary .not (.unary .not (.unary .not (.unary .not (.bool true)))))
def continueStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .doWhile (.ifThen (.unary .not (.assign (.local .here) (.bool false))) .cont) (.local .here)
def normalStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .doWhile (.block Old.singleItems) (.bool false)
def broken : RawSourceAdapter.Adapter ctx [] false false breakStmt :=
 RawSourceAdapterDoWhile.adapter deep (RawSourceAdapter.body Old.breakBody)
def continued : RawSourceAdapter.Adapter ctx [] false false continueStmt :=
 RawSourceAdapterDoWhile.adapter read (RawSourceAdapter.body Old.mutatingContinue)
def normal : RawSourceAdapter.Adapter ctx [] false false normalStmt :=
 RawSourceAdapterDoWhile.adapter Old.stopped (RawSourceAdapter.body Old.normalBody)
def witness : Nonempty (RawSourceAdapter.Adapter ctx [] false false continueStmt) := ⟨continued⟩
theorem breakExit : (Solidity.Yul.Checks.RawDoWhileHorizon.broken.run 3 Solidity.Yul.Checks.RawDoWhileHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawDoWhileHorizon.broken.run 3 Solidity.Yul.Checks.RawDoWhileHorizon.dirty).2 Solidity.Yul.Checks.RawDoWhileHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawDoWhileHorizon.broken.run 3 Solidity.Yul.Checks.RawDoWhileHorizon.dirty).2 Solidity.Yul.Checks.RawDoWhileHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem continueExit : (Solidity.Yul.Checks.RawDoWhileHorizon.continued.run 5 Solidity.Yul.Checks.RawDoWhileHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawDoWhileHorizon.continued.run 5 Solidity.Yul.Checks.RawDoWhileHorizon.dirty).2 Solidity.Yul.Checks.RawDoWhileHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawDoWhileHorizon.continued.run 5 Solidity.Yul.Checks.RawDoWhileHorizon.dirty).2 Solidity.Yul.Checks.RawDoWhileHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem falseStillRunsBody : (Solidity.Yul.Checks.RawDoWhileHorizon.normal.run 10 Solidity.Yul.Checks.RawDoWhileHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawDoWhileHorizon.normal.run 10 Solidity.Yul.Checks.RawDoWhileHorizon.dirty).2 Solidity.Yul.Checks.RawDoWhileHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawDoWhileHorizon.normal.run 10 Solidity.Yul.Checks.RawDoWhileHorizon.dirty).2 Solidity.Yul.Checks.RawDoWhileHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem breakStable : ∀ extra : Nat, Solidity.Yul.Checks.RawDoWhileHorizon.broken.run (3+extra) Solidity.Yul.Checks.RawDoWhileHorizon.dirty = Solidity.Yul.Checks.RawDoWhileHorizon.broken.run 3 Solidity.Yul.Checks.RawDoWhileHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawDoWhileHorizon.adapterExtension Solidity.Yul.Checks.RawDoWhileHorizon.ctx [] false false _ Solidity.Yul.Checks.RawDoWhileHorizon.deep _ Solidity.Yul.Checks.RawDoWhileHorizon.Old.breakBody 3 extra Solidity.Yul.Checks.RawDoWhileHorizon.dirty (by change (Solidity.Yul.Checks.RawDoWhileHorizon.broken.run 3 Solidity.Yul.Checks.RawDoWhileHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawDoWhileHorizon.breakExit).1]; intro bad; cases bad)

theorem continueStable : ∀ extra : Nat, Solidity.Yul.Checks.RawDoWhileHorizon.continued.run (5+extra) Solidity.Yul.Checks.RawDoWhileHorizon.dirty = Solidity.Yul.Checks.RawDoWhileHorizon.continued.run 5 Solidity.Yul.Checks.RawDoWhileHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawDoWhileHorizon.adapterExtension Solidity.Yul.Checks.RawDoWhileHorizon.ctx [] false false _ Solidity.Yul.Checks.RawDoWhileHorizon.read _ Solidity.Yul.Checks.RawDoWhileHorizon.Old.mutatingContinue 5 extra Solidity.Yul.Checks.RawDoWhileHorizon.dirty (by change (Solidity.Yul.Checks.RawDoWhileHorizon.continued.run 5 Solidity.Yul.Checks.RawDoWhileHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawDoWhileHorizon.continueExit).1]; intro bad; cases bad)

theorem normalStable : ∀ extra : Nat, Solidity.Yul.Checks.RawDoWhileHorizon.normal.run (10+extra) Solidity.Yul.Checks.RawDoWhileHorizon.dirty = Solidity.Yul.Checks.RawDoWhileHorizon.normal.run 10 Solidity.Yul.Checks.RawDoWhileHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawDoWhileHorizon.adapterExtension Solidity.Yul.Checks.RawDoWhileHorizon.ctx [] false false _ Solidity.Yul.Checks.RawDoWhileHorizon.Old.stopped _ Solidity.Yul.Checks.RawDoWhileHorizon.Old.normalBody 10 extra Solidity.Yul.Checks.RawDoWhileHorizon.dirty (by change (Solidity.Yul.Checks.RawDoWhileHorizon.normal.run 10 Solidity.Yul.Checks.RawDoWhileHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawDoWhileHorizon.falseStillRunsBody).1]; intro bad; cases bad)

theorem earlyTimeout : (Solidity.Yul.Checks.RawDoWhileHorizon.normal.run 9 Solidity.Yul.Checks.RawDoWhileHorizon.dirty).1 = .error .timeout := by
  rfl

theorem conditionWouldTimeout : (Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawDoWhileHorizon.deep 2 Solidity.Yul.Checks.RawDoWhileHorizon.dirty).1 = .error .timeout := by
  rfl

theorem cleanSource : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawDoWhileHorizon.env) (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawDoWhileHorizon.env)), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawDoWhileHorizon.continued.run fuel Solidity.Yul.Checks.RawDoWhileHorizon.initial).2 = true ∧ (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawDoWhileHorizon.continueStmt Solidity.Yul.Checks.RawDoWhileHorizon.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawDoWhileHorizon.env,Solidity.Yul.Checks.RawDoWhileHorizon.initial.world) = Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawDoWhileHorizon.continued.run fuel Solidity.Yul.Checks.RawDoWhileHorizon.initial) := by
  intro glob frame fuel nps ph
  exact Solidity.Yul.Checks.RawDoWhileHorizon.continued.correct glob frame fuel nps ph Solidity.Yul.Checks.RawDoWhileHorizon.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _)

#print axioms Solidity.Yul.RawDoWhileHorizon.successor
#print axioms Solidity.Yul.RawDoWhileHorizon.extension
#print axioms Solidity.Yul.RawDoWhileHorizon.adapterSuccessor
#print axioms Solidity.Yul.RawDoWhileHorizon.adapterExtension
#print axioms breakExit
#print axioms continueExit
#print axioms falseStillRunsBody
#print axioms breakStable
#print axioms continueStable
#print axioms normalStable
#print axioms earlyTimeout
#print axioms conditionWouldTimeout
#print axioms cleanSource
end Solidity.Yul.Checks.RawDoWhileHorizon
