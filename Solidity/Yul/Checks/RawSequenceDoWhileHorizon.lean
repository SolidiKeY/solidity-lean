import Solidity.Yul.RawSequenceDoWhileHorizon
import Solidity.Yul.Checks.RawSequenceWhileHorizon
/-! Concrete sequence/body-first controls: break and continue bypass the deep tail,
normal executes before a false guard, completed entire dirty frames stabilize.
Clean Source correctness remains separately bounded. H30 registration is external. -/
namespace Solidity.Yul.Checks.RawSequenceDoWhileHorizon
namespace Old
export Solidity.Yul.Checks.RawSequenceWhileHorizon
 (ctx env dirty initial flag small read breakItems breakProof continueItems continueProof normalItems normalProof stopped)
end Old
export Old (ctx env dirty initial flag small read)
def deep : LocalBoolControl.Supported env ctx.tys
 (.unary .not (.unary .not (.unary .not (.unary .not (.bool true))))) :=
 .not (.not (.not (.not (.base (.literal true)))))
def breakStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .doWhile (.block Old.breakItems) (.unary .not (.unary .not (.unary .not (.unary .not (.bool true)))))
def continueStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .doWhile (.block Old.continueItems) (.local .here)
def normalStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .doWhile (.block Old.normalItems) (.bool false)
def broken : RawSourceAdapter.Adapter ctx [] false false breakStmt :=
 RawSourceAdapterDoWhile.adapter deep (RawSourceAdapter.block (RawSourceAdapter.sequence Old.breakProof))
def continued : RawSourceAdapter.Adapter ctx [] false false continueStmt :=
 RawSourceAdapterDoWhile.adapter read (RawSourceAdapter.block (RawSourceAdapter.sequence Old.continueProof))
def normal : RawSourceAdapter.Adapter ctx [] false false normalStmt :=
 RawSourceAdapterDoWhile.adapter Old.stopped (RawSourceAdapter.block (RawSourceAdapter.sequence Old.normalProof))
def witness : Nonempty (RawSourceAdapter.Adapter ctx [] false false continueStmt) := ⟨continued⟩
theorem breakExit : (Solidity.Yul.Checks.RawSequenceDoWhileHorizon.broken.run 5 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawSequenceDoWhileHorizon.broken.run 5 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawSequenceDoWhileHorizon.broken.run 5 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem continueExit : (Solidity.Yul.Checks.RawSequenceDoWhileHorizon.continued.run 7 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawSequenceDoWhileHorizon.continued.run 7 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawSequenceDoWhileHorizon.continued.run 7 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem falseStillRunsBody : (Solidity.Yul.Checks.RawSequenceDoWhileHorizon.normal.run 12 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawSequenceDoWhileHorizon.normal.run 12 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawSequenceDoWhileHorizon.normal.run 12 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem breakStable : ∀ extra : Nat, Solidity.Yul.Checks.RawSequenceDoWhileHorizon.broken.run (5+extra) Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty = Solidity.Yul.Checks.RawSequenceDoWhileHorizon.broken.run 5 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawSequenceDoWhileHorizon.adapterExtension Solidity.Yul.Checks.RawSequenceDoWhileHorizon.ctx [] false false _ Solidity.Yul.Checks.RawSequenceDoWhileHorizon.deep _ Solidity.Yul.Checks.RawSequenceDoWhileHorizon.Old.breakProof 5 extra Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty (by change (Solidity.Yul.Checks.RawSequenceDoWhileHorizon.broken.run 5 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawSequenceDoWhileHorizon.breakExit).1]; intro bad; cases bad)

theorem continueStable : ∀ extra : Nat, Solidity.Yul.Checks.RawSequenceDoWhileHorizon.continued.run (7+extra) Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty = Solidity.Yul.Checks.RawSequenceDoWhileHorizon.continued.run 7 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawSequenceDoWhileHorizon.adapterExtension Solidity.Yul.Checks.RawSequenceDoWhileHorizon.ctx [] false false _ Solidity.Yul.Checks.RawSequenceDoWhileHorizon.read _ Solidity.Yul.Checks.RawSequenceDoWhileHorizon.Old.continueProof 7 extra Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty (by change (Solidity.Yul.Checks.RawSequenceDoWhileHorizon.continued.run 7 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawSequenceDoWhileHorizon.continueExit).1]; intro bad; cases bad)

theorem normalStable : ∀ extra : Nat, Solidity.Yul.Checks.RawSequenceDoWhileHorizon.normal.run (12+extra) Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty = Solidity.Yul.Checks.RawSequenceDoWhileHorizon.normal.run 12 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawSequenceDoWhileHorizon.adapterExtension Solidity.Yul.Checks.RawSequenceDoWhileHorizon.ctx [] false false _ Solidity.Yul.Checks.RawSequenceDoWhileHorizon.Old.stopped _ Solidity.Yul.Checks.RawSequenceDoWhileHorizon.Old.normalProof 12 extra Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty (by change (Solidity.Yul.Checks.RawSequenceDoWhileHorizon.normal.run 12 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawSequenceDoWhileHorizon.falseStillRunsBody).1]; intro bad; cases bad)

theorem earlyTimeout : (Solidity.Yul.Checks.RawSequenceDoWhileHorizon.normal.run 11 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty).1 = .error .timeout := by
  rfl

theorem conditionWouldTimeout : (Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawSequenceDoWhileHorizon.deep 4 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.dirty).1 = .error .timeout := by
  rfl

theorem cleanSource : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawSequenceDoWhileHorizon.env) (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawSequenceDoWhileHorizon.env)), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawSequenceDoWhileHorizon.continued.run fuel Solidity.Yul.Checks.RawSequenceDoWhileHorizon.initial).2 = true ∧ (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawSequenceDoWhileHorizon.continueStmt Solidity.Yul.Checks.RawSequenceDoWhileHorizon.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawSequenceDoWhileHorizon.env,Solidity.Yul.Checks.RawSequenceDoWhileHorizon.initial.world) = Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawSequenceDoWhileHorizon.continued.run fuel Solidity.Yul.Checks.RawSequenceDoWhileHorizon.initial) := by
  intro glob frame fuel nps ph
  exact Solidity.Yul.Checks.RawSequenceDoWhileHorizon.continued.correct glob frame fuel nps ph Solidity.Yul.Checks.RawSequenceDoWhileHorizon.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _)

#print axioms Solidity.Yul.RawSequenceDoWhileHorizon.successor
#print axioms Solidity.Yul.RawSequenceDoWhileHorizon.extension
#print axioms Solidity.Yul.RawSequenceDoWhileHorizon.adapterSuccessor
#print axioms Solidity.Yul.RawSequenceDoWhileHorizon.adapterExtension
#print axioms breakExit
#print axioms continueExit
#print axioms falseStillRunsBody
#print axioms breakStable
#print axioms continueStable
#print axioms normalStable
#print axioms earlyTimeout
#print axioms conditionWouldTimeout
#print axioms cleanSource
end Solidity.Yul.Checks.RawSequenceDoWhileHorizon
