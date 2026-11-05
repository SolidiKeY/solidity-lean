import Solidity.Yul.RawAdapterLoopHorizon
import Solidity.Yul.Checks.RawControlledWhileHorizon
namespace Solidity.Yul.Checks.RawAdapterLoopHorizon
namespace Old
export Solidity.Yul.Checks.RawControlledWhileHorizon
 (ctx env dirty initial flag small read stopped breakBody mutatingContinue normalBody singleItems)
end Old
export Old (ctx env dirty initial flag small read)
def breakStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .whileLoop (.local .here) (.ifThen (.local .here) .brk)
def continueStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .whileLoop (.local .here) (.ifThen (.unary .not (.assign (.local .here) (.bool false))) .cont)
def normalStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .whileLoop (.local .here) (.block Old.singleItems)
def broken : RawSourceAdapter.Adapter ctx [] false false breakStmt :=
 RawSourceAdapterLoop.loop read (RawSourceAdapter.body Old.breakBody)
def continued : RawSourceAdapter.Adapter ctx [] false false continueStmt :=
 RawSourceAdapterLoop.loop read (RawSourceAdapter.body Old.mutatingContinue)
def normal : RawSourceAdapter.Adapter ctx [] false false normalStmt :=
 RawSourceAdapterLoop.loop read (RawSourceAdapter.body Old.normalBody)
def skipped := RawSourceAdapterLoop.loop Old.stopped (RawSourceAdapter.body Old.normalBody)
def witness : Nonempty (RawSourceAdapter.Adapter ctx [] false false continueStmt) := ⟨continued⟩

theorem breakExit : (Solidity.Yul.Checks.RawAdapterLoopHorizon.broken.run 3 Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawAdapterLoopHorizon.broken.run 3 Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty).2 Solidity.Yul.Checks.RawAdapterLoopHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawAdapterLoopHorizon.broken.run 3 Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty).2 Solidity.Yul.Checks.RawAdapterLoopHorizon.small).val = 257 := by
 exact ⟨rfl,rfl,rfl⟩

theorem continueExit : (Solidity.Yul.Checks.RawAdapterLoopHorizon.continued.run 5 Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawAdapterLoopHorizon.continued.run 5 Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty).2 Solidity.Yul.Checks.RawAdapterLoopHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawAdapterLoopHorizon.continued.run 5 Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty).2 Solidity.Yul.Checks.RawAdapterLoopHorizon.small).val = 257 := by
 exact ⟨rfl,rfl,rfl⟩

theorem normalExit : (Solidity.Yul.Checks.RawAdapterLoopHorizon.normal.run 10 Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawAdapterLoopHorizon.normal.run 10 Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty).2 Solidity.Yul.Checks.RawAdapterLoopHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawAdapterLoopHorizon.normal.run 10 Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty).2 Solidity.Yul.Checks.RawAdapterLoopHorizon.small).val = 257 := by
 exact ⟨rfl,rfl,rfl⟩

theorem continueStable : ∀ extra : Nat, Solidity.Yul.Checks.RawAdapterLoopHorizon.continued.run (5+extra) Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty = Solidity.Yul.Checks.RawAdapterLoopHorizon.continued.run 5 Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty := by
 intro extra
 exact Solidity.Yul.RawAdapterLoopHorizon.extension Solidity.Yul.Checks.RawAdapterLoopHorizon.ctx [] false false (.local .here) Solidity.Yul.Checks.RawAdapterLoopHorizon.read _ Solidity.Yul.Checks.RawAdapterLoopHorizon.Old.mutatingContinue 5 extra Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty (by change (Solidity.Yul.Checks.RawAdapterLoopHorizon.continued.run 5 Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawAdapterLoopHorizon.continueExit).1]; intro bad; cases bad)

theorem allFuelAgreement : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawAdapterLoopHorizon.ctx),
 Solidity.Yul.RawSourceAdapterLoop.run Solidity.Yul.Checks.RawAdapterLoopHorizon.read (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawAdapterLoopHorizon.Old.mutatingContinue) fuel state =
 Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawAdapterLoopHorizon.read Solidity.Yul.Checks.RawAdapterLoopHorizon.Old.mutatingContinue fuel state := by
 intro fuel state
 exact Solidity.Yul.RawAdapterLoopHorizon.body_agrees Solidity.Yul.Checks.RawAdapterLoopHorizon.ctx [] false false (.local .here) Solidity.Yul.Checks.RawAdapterLoopHorizon.read _ Solidity.Yul.Checks.RawAdapterLoopHorizon.Old.mutatingContinue fuel state

theorem earlyTimeout : (Solidity.Yul.Checks.RawAdapterLoopHorizon.continued.run 4 Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty).1 = .error .timeout := by
 rfl

theorem cleanSource : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawAdapterLoopHorizon.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawAdapterLoopHorizon.env)),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawAdapterLoopHorizon.continued.run fuel Solidity.Yul.Checks.RawAdapterLoopHorizon.initial).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawAdapterLoopHorizon.continueStmt Solidity.Yul.Checks.RawAdapterLoopHorizon.initial.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawAdapterLoopHorizon.env,Solidity.Yul.Checks.RawAdapterLoopHorizon.initial.world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawAdapterLoopHorizon.continued.run fuel Solidity.Yul.Checks.RawAdapterLoopHorizon.initial) := by
 intro glob frame fuel nps ph
 exact Solidity.Yul.Checks.RawAdapterLoopHorizon.continued.correct glob frame fuel nps ph Solidity.Yul.Checks.RawAdapterLoopHorizon.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _)

theorem falseSkip : (Solidity.Yul.Checks.RawAdapterLoopHorizon.skipped.run 2 Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawAdapterLoopHorizon.skipped.run 2 Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty).2 Solidity.Yul.Checks.RawAdapterLoopHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawAdapterLoopHorizon.skipped.run 2 Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty).2 Solidity.Yul.Checks.RawAdapterLoopHorizon.small).val = 257 := by
 exact ⟨rfl,rfl,rfl⟩

theorem normalStable : ∀ extra : Nat, Solidity.Yul.Checks.RawAdapterLoopHorizon.normal.run (10+extra) Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty = Solidity.Yul.Checks.RawAdapterLoopHorizon.normal.run 10 Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty := by
 intro extra
 exact Solidity.Yul.RawAdapterLoopHorizon.extension Solidity.Yul.Checks.RawAdapterLoopHorizon.ctx [] false false (.local .here) Solidity.Yul.Checks.RawAdapterLoopHorizon.read _ Solidity.Yul.Checks.RawAdapterLoopHorizon.Old.normalBody 10 extra Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty (by change (Solidity.Yul.Checks.RawAdapterLoopHorizon.normal.run 10 Solidity.Yul.Checks.RawAdapterLoopHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawAdapterLoopHorizon.normalExit).1]; intro bad; cases bad)
#print axioms Solidity.Yul.RawAdapterLoopHorizon.body_agrees
#print axioms Solidity.Yul.RawAdapterLoopHorizon.successor
#print axioms Solidity.Yul.RawAdapterLoopHorizon.extension
#print axioms breakExit
#print axioms continueExit
#print axioms normalExit
#print axioms continueStable
#print axioms allFuelAgreement
#print axioms earlyTimeout
#print axioms cleanSource
#print axioms falseSkip
#print axioms normalStable
end Solidity.Yul.Checks.RawAdapterLoopHorizon
