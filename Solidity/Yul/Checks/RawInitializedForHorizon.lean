import Solidity.Yul.RawInitializedForHorizon
import Solidity.Yul.Checks.RawInitializedForPostHorizon
/-! Actual no-post initialized adapters reuse existing intrinsic fixtures.
Mutating initializer/body, stuck initializer controls and whole dirty frames are
checked separately from clean Source correctness. H30 registration is external. -/
namespace Solidity.Yul.Checks.RawInitializedForHorizon
namespace Old
export Solidity.Yul.Checks.RawInitializedForPostHorizon
 (ctx env dirty initial flag small read start startProof skipProof breakProof deepExpr)
export Solidity.Yul.Checks.RawControlledWhileHorizon (normalBody singleItems stopped mutatingContinue)
export Solidity.Yul.Checks.RawForPostHorizon (deep continuation)
end Old
export Old (ctx env dirty initial flag small read start startProof skipProof breakProof)
def continueStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .forLoop start (.some (.local .here)) .none
 (.ifThen (.unary .not (.assign (.local .here) (.bool false))) .cont)
def breakStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .forLoop .brk (.some Old.deepExpr) .none .skip
def refuseStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .forLoop .cont (.some Old.deepExpr) .none .skip
def falseStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .forLoop .skip (.some (.bool false)) .none (.block Old.singleItems)
def normalStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .forLoop .skip (.some (.local .here)) .none (.block Old.singleItems)
def continued : RawSourceAdapter.Adapter ctx [] false false continueStmt :=
 RawSourceAdapterFor.adapter (RawSourceAdapter.body startProof)
 read (RawSourceAdapter.body Old.mutatingContinue)
def refusedBreak : RawSourceAdapter.Adapter ctx [] false false breakStmt :=
 RawSourceAdapterFor.adapter (RawSourceAdapter.body breakProof)
 Old.deep (RawSourceAdapter.body skipProof)
def refusedContinue : RawSourceAdapter.Adapter ctx [] false false refuseStmt :=
 RawSourceAdapterFor.adapter (RawSourceAdapter.body Old.continuation)
 Old.deep (RawSourceAdapter.body skipProof)
def stopped : RawSourceAdapter.Adapter ctx [] false false falseStmt :=
 RawSourceAdapterFor.adapter (RawSourceAdapter.body skipProof)
 Old.stopped (RawSourceAdapter.body Old.normalBody)
def normal : RawSourceAdapter.Adapter ctx [] false false normalStmt :=
 RawSourceAdapterFor.adapter (RawSourceAdapter.body skipProof)
 read (RawSourceAdapter.body Old.normalBody)
def witness : Nonempty (RawSourceAdapter.Adapter ctx [] false false continueStmt) := ⟨continued⟩
theorem initializedExit : (Solidity.Yul.Checks.RawInitializedForHorizon.continued.run 6 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForHorizon.continued.run 6 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForHorizon.continued.run 6 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem breakRefusal : (Solidity.Yul.Checks.RawInitializedForHorizon.refusedBreak.run 2 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).1 = .error (.stuck "for initializer") ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForHorizon.refusedBreak.run 2 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForHorizon.refusedBreak.run 2 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem continueRefusal : (Solidity.Yul.Checks.RawInitializedForHorizon.refusedContinue.run 2 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).1 = .error (.stuck "for initializer") ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForHorizon.refusedContinue.run 2 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForHorizon.refusedContinue.run 2 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem completedStable : ∀ extra : Nat, Solidity.Yul.Checks.RawInitializedForHorizon.continued.run (6+extra) Solidity.Yul.Checks.RawInitializedForHorizon.dirty = Solidity.Yul.Checks.RawInitializedForHorizon.continued.run 6 Solidity.Yul.Checks.RawInitializedForHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawInitializedForHorizon.adapterExtension Solidity.Yul.Checks.RawInitializedForHorizon.ctx [] false false _ Solidity.Yul.Checks.RawInitializedForHorizon.startProof _ Solidity.Yul.Checks.RawInitializedForHorizon.read _ Solidity.Yul.Checks.RawInitializedForHorizon.Old.mutatingContinue 6 extra Solidity.Yul.Checks.RawInitializedForHorizon.dirty (by change (Solidity.Yul.Checks.RawInitializedForHorizon.continued.run 6 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawInitializedForHorizon.initializedExit).1]; intro bad; cases bad)

theorem breakStable : ∀ extra : Nat, Solidity.Yul.Checks.RawInitializedForHorizon.refusedBreak.run (2+extra) Solidity.Yul.Checks.RawInitializedForHorizon.dirty = Solidity.Yul.Checks.RawInitializedForHorizon.refusedBreak.run 2 Solidity.Yul.Checks.RawInitializedForHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawInitializedForHorizon.adapterExtension Solidity.Yul.Checks.RawInitializedForHorizon.ctx [] false false _ Solidity.Yul.Checks.RawInitializedForHorizon.breakProof _ Solidity.Yul.Checks.RawInitializedForHorizon.Old.deep _ Solidity.Yul.Checks.RawInitializedForHorizon.skipProof 2 extra Solidity.Yul.Checks.RawInitializedForHorizon.dirty (by change (Solidity.Yul.Checks.RawInitializedForHorizon.refusedBreak.run 2 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawInitializedForHorizon.breakRefusal).1]; intro bad; cases bad)

theorem earlyTimeout : (Solidity.Yul.Checks.RawInitializedForHorizon.continued.run 5 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).1 = .error .timeout := by
  rfl

theorem falseGuard : (Solidity.Yul.Checks.RawInitializedForHorizon.stopped.run 3 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForHorizon.stopped.run 3 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForHorizon.stopped.run 3 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem normalExit : (Solidity.Yul.Checks.RawInitializedForHorizon.normal.run 11 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForHorizon.normal.run 11 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForHorizon.normal.run 11 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem normalStable : ∀ extra : Nat, Solidity.Yul.Checks.RawInitializedForHorizon.normal.run (11+extra) Solidity.Yul.Checks.RawInitializedForHorizon.dirty = Solidity.Yul.Checks.RawInitializedForHorizon.normal.run 11 Solidity.Yul.Checks.RawInitializedForHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawInitializedForHorizon.adapterExtension Solidity.Yul.Checks.RawInitializedForHorizon.ctx [] false false _ Solidity.Yul.Checks.RawInitializedForHorizon.skipProof _ Solidity.Yul.Checks.RawInitializedForHorizon.read _ Solidity.Yul.Checks.RawInitializedForHorizon.Old.normalBody 11 extra Solidity.Yul.Checks.RawInitializedForHorizon.dirty (by change (Solidity.Yul.Checks.RawInitializedForHorizon.normal.run 11 Solidity.Yul.Checks.RawInitializedForHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawInitializedForHorizon.normalExit).1]; intro bad; cases bad)

theorem cleanSource : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawInitializedForHorizon.env) (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawInitializedForHorizon.env)), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawInitializedForHorizon.continued.run fuel Solidity.Yul.Checks.RawInitializedForHorizon.initial).2 = true ∧ (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawInitializedForHorizon.continueStmt Solidity.Yul.Checks.RawInitializedForHorizon.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawInitializedForHorizon.env,Solidity.Yul.Checks.RawInitializedForHorizon.initial.world) = Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawInitializedForHorizon.continued.run fuel Solidity.Yul.Checks.RawInitializedForHorizon.initial) := by
  intro glob frame fuel nps ph
  exact Solidity.Yul.Checks.RawInitializedForHorizon.continued.correct glob frame fuel nps ph Solidity.Yul.Checks.RawInitializedForHorizon.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _)

#print axioms Solidity.Yul.RawInitializedForHorizon.successor
#print axioms Solidity.Yul.RawInitializedForHorizon.extension
#print axioms Solidity.Yul.RawInitializedForHorizon.adapterSuccessor
#print axioms Solidity.Yul.RawInitializedForHorizon.adapterExtension
#print axioms initializedExit
#print axioms breakRefusal
#print axioms continueRefusal
#print axioms completedStable
#print axioms breakStable
#print axioms earlyTimeout
#print axioms falseGuard
#print axioms normalExit
#print axioms normalStable
#print axioms cleanSource
end Solidity.Yul.Checks.RawInitializedForHorizon
