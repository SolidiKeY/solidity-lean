import Solidity.Yul.RawInitializedForPostHorizon
import Solidity.Yul.Checks.RawForPostHorizon
/-! Actual initialized same-context for-post adapters: initializer effects,
terminal stuck control, whole dirty frames and a separate clean Source boundary.
H30 shared registration remains a coordinator integration obligation. -/
namespace Solidity.Yul.Checks.RawInitializedForPostHorizon
namespace Old
export Solidity.Yul.Checks.RawForPostHorizon
 (ctx env dirty initial flag small read writeFalse continuation deep)
export Solidity.Yul.Checks.RawControlledWhileHorizon (singleItems normalBody stopped)
end Old
export Old (ctx env dirty initial flag small read)
def start : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .ifThen (.assign (.local .here) (.bool true)) .skip
def startProof : RawLoopBody.Supported ctx [] false false start :=
 .ifThen (.assign .here (.base (.literal true))) .skip
def skipProof : RawLoopBody.Supported ctx [] false false .skip := .skip
def breakProof : RawLoopBody.Supported ctx [] false false .brk := .break_
def deepExpr : Solidity.Source.RExpr env ctx.tys .bool :=
 .unary .not (.unary .not (.unary .not (.unary .not (.bool true))))
def continueStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .forLoop start (.some (.local .here)) (.some (.assign (.local .here) (.bool false))) .cont
def breakStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .forLoop .brk (.some deepExpr) (.some deepExpr) .skip
def refuseStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .forLoop .cont (.some deepExpr) (.some deepExpr) .skip
def falseStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .forLoop .skip (.some (.bool false)) (.some deepExpr) (.block Old.singleItems)
def normalStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .forLoop .skip (.some (.local .here)) (.some (.assign (.local .here) (.bool false))) (.block Old.singleItems)
def continued : RawSourceAdapter.Adapter ctx [] false false continueStmt :=
 RawSourceForPost.Initialized.adapter (RawSourceAdapter.body startProof)
 read Old.writeFalse (RawSourceAdapter.body Old.continuation)
def refusedBreak : RawSourceAdapter.Adapter ctx [] false false breakStmt :=
 RawSourceForPost.Initialized.adapter (RawSourceAdapter.body breakProof)
 Old.deep Old.deep (RawSourceAdapter.body skipProof)
def refusedContinue : RawSourceAdapter.Adapter ctx [] false false refuseStmt :=
 RawSourceForPost.Initialized.adapter (RawSourceAdapter.body Old.continuation)
 Old.deep Old.deep (RawSourceAdapter.body skipProof)
def stopped : RawSourceAdapter.Adapter ctx [] false false falseStmt :=
 RawSourceForPost.Initialized.adapter (RawSourceAdapter.body skipProof)
 Old.stopped Old.deep (RawSourceAdapter.body Old.normalBody)
def normal : RawSourceAdapter.Adapter ctx [] false false normalStmt :=
 RawSourceForPost.Initialized.adapter (RawSourceAdapter.body skipProof)
 read Old.writeFalse (RawSourceAdapter.body Old.normalBody)
def witness : Nonempty (RawSourceAdapter.Adapter ctx [] false false continueStmt) := ⟨continued⟩
theorem initializedExit : (Solidity.Yul.Checks.RawInitializedForPostHorizon.continued.run 4 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForPostHorizon.continued.run 4 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForPostHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForPostHorizon.continued.run 4 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForPostHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem breakRefusal : (Solidity.Yul.Checks.RawInitializedForPostHorizon.refusedBreak.run 2 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).1 = .error (.stuck "for initializer") ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForPostHorizon.refusedBreak.run 2 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForPostHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForPostHorizon.refusedBreak.run 2 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForPostHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem continueRefusal : (Solidity.Yul.Checks.RawInitializedForPostHorizon.refusedContinue.run 2 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).1 = .error (.stuck "for initializer") ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForPostHorizon.refusedContinue.run 2 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForPostHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForPostHorizon.refusedContinue.run 2 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForPostHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem completedStable : ∀ extra : Nat, Solidity.Yul.Checks.RawInitializedForPostHorizon.continued.run (4+extra) Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty = Solidity.Yul.Checks.RawInitializedForPostHorizon.continued.run 4 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawInitializedForPostHorizon.adapterExtension Solidity.Yul.Checks.RawInitializedForPostHorizon.ctx [] false false _ Solidity.Yul.Checks.RawInitializedForPostHorizon.startProof _ Solidity.Yul.Checks.RawInitializedForPostHorizon.read _ Solidity.Yul.Checks.RawInitializedForPostHorizon.Old.writeFalse _ Solidity.Yul.Checks.RawInitializedForPostHorizon.Old.continuation 4 extra Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty (by change (Solidity.Yul.Checks.RawInitializedForPostHorizon.continued.run 4 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawInitializedForPostHorizon.initializedExit).1]; intro bad; cases bad)

theorem breakStable : ∀ extra : Nat, Solidity.Yul.Checks.RawInitializedForPostHorizon.refusedBreak.run (2+extra) Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty = Solidity.Yul.Checks.RawInitializedForPostHorizon.refusedBreak.run 2 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawInitializedForPostHorizon.adapterExtension Solidity.Yul.Checks.RawInitializedForPostHorizon.ctx [] false false _ Solidity.Yul.Checks.RawInitializedForPostHorizon.breakProof _ Solidity.Yul.Checks.RawInitializedForPostHorizon.Old.deep _ Solidity.Yul.Checks.RawInitializedForPostHorizon.Old.deep _ Solidity.Yul.Checks.RawInitializedForPostHorizon.skipProof 2 extra Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty (by change (Solidity.Yul.Checks.RawInitializedForPostHorizon.refusedBreak.run 2 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawInitializedForPostHorizon.breakRefusal).1]; intro bad; cases bad)

theorem earlyTimeout : (Solidity.Yul.Checks.RawInitializedForPostHorizon.continued.run 3 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).1 = .error .timeout := by
  rfl

theorem falseGuard : (Solidity.Yul.Checks.RawInitializedForPostHorizon.stopped.run 3 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForPostHorizon.stopped.run 3 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForPostHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForPostHorizon.stopped.run 3 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForPostHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem normalExit : (Solidity.Yul.Checks.RawInitializedForPostHorizon.normal.run 11 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForPostHorizon.normal.run 11 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForPostHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawInitializedForPostHorizon.normal.run 11 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).2 Solidity.Yul.Checks.RawInitializedForPostHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem normalStable : ∀ extra : Nat, Solidity.Yul.Checks.RawInitializedForPostHorizon.normal.run (11+extra) Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty = Solidity.Yul.Checks.RawInitializedForPostHorizon.normal.run 11 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawInitializedForPostHorizon.adapterExtension Solidity.Yul.Checks.RawInitializedForPostHorizon.ctx [] false false _ Solidity.Yul.Checks.RawInitializedForPostHorizon.skipProof _ Solidity.Yul.Checks.RawInitializedForPostHorizon.read _ Solidity.Yul.Checks.RawInitializedForPostHorizon.Old.writeFalse _ Solidity.Yul.Checks.RawInitializedForPostHorizon.Old.normalBody 11 extra Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty (by change (Solidity.Yul.Checks.RawInitializedForPostHorizon.normal.run 11 Solidity.Yul.Checks.RawInitializedForPostHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawInitializedForPostHorizon.normalExit).1]; intro bad; cases bad)

theorem cleanSource : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawInitializedForPostHorizon.env) (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawInitializedForPostHorizon.env)), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawInitializedForPostHorizon.continued.run fuel Solidity.Yul.Checks.RawInitializedForPostHorizon.initial).2 = true ∧ (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawInitializedForPostHorizon.continueStmt Solidity.Yul.Checks.RawInitializedForPostHorizon.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawInitializedForPostHorizon.env,Solidity.Yul.Checks.RawInitializedForPostHorizon.initial.world) = Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawInitializedForPostHorizon.continued.run fuel Solidity.Yul.Checks.RawInitializedForPostHorizon.initial) := by
  intro glob frame fuel nps ph
  exact Solidity.Yul.Checks.RawInitializedForPostHorizon.continued.correct glob frame fuel nps ph Solidity.Yul.Checks.RawInitializedForPostHorizon.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _)

#print axioms Solidity.Yul.RawInitializedForPostHorizon.successor
#print axioms Solidity.Yul.RawInitializedForPostHorizon.extension
#print axioms Solidity.Yul.RawInitializedForPostHorizon.adapterSuccessor
#print axioms Solidity.Yul.RawInitializedForPostHorizon.adapterExtension
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
end Solidity.Yul.Checks.RawInitializedForPostHorizon
