import Solidity.Yul.RawAdapterSequenceLoopHorizon
import Solidity.Yul.Checks.RawSequenceWhileHorizon
namespace Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon
namespace Old
export Solidity.Yul.Checks.RawSequenceWhileHorizon
 (ctx env dirty initial flag small read breakItems breakProof continueItems continueProof normalItems normalProof)
end Old
export Old (ctx env dirty initial flag small read)
def breakStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys := .whileLoop (.local .here) (.block Old.breakItems)
def continueStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys := .whileLoop (.local .here) (.block Old.continueItems)
def normalStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys := .whileLoop (.local .here) (.block Old.normalItems)
def broken : RawSourceAdapter.Adapter ctx [] false false breakStmt :=
 RawSourceAdapterLoop.loop read (RawSourceAdapter.block (RawSourceAdapter.sequence Old.breakProof))
def continued : RawSourceAdapter.Adapter ctx [] false false continueStmt :=
 RawSourceAdapterLoop.loop read (RawSourceAdapter.block (RawSourceAdapter.sequence Old.continueProof))
def normal : RawSourceAdapter.Adapter ctx [] false false normalStmt :=
 RawSourceAdapterLoop.loop read (RawSourceAdapter.block (RawSourceAdapter.sequence Old.normalProof))
def witness : Nonempty (RawSourceAdapter.Adapter ctx [] false false continueStmt) := ⟨continued⟩

theorem breakExit : (Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.broken.run 5 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.broken.run 5 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.dirty).2 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.broken.run 5 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.dirty).2 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.small).val = 257 := by
 exact ⟨rfl,rfl,rfl⟩

theorem continueExit : (Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.continued.run 7 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.continued.run 7 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.dirty).2 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.continued.run 7 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.dirty).2 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.small).val = 257 := by
 exact ⟨rfl,rfl,rfl⟩

theorem normalExit : (Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.normal.run 12 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.normal.run 12 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.dirty).2 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.normal.run 12 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.dirty).2 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.small).val = 257 := by
 exact ⟨rfl,rfl,rfl⟩

theorem continueStable : ∀ extra : Nat, Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.continued.run (7+extra) Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.dirty = Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.continued.run 7 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.dirty := by
 intro extra
 exact Solidity.Yul.RawAdapterSequenceLoopHorizon.extension Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.ctx [] false false Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.Old.continueItems Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.Old.continueProof (.local .here) Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.read 7 extra Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.dirty (by change (Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.continued.run 7 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.continueExit).1]; intro bad; cases bad)

theorem allFuelBlock : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.ctx),
 (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.Old.continueProof)).run fuel state =
 Solidity.Yul.RawControlSequence.block Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.Old.continueProof fuel state := by
 intro fuel state
 exact Solidity.Yul.RawAdapterSequenceLoopHorizon.block_agrees Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.ctx [] false false Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.Old.continueItems Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.Old.continueProof fuel state

theorem allFuelDriver : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.ctx),
 Solidity.Yul.RawSourceAdapterLoop.run Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.read (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.Old.continueProof)) fuel state =
 Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.read Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.Old.continueProof fuel state := by
 intro fuel state
 exact Solidity.Yul.RawAdapterSequenceLoopHorizon.body_agrees Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.ctx [] false false Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.Old.continueItems Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.Old.continueProof (.local .here) Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.read fuel state

theorem earlyTimeout : (Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.continued.run 6 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.dirty).1 = .error .timeout := by
 rfl

theorem cleanSource : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.env)),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.continued.run fuel Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.initial).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.continueStmt Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.initial.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.env,Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.initial.world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.continued.run fuel Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.initial) := by
 intro glob frame fuel nps ph
 exact Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.continued.correct glob frame fuel nps ph Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _)

theorem normalStable : ∀ extra : Nat, Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.normal.run (12+extra) Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.dirty = Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.normal.run 12 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.dirty := by
 intro extra
 exact Solidity.Yul.RawAdapterSequenceLoopHorizon.extension Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.ctx [] false false Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.Old.normalItems Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.Old.normalProof (.local .here) Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.read 12 extra Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.dirty (by change (Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.normal.run 12 Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.dirty).1 ≠ .error .timeout; rw [(Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon.normalExit).1]; intro bad; cases bad)
#print axioms Solidity.Yul.RawAdapterSequenceLoopHorizon.block_agrees
#print axioms Solidity.Yul.RawAdapterSequenceLoopHorizon.body_agrees
#print axioms Solidity.Yul.RawAdapterSequenceLoopHorizon.successor
#print axioms Solidity.Yul.RawAdapterSequenceLoopHorizon.extension
#print axioms breakExit
#print axioms continueExit
#print axioms normalExit
#print axioms continueStable
#print axioms allFuelBlock
#print axioms allFuelDriver
#print axioms earlyTimeout
#print axioms cleanSource
#print axioms normalStable
end Solidity.Yul.Checks.RawAdapterSequenceLoopHorizon
