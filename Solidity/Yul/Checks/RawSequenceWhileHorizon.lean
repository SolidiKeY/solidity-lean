import Solidity.Yul.RawSequenceWhileHorizon
import Solidity.Yul.Checks.RawControlledWhileHorizon
namespace Solidity.Yul.Checks.RawSequenceWhileHorizon
namespace Old
export Solidity.Yul.Checks.RawControlledWhileHorizon
 (ctx env dirty initial flag small read breakBody mutatingContinue normalBody singleItems singleProof stopped)
end Old
export Old (ctx env dirty initial flag small read stopped)
def tailItems : Solidity.Source.RItems env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .stmt (.block Old.singleItems) .nil
def tailProof : RawControlSequence.Supported ctx [] false false tailItems :=
 .cons (.plain Old.singleProof) .nil
def breakItems : Solidity.Source.RItems env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .stmt (.ifThen (.local .here) .brk) tailItems
def breakProof : RawControlSequence.Supported ctx [] false false breakItems := .cons Old.breakBody tailProof
def continueItems : Solidity.Source.RItems env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .stmt (.ifThen (.unary .not (.assign (.local .here) (.bool false))) .cont) tailItems
def continueProof : RawControlSequence.Supported ctx [] false false continueItems := .cons Old.mutatingContinue tailProof
def normalItems : Solidity.Source.RItems env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .stmt (.block Old.singleItems) .nil
def normalProof : RawControlSequence.Supported ctx [] false false normalItems := .cons Old.normalBody .nil
def sourceLoop : Solidity.Source.RStmt env [] false ⟨false,false⟩ ctx.tys ctx.tys :=
 .whileLoop (.local .here) (.block continueItems)
def witness : Nonempty (RawControlSequence.Supported ctx [] false false continueItems) := ⟨continueProof⟩

theorem breakExit : (Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.breakProof 5 Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.breakProof 5 Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceWhileHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.breakProof 5 Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceWhileHorizon.small).val = 257 := by
 exact ⟨rfl,rfl,rfl⟩

theorem continueExit : (Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.continueProof 7 Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.continueProof 7 Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceWhileHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.continueProof 7 Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceWhileHorizon.small).val = 257 := by
 exact ⟨rfl,rfl,rfl⟩

theorem normalExit : (Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.normalProof 12 Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.normalProof 12 Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceWhileHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.normalProof 12 Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceWhileHorizon.small).val = 257 := by
 exact ⟨rfl,rfl,rfl⟩

theorem continueStable : ∀ extra : Nat, Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.continueProof (7+extra) Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty = Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.continueProof 7 Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty := by
 intro extra
 exact Solidity.Yul.RawSequenceWhileHorizon.extension Solidity.Yul.Checks.RawSequenceWhileHorizon.ctx [] false false (.local .here) Solidity.Yul.Checks.RawSequenceWhileHorizon.read _ Solidity.Yul.Checks.RawSequenceWhileHorizon.continueProof 7 extra Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty (by rw [(Solidity.Yul.Checks.RawSequenceWhileHorizon.continueExit).1]; intro bad; cases bad)

theorem breakStable : ∀ extra : Nat, Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.breakProof (5+extra) Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty = Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.breakProof 5 Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty := by
 intro extra
 exact Solidity.Yul.RawSequenceWhileHorizon.extension Solidity.Yul.Checks.RawSequenceWhileHorizon.ctx [] false false (.local .here) Solidity.Yul.Checks.RawSequenceWhileHorizon.read _ Solidity.Yul.Checks.RawSequenceWhileHorizon.breakProof 5 extra Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty (by rw [(Solidity.Yul.Checks.RawSequenceWhileHorizon.breakExit).1]; intro bad; cases bad)

theorem falseSkip : (Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.stopped Solidity.Yul.Checks.RawSequenceWhileHorizon.normalProof 2 Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.stopped Solidity.Yul.Checks.RawSequenceWhileHorizon.normalProof 2 Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceWhileHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.stopped Solidity.Yul.Checks.RawSequenceWhileHorizon.normalProof 2 Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceWhileHorizon.small).val = 257 := by
 exact ⟨rfl,rfl,rfl⟩

theorem earlyTimeout : (Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.continueProof 6 Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty).1 = .error .timeout := by
 rfl

theorem cleanSource : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawSequenceWhileHorizon.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawSequenceWhileHorizon.env)),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.continueProof fuel Solidity.Yul.Checks.RawSequenceWhileHorizon.initial).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawSequenceWhileHorizon.sourceLoop Solidity.Yul.Checks.RawSequenceWhileHorizon.initial.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawSequenceWhileHorizon.env,Solidity.Yul.Checks.RawSequenceWhileHorizon.initial.world) =
 Solidity.Yul.RawSequence.represented (Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.continueProof fuel Solidity.Yul.Checks.RawSequenceWhileHorizon.initial) := by
 intro glob frame fuel nps ph
 exact Solidity.Yul.RawSequenceWhile.correct (l := false) Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.continueProof glob frame fuel nps ph Solidity.Yul.Checks.RawSequenceWhileHorizon.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _)

theorem normalStable : ∀ extra : Nat, Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.normalProof (12+extra) Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty = Solidity.Yul.RawSequenceWhile.run Solidity.Yul.Checks.RawSequenceWhileHorizon.read Solidity.Yul.Checks.RawSequenceWhileHorizon.normalProof 12 Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty := by
 intro extra
 exact Solidity.Yul.RawSequenceWhileHorizon.extension Solidity.Yul.Checks.RawSequenceWhileHorizon.ctx [] false false (.local .here) Solidity.Yul.Checks.RawSequenceWhileHorizon.read _ Solidity.Yul.Checks.RawSequenceWhileHorizon.normalProof 12 extra Solidity.Yul.Checks.RawSequenceWhileHorizon.dirty (by rw [(Solidity.Yul.Checks.RawSequenceWhileHorizon.normalExit).1]; intro bad; cases bad)
#print axioms Solidity.Yul.RawSequenceWhileHorizon.successor
#print axioms Solidity.Yul.RawSequenceWhileHorizon.extension
#print axioms breakExit
#print axioms continueExit
#print axioms normalExit
#print axioms continueStable
#print axioms breakStable
#print axioms falseSkip
#print axioms earlyTimeout
#print axioms cleanSource
#print axioms normalStable
end Solidity.Yul.Checks.RawSequenceWhileHorizon
