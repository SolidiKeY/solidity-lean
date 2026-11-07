import Solidity.Yul.RawControlSequenceHorizon
import Solidity.Yul.Checks.RawLoopBodyHorizon

namespace Solidity.Yul.Checks.RawControlSequenceHorizon
namespace Old
export Solidity.Yul.Checks.RawLoopBodyHorizon
  (ctx env dirty initial flag small breakBody continueBody skipped)
export Solidity.Yul.Checks.RawLoopBodyHorizon.Old (items proof)
end Old
export Old (ctx env dirty initial flag small)
def tailItems : Solidity.Source.RItems env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
  .stmt (.block Old.items) .nil
def tailProof : RawControlSequence.Supported ctx [] false false tailItems :=
  .cons (.plain Old.proof) .nil
def breakItems : Solidity.Source.RItems env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
  .stmt (.ifThen (.local .here) .brk) tailItems
def breakProof : RawControlSequence.Supported ctx [] false false breakItems :=
  .cons Old.breakBody tailProof
def continueItems : Solidity.Source.RItems env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
  .stmt (.ifThen (.local .here) .cont) tailItems
def continueProof : RawControlSequence.Supported ctx [] false false continueItems :=
  .cons Old.continueBody tailProof
def normalItems : Solidity.Source.RItems env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
  .stmt (.ifThen (.assign (.local .here) (.bool false)) (.block Old.items)) tailItems
def normalProof : RawControlSequence.Supported ctx [] false false normalItems :=
  .cons Old.skipped tailProof
def witness : Nonempty (RawControlSequence.Supported ctx [] false false normalItems) := ⟨normalProof⟩
theorem breakShortCircuit : (Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.breakProof 3 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty).1 = .ok (.break_ rfl) ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.breakProof 3 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty).2 Solidity.Yul.Checks.RawControlSequenceHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.breakProof 3 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty).2 Solidity.Yul.Checks.RawControlSequenceHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩


theorem continueShortCircuit : (Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.continueProof 3 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty).1 = .ok (.continue_ rfl) ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.continueProof 3 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty).2 Solidity.Yul.Checks.RawControlSequenceHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.continueProof 3 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty).2 Solidity.Yul.Checks.RawControlSequenceHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩


theorem breakStable : ∀ extra : Nat, Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.breakProof (3+extra) Solidity.Yul.Checks.RawControlSequenceHorizon.dirty = Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.breakProof 3 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawControlSequenceHorizon.extension Solidity.Yul.Checks.RawControlSequenceHorizon.ctx [] false false _ Solidity.Yul.Checks.RawControlSequenceHorizon.breakProof 3 extra Solidity.Yul.Checks.RawControlSequenceHorizon.dirty (by rw [(Solidity.Yul.Checks.RawControlSequenceHorizon.breakShortCircuit).1]; intro bad; cases bad)


theorem continueStable : ∀ extra : Nat, Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.continueProof (3+extra) Solidity.Yul.Checks.RawControlSequenceHorizon.dirty = Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.continueProof 3 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawControlSequenceHorizon.extension Solidity.Yul.Checks.RawControlSequenceHorizon.ctx [] false false _ Solidity.Yul.Checks.RawControlSequenceHorizon.continueProof 3 extra Solidity.Yul.Checks.RawControlSequenceHorizon.dirty (by rw [(Solidity.Yul.Checks.RawControlSequenceHorizon.continueShortCircuit).1]; intro bad; cases bad)


theorem normalPartial : (Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.normalProof 11 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.normalProof 11 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty).2 Solidity.Yul.Checks.RawControlSequenceHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.normalProof 11 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty).2 Solidity.Yul.Checks.RawControlSequenceHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩


theorem normalComplete : (Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.normalProof 12 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.normalProof 12 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty).2 Solidity.Yul.Checks.RawControlSequenceHorizon.flag).val = 1 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.normalProof 12 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty).2 Solidity.Yul.Checks.RawControlSequenceHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩


theorem normalStable : ∀ extra : Nat, Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.normalProof (12+extra) Solidity.Yul.Checks.RawControlSequenceHorizon.dirty = Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.normalProof 12 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawControlSequenceHorizon.extension Solidity.Yul.Checks.RawControlSequenceHorizon.ctx [] false false _ Solidity.Yul.Checks.RawControlSequenceHorizon.normalProof 12 extra Solidity.Yul.Checks.RawControlSequenceHorizon.dirty (by rw [(Solidity.Yul.Checks.RawControlSequenceHorizon.normalComplete).1]; intro bad; cases bad)


theorem blockOffset : Solidity.Yul.RawControlSequence.block Solidity.Yul.Checks.RawControlSequenceHorizon.normalProof 13 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty = Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.normalProof 12 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty := by
  rfl


theorem blockStable : ∀ extra : Nat, Solidity.Yul.RawControlSequence.block Solidity.Yul.Checks.RawControlSequenceHorizon.normalProof (13+extra) Solidity.Yul.Checks.RawControlSequenceHorizon.dirty = Solidity.Yul.RawControlSequence.block Solidity.Yul.Checks.RawControlSequenceHorizon.normalProof 13 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawControlSequenceHorizon.blockExtension Solidity.Yul.Checks.RawControlSequenceHorizon.ctx [] false false _ Solidity.Yul.Checks.RawControlSequenceHorizon.normalProof 13 extra Solidity.Yul.Checks.RawControlSequenceHorizon.dirty (by rw [Solidity.Yul.Checks.RawControlSequenceHorizon.blockOffset,(Solidity.Yul.Checks.RawControlSequenceHorizon.normalComplete).1]; intro bad; cases bad)


theorem earlyTimeouts : Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.breakProof 0 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty = (.error .timeout,Solidity.Yul.Checks.RawControlSequenceHorizon.dirty) ∧ (Solidity.Yul.RawControlSequence.run Solidity.Yul.Checks.RawControlSequenceHorizon.breakProof 2 Solidity.Yul.Checks.RawControlSequenceHorizon.dirty).1 = .error .timeout := by
  exact ⟨rfl,rfl⟩


theorem cleanSource : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawControlSequenceHorizon.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawControlSequenceHorizon.env)),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawControlSequence.block Solidity.Yul.Checks.RawControlSequenceHorizon.breakProof fuel Solidity.Yul.Checks.RawControlSequenceHorizon.initial).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph (.block Solidity.Yul.Checks.RawControlSequenceHorizon.breakItems) Solidity.Yul.Checks.RawControlSequenceHorizon.initial.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawControlSequenceHorizon.env,Solidity.Yul.Checks.RawControlSequenceHorizon.initial.world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawControlSequence.block Solidity.Yul.Checks.RawControlSequenceHorizon.breakProof fuel Solidity.Yul.Checks.RawControlSequenceHorizon.initial) := by
  intro glob frame fuel nps ph
  exact Solidity.Yul.RawControlSequence.block_correct Solidity.Yul.Checks.RawControlSequenceHorizon.breakProof glob frame fuel nps ph Solidity.Yul.Checks.RawControlSequenceHorizon.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _)

#print axioms Solidity.Yul.RawControlSequenceHorizon.successor
#print axioms Solidity.Yul.RawControlSequenceHorizon.blockSuccessor
#print axioms Solidity.Yul.RawControlSequenceHorizon.extension
#print axioms Solidity.Yul.RawControlSequenceHorizon.blockExtension
#print axioms breakShortCircuit
#print axioms continueShortCircuit
#print axioms breakStable
#print axioms continueStable
#print axioms normalPartial
#print axioms normalComplete
#print axioms normalStable
#print axioms blockOffset
#print axioms blockStable
#print axioms earlyTimeouts
#print axioms cleanSource
end Solidity.Yul.Checks.RawControlSequenceHorizon
