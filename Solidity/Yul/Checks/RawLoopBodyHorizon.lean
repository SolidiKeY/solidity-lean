import Solidity.Yul.RawLoopBodyHorizon
import Solidity.Yul.Checks.RawSequenceHorizon

namespace Solidity.Yul.Checks.RawLoopBodyHorizon
namespace Old
export Solidity.Yul.Checks.RawSequenceHorizon (ctx env dirty initial flag small items proof)
end Old
export Old (ctx env dirty initial flag small)
def read : LocalBoolControl.Supported env ctx.tys (.local .here) := .base (.local .here)
def write (value : Bool) : LocalBoolControl.Supported env ctx.tys
    (.assign (.local .here) (.bool value)) := .assign .here (.base (.literal value))
def breakBody : RawLoopBody.Supported ctx [] false false (.ifThen (.local .here) .brk) :=
  .ifThen read .break_
def continueBody : RawLoopBody.Supported ctx [] false false (.ifThen (.local .here) .cont) :=
  .ifThen read .continue_
def skipped : RawLoopBody.Supported ctx [] false false
    (.ifThen (.assign (.local .here) (.bool false)) (.block Old.items)) :=
  .ifThen (write false) (.plain Old.proof)
def selected : RawLoopBody.Supported ctx [] false false
    (.ifThen (.assign (.local .here) (.bool true)) (.block Old.items)) :=
  .ifThen (write true) (.plain Old.proof)
def witness : Nonempty (RawLoopBody.Supported ctx [] false false
    (.ifThen (.assign (.local .here) (.bool true)) (.block Old.items))) := ⟨selected⟩
theorem dirtyCondition : (Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawLoopBodyHorizon.read 1 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).1 = .ok true ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawLoopBodyHorizon.read 1 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).2 Solidity.Yul.Checks.RawLoopBodyHorizon.flag).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawLoopBodyHorizon.read 1 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).2 Solidity.Yul.Checks.RawLoopBodyHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩


theorem conditionStable : ∀ extra : Nat, Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawLoopBodyHorizon.read (1+extra) Solidity.Yul.Checks.RawLoopBodyHorizon.dirty = Solidity.Yul.RawCondition.eval Solidity.Yul.Checks.RawLoopBodyHorizon.read 1 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawLoopBodyHorizon.conditionExtension Solidity.Yul.Checks.RawLoopBodyHorizon.ctx _ Solidity.Yul.Checks.RawLoopBodyHorizon.read 1 extra Solidity.Yul.Checks.RawLoopBodyHorizon.dirty (by rw [(Solidity.Yul.Checks.RawLoopBodyHorizon.dirtyCondition).1]; intro bad; cases bad)


theorem breakSelected : (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.breakBody 2 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).1 = .ok (.break_ rfl) ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.breakBody 2 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).2 Solidity.Yul.Checks.RawLoopBodyHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.breakBody 2 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).2 Solidity.Yul.Checks.RawLoopBodyHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩


theorem continueSelected : (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.continueBody 2 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).1 = .ok (.continue_ rfl) ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.continueBody 2 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).2 Solidity.Yul.Checks.RawLoopBodyHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.continueBody 2 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).2 Solidity.Yul.Checks.RawLoopBodyHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩


theorem falseSkipsDeepBody : (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.skipped 3 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.skipped 3 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).2 Solidity.Yul.Checks.RawLoopBodyHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.skipped 3 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).2 Solidity.Yul.Checks.RawLoopBodyHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩


theorem selectedPartial : (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.selected 10 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.selected 10 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).2 Solidity.Yul.Checks.RawLoopBodyHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.selected 10 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).2 Solidity.Yul.Checks.RawLoopBodyHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩


theorem selectedComplete : (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.selected 11 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.selected 11 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).2 Solidity.Yul.Checks.RawLoopBodyHorizon.flag).val = 1 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.selected 11 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).2 Solidity.Yul.Checks.RawLoopBodyHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩


theorem breakStable : ∀ extra : Nat, Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.breakBody (2+extra) Solidity.Yul.Checks.RawLoopBodyHorizon.dirty = Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.breakBody 2 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawLoopBodyHorizon.extension Solidity.Yul.Checks.RawLoopBodyHorizon.ctx [] false false _ Solidity.Yul.Checks.RawLoopBodyHorizon.breakBody 2 extra Solidity.Yul.Checks.RawLoopBodyHorizon.dirty (by rw [(Solidity.Yul.Checks.RawLoopBodyHorizon.breakSelected).1]; intro bad; cases bad)


theorem selectedStable : ∀ extra : Nat, Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.selected (11+extra) Solidity.Yul.Checks.RawLoopBodyHorizon.dirty = Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.selected 11 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawLoopBodyHorizon.extension Solidity.Yul.Checks.RawLoopBodyHorizon.ctx [] false false _ Solidity.Yul.Checks.RawLoopBodyHorizon.selected 11 extra Solidity.Yul.Checks.RawLoopBodyHorizon.dirty (by rw [(Solidity.Yul.Checks.RawLoopBodyHorizon.selectedComplete).1]; intro bad; cases bad)


theorem zeroTimeout : Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.breakBody 0 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty = (.error .timeout,Solidity.Yul.Checks.RawLoopBodyHorizon.dirty) ∧ (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.breakBody 1 Solidity.Yul.Checks.RawLoopBodyHorizon.dirty).1 = .error .timeout := by
  exact ⟨rfl,rfl⟩


theorem cleanSource : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawLoopBodyHorizon.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawLoopBodyHorizon.env)),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.selected fuel Solidity.Yul.Checks.RawLoopBodyHorizon.initial).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (.ifThen (.assign (.local .here) (.bool true)) (.block Solidity.Yul.Checks.RawLoopBodyHorizon.Old.items)) Solidity.Yul.Checks.RawLoopBodyHorizon.initial.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawLoopBodyHorizon.env,Solidity.Yul.Checks.RawLoopBodyHorizon.initial.world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawLoopBody.run Solidity.Yul.Checks.RawLoopBodyHorizon.selected fuel Solidity.Yul.Checks.RawLoopBodyHorizon.initial) := by
  intro glob frame fuel nps ph
  exact Solidity.Yul.RawLoopBody.correct Solidity.Yul.Checks.RawLoopBodyHorizon.selected glob frame fuel nps ph Solidity.Yul.Checks.RawLoopBodyHorizon.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _)

#print axioms Solidity.Yul.RawLoopBodyHorizon.conditionSuccessor
#print axioms Solidity.Yul.RawLoopBodyHorizon.successor
#print axioms Solidity.Yul.RawLoopBodyHorizon.conditionExtension
#print axioms Solidity.Yul.RawLoopBodyHorizon.extension
#print axioms dirtyCondition
#print axioms conditionStable
#print axioms breakSelected
#print axioms continueSelected
#print axioms falseSkipsDeepBody
#print axioms selectedPartial
#print axioms selectedComplete
#print axioms breakStable
#print axioms selectedStable
#print axioms zeroTimeout
#print axioms cleanSource
end Solidity.Yul.Checks.RawLoopBodyHorizon
