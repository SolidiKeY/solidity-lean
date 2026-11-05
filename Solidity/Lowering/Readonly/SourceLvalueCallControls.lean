import Solidity.Lowering.Readonly.SourceLvalueCallEffects
import Solidity.Lowering.Readonly.CopyControls

/-! Actual typed key/location/payment helper runs. Static value calls halt their
caller; ordinary unaffordable calls return a failed child outcome. These are
Source observations, not target/native execution correspondence. -/
namespace Solidity.Lowering.Readonly.SourceLvalueCallControls
open Solidity.Source Solidity.Source.SemanticsExamples
open SourceHistory
namespace C
abbrev E := CopyControls.E
abbrev frame := CopyControls.frame
abbrev checkpoint := CopyControls.checkpoint
end C
def storedKey := (keyStep {C.frame with static := true} 12
  (RVal.val CopyControls.sourceRef) : EM C.E [] _).run (L0 C.E, C.checkpoint)
def literalKey := (keyStep {C.frame with static := true} 0
  (RVal.strLit [7,9]) : EM C.E [] _).run (L0 C.E, C.checkpoint)
def boolKey := (keyStep {C.frame with static := true} 0
  (RVal.val (.bool true)) : EM C.E [] _).run (L0 C.E, C.checkpoint)
def refusedKey := (keyStep {C.frame with static := true} 0
  (RVal.tuple .nil) : EM C.E [] _).run (L0 C.E, C.checkpoint)
def exhaustedKey := (keyStep {C.frame with static := true} 0
  (RVal.val CopyControls.sourceRef) : EM C.E [] _).run (L0 C.E, C.checkpoint)
def locator (n : Nat) := (evalLoc (GB (fun _ => .answer (.success [])))
  {FC with static := true} n
  (.state dX dX_ty rfl : RLVal EB [] uint)).run (L0 EB, sB)
def payment (mode hasValue : Bool) (out : Solidity.Roadmap.Outcome) :=
  (pay (GB (fun _ => .answer out)) {FC with static := mode} 8
    (.local .here : RExpr EB [.address true] (.address true))
    (if hasValue then lit 1 else lit 0)).run (.cons (.address ext) .nil, sB)

theorem observations : Solidity.Lowering.Readonly.SourceLvalueCallControls.storedKey.1 = .ok (.key [7,9]) ∧
 Solidity.Lowering.Readonly.SourceLvalueCallControls.storedKey.2.2.ex = Solidity.Lowering.Readonly.SourceLvalueCallControls.C.checkpoint.ex ∧
 Solidity.Lowering.Readonly.SourceLvalueCallControls.literalKey.1 = .ok (.key [7,9]) ∧
 Solidity.Lowering.Readonly.SourceLvalueCallControls.boolKey.1 = .ok (.key (Solidity.Source.wordBytes (Solidity.Source.SemanticsExamples.word 1))) ∧
 Solidity.Lowering.Readonly.SourceLvalueCallControls.refusedKey.1 = .error (.stuck "mapping key") ∧
 Solidity.Lowering.Readonly.SourceLvalueCallControls.exhaustedKey.1 = .error .timeout ∧
 (Solidity.Lowering.Readonly.SourceLvalueCallControls.locator 1).1 = .ok (.stor Solidity.Source.SemanticsExamples.dX.path) ∧
 (Solidity.Lowering.Readonly.SourceLvalueCallControls.locator 1).2.2.ex = Solidity.Source.SemanticsExamples.sB.ex ∧
 (Solidity.Lowering.Readonly.SourceLvalueCallControls.locator 0).1 = .error .timeout ∧
 (Solidity.Lowering.Readonly.SourceLvalueCallControls.payment true false (.success [7,9])).1 = .ok (.success [7,9]) ∧
 (Solidity.Lowering.Readonly.SourceLvalueCallControls.payment true false (.success [7,9])).2.2.ex = Solidity.Source.SemanticsExamples.sB.ex ∧
 (Solidity.Lowering.Readonly.SourceLvalueCallControls.payment true false (.revert [9])).1 = .ok (.revert [9]) ∧
 (Solidity.Lowering.Readonly.SourceLvalueCallControls.payment true true (.success [])).1 = .error (.revert []) ∧
 (Solidity.Lowering.Readonly.SourceLvalueCallControls.payment true true (.success [])).2.2.events = [] ∧
 (Solidity.Lowering.Readonly.SourceLvalueCallControls.payment false true (.success [])).1 = .ok (.revert []) ∧
 (Solidity.Lowering.Readonly.SourceLvalueCallControls.payment false true (.success [])).2.2.events = [] ∧
 (Solidity.Lowering.Readonly.SourceLvalueCallControls.payment false false (.success [7])).1 = .ok (.success [7]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

theorem local_client : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.evalLoc G F 1 (Solidity.Source.RLVal.local .here : Solidity.Source.RLVal E [.bool] .bool)) := by
  intro E G F
  exact Solidity.Lowering.Readonly.SourceHistory.evalLoc_succ G F 0
    (Solidity.Lowering.Readonly.SourceHistory.at_zero G) (.local .here)

theorem caller_halt_not_child_revert : (Solidity.Lowering.Readonly.SourceLvalueCallControls.payment true true (.success [])).1 ≠ (Solidity.Lowering.Readonly.SourceLvalueCallControls.payment false true (.success [])).1 := by
  rw [Solidity.Lowering.Readonly.SourceLvalueCallControls.observations.2.2.2.2.2.2.2.2.2.2.2.2.1,
    Solidity.Lowering.Readonly.SourceLvalueCallControls.observations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  intro same
  cases same

end Solidity.Lowering.Readonly.SourceLvalueCallControls
