import Solidity.Lowering.G19.AssignmentDoWhileBreak
import Solidity.Lowering.G19.AssignmentWhileBreakControls

/-! Mixed mapped clients: body writes once, arbitrary trailing condition is skipped. -/
namespace Solidity.Lowering.G19.AssignmentDoWhileBreak.Controls
open Solidity.Lowering.V07
open Source.SemanticsExamples
open AssignmentWhileBreak (code)
open AssignmentWhileBreak.Controls (trueTarget falseTarget)
namespace P
abbrev C := P12Controls.C
abbrev source := P12Controls.source
abbrev target := P12Controls.target
abbrev mapping := P12Controls.mapping
abbrev BindingRel := P12Controls.BindingRel
end P

theorem yes (pipeline : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) (condition : Source.RExpr MixedAssignmentControls.E P12Controls.SrcCtx .bool) :
    (Source.execS (MixedAssignmentControls.globals pipeline) {F0 with checked := checked}
      (fuel+6) 0 none (R := []) (M := false)
      (.doWhile (l := false) (u := false) (body .here (.there .here)) condition)
      P.source.1).run (.nil,P.source.2) =
      (.ok (Source.Out.normal P12Controls.sourcePost.1),(.nil,P.source.2)) ∧
    (code P.mapping .here (.there .here) rfl rfl : Prog P.C _ _).run P.target =
      .ok ⟨trueTarget,List.prefix_refl _⟩ ∧
    P.mapping.Related P.BindingRel P12Controls.sourcePost.1 trueTarget.env := by
  rcases correct (MixedAssignmentControls.globals pipeline) {F0 with checked := checked}
    fuel 0 none (returns := []) (M := false) (l := false) (u := false)
    P.source P.target P.mapping P.BindingRel P12Controls.initial P12Controls.bool_reflect
    .here (.there .here) rfl rfl rfl rfl condition with ⟨src,tgt,related,_⟩
  exact ⟨src,tgt,related⟩

theorem no (pipeline : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) (condition : Source.RExpr MixedAssignmentControls.E P12Controls.SrcCtx .bool) :
    (Source.execS (MixedAssignmentControls.globals pipeline) {F0 with checked := checked}
      (fuel+6) 0 none (R := []) (M := false)
      (.doWhile (l := false) (u := false) (body (.there .here) .here) condition)
      P.source.1).run (.nil,P.source.2) =
      (.ok (Source.Out.normal AssignmentReturnFlag.Controls.falseSource.1),(.nil,P.source.2)) ∧
    (code P.mapping (.there .here) .here rfl rfl : Prog P.C _ _).run P.target =
      .ok ⟨falseTarget,List.prefix_refl _⟩ ∧
    P.mapping.Related P.BindingRel AssignmentReturnFlag.Controls.falseSource.1 falseTarget.env := by
  rcases correct (MixedAssignmentControls.globals pipeline) {F0 with checked := checked}
    fuel 0 none (returns := []) (M := false) (l := false) (u := false)
    P.source P.target P.mapping P.BindingRel P12Controls.initial P12Controls.bool_reflect
    (.there .here) .here rfl rfl rfl rfl condition with ⟨src,tgt,related,_⟩
  exact ⟨src,tgt,related⟩

theorem same_slot (pipeline : Roadmap.Pipeline) (fuel : Nat) (condition : Source.RExpr MixedAssignmentControls.E P12Controls.SrcCtx .bool) :
    (Source.execS (MixedAssignmentControls.globals pipeline) F0 (fuel+6) 0 none
      (R := []) (M := false)
      (.doWhile (l := false) (u := false) (body .here .here) condition)
      P.source.1).run (.nil,P.source.2) =
      (.ok (Source.Out.normal P.source.1),(.nil,P.source.2)) ∧
    (code P.mapping .here .here rfl rfl : Prog P.C _ _).run P.target =
      .ok ⟨P.target,List.prefix_refl _⟩ := by
  rcases correct (MixedAssignmentControls.globals pipeline) F0 fuel 0 none
    (returns := []) (M := false) (l := false) (u := false) P.source P.target P.mapping
    P.BindingRel P12Controls.initial P12Controls.bool_reflect .here .here rfl rfl rfl rfl condition with
      ⟨src,tgt,_,_⟩
  exact ⟨src,tgt⟩

/-- This exact trailing condition has a real write if evaluated on the post-body locals. -/
theorem condition_is_effectful :
    Source.evalE (MixedAssignmentControls.globals .legacy) F0 2
      (.assign (.local .here) (.bool false)) (plan := none) (calldataKnown := true) P12Controls.sourcePost =
      (.ok (.val (.bool false)),P.source) := by rfl

/-- Yet the actual loop keeps the body's true write, not that trailing false write. -/
theorem trailing_write_refused :
    (Source.execS (MixedAssignmentControls.globals .legacy) F0 6 0 none
      (R := []) (M := false)
      (.doWhile (l := false) (u := false) (body .here (.there .here))
        (.assign (.local .here) (.bool false))) P.source.1).run (.nil,P.source.2) ≠
      (.ok (Source.Out.normal P.source.1),(.nil,P.source.2)) := by
  rw [source_run (MixedAssignmentControls.globals .legacy) F0 0 0 none
    P.source.1 P.source.2 .here (.there .here) true rfl
    (.assign (.local .here) (.bool false))]
  intro same
  cases same

end Solidity.Lowering.G19.AssignmentDoWhileBreak.Controls
