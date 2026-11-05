import Solidity.Lowering.G19.AssignmentDoWhileContinue
import Solidity.Lowering.G19.AssignmentWhileBreakControls

/-! Actual mixed mapped clients and effectful/declaration suffix rejection. -/
namespace Solidity.Lowering.G19.AssignmentDoWhileContinue.Controls
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

theorem yes (pipeline : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) {tailΓ : Source.RCtx}
    (tail : Source.RItems MixedAssignmentControls.E [] false ⟨true,false⟩ P12Controls.SrcCtx tailΓ) :
    (Source.execS (MixedAssignmentControls.globals pipeline) {F0 with checked := checked}
      (fuel+6) 0 none (R := []) (M := false)
      (.doWhile (l := false) (u := false) (body .here (.there .here) tail) (.bool false))
      P.source.1).run (.nil,P.source.2) =
      (.ok (Source.Out.normal P12Controls.sourcePost.1),(.nil,P.source.2)) ∧
    (code P.mapping .here (.there .here) rfl rfl : Prog P.C _ _).run P.target =
      .ok ⟨trueTarget,List.prefix_refl _⟩ ∧
    P.mapping.Related P.BindingRel P12Controls.sourcePost.1 trueTarget.env := by
  rcases correct (MixedAssignmentControls.globals pipeline) {F0 with checked := checked}
    fuel 0 none (returns := []) (M := false) (l := false) (u := false)
    P.source P.target P.mapping P.BindingRel P12Controls.initial P12Controls.bool_reflect
    .here (.there .here) rfl rfl rfl rfl tail with ⟨src,tgt,related,_⟩
  exact ⟨src,tgt,related⟩

theorem no (pipeline : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) {tailΓ : Source.RCtx}
    (tail : Source.RItems MixedAssignmentControls.E [] false ⟨true,false⟩ P12Controls.SrcCtx tailΓ) :
    (Source.execS (MixedAssignmentControls.globals pipeline) {F0 with checked := checked}
      (fuel+6) 0 none (R := []) (M := false)
      (.doWhile (l := false) (u := false) (body (.there .here) .here tail) (.bool false))
      P.source.1).run (.nil,P.source.2) =
      (.ok (Source.Out.normal AssignmentReturnFlag.Controls.falseSource.1),(.nil,P.source.2)) ∧
    (code P.mapping (.there .here) .here rfl rfl : Prog P.C _ _).run P.target =
      .ok ⟨falseTarget,List.prefix_refl _⟩ ∧
    P.mapping.Related P.BindingRel AssignmentReturnFlag.Controls.falseSource.1 falseTarget.env := by
  rcases correct (MixedAssignmentControls.globals pipeline) {F0 with checked := checked}
    fuel 0 none (returns := []) (M := false) (l := false) (u := false)
    P.source P.target P.mapping P.BindingRel P12Controls.initial P12Controls.bool_reflect
    (.there .here) .here rfl rfl rfl rfl tail with ⟨src,tgt,related,_⟩
  exact ⟨src,tgt,related⟩

theorem same_slot (pipeline : Roadmap.Pipeline) (fuel : Nat) {tailΓ : Source.RCtx}
    (tail : Source.RItems MixedAssignmentControls.E [] false ⟨true,false⟩ P12Controls.SrcCtx tailΓ) :
    (Source.execS (MixedAssignmentControls.globals pipeline) F0 (fuel+6) 0 none
      (R := []) (M := false)
      (.doWhile (l := false) (u := false) (body .here .here tail) (.bool false))
      P.source.1).run (.nil,P.source.2) =
      (.ok (Source.Out.normal P.source.1),(.nil,P.source.2)) ∧
    (code P.mapping .here .here rfl rfl : Prog P.C _ _).run P.target =
      .ok ⟨P.target,List.prefix_refl _⟩ := by
  rcases correct (MixedAssignmentControls.globals pipeline) F0 fuel 0 none
    (returns := []) (M := false) (l := false) (u := false) P.source P.target P.mapping
    P.BindingRel P12Controls.initial P12Controls.bool_reflect .here .here rfl rfl rfl rfl tail with
      ⟨src,tgt,_,_⟩
  exact ⟨src,tgt⟩

/-- The skipped suffix would overwrite the body's true value if run. -/
theorem suffix_is_effectful :
    Source.evalE (MixedAssignmentControls.globals .legacy) F0 2
      (.assign (.local .here) (.bool false)) P12Controls.sourcePost =
      (.ok (.val (.bool false)),P.source) := by rfl

/-- Continue cannot be replaced by normal fallthrough into this suffix. -/
theorem dead_suffix_refused :
    (Source.execS (MixedAssignmentControls.globals .legacy) F0 6 0 none
      (R := []) (M := false)
      (.doWhile (l := false) (u := false)
        (body .here (.there .here)
          (.stmt (.expr (.assign (.local .here) (.bool false))) .nil)) (.bool false))
      P.source.1).run (.nil,P.source.2) ≠
      (.ok (Source.Out.normal P.source.1),(.nil,P.source.2)) := by
  rw [source_run (MixedAssignmentControls.globals .legacy) F0 0 0 none
    P.source.1 P.source.2 .here (.there .here) true rfl
    (.stmt (.expr (.assign (.local .here) (.bool false))) .nil)]
  intro same
  cases same

/-- The arbitrary suffix can extend the typed context; it is still skipped. -/
theorem declaring_suffix_skipped :
    (Source.execS (MixedAssignmentControls.globals .legacy) F0 6 0 none
      (R := []) (M := false)
      (.doWhile (l := false) (u := false)
        (body .here (.there .here) (.stmt (.declVar .bool) .nil)) (.bool false))
      P.source.1).run (.nil,P.source.2) =
      (.ok (Source.Out.normal P12Controls.sourcePost.1),(.nil,P.source.2)) :=
  source_run (MixedAssignmentControls.globals .legacy) F0 0 0 none
    P.source.1 P.source.2 .here (.there .here) true rfl (.stmt (.declVar .bool) .nil)

end Solidity.Lowering.G19.AssignmentDoWhileContinue.Controls
