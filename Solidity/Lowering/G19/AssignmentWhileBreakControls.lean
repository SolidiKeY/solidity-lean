import Solidity.Lowering.G19.AssignmentWhileBreak
import Solidity.Lowering.G19.AssignmentReturnFlagControls

/-! Actual mixed V07/P12 inputs. Neither branch may discard the condition
write; the private capture is scoped away. No physical StateRepr is claimed. -/
namespace Solidity.Lowering.G19.AssignmentWhileBreak.Controls
open Solidity.Lowering.V07
open Source.SemanticsExamples
namespace P
abbrev C := P12Controls.C
abbrev source := P12Controls.source
abbrev target := P12Controls.target
abbrev mapping := P12Controls.mapping
abbrev BindingRel := P12Controls.BindingRel
end P

def trueTarget := P.target.setLocal (.here : Idx P12Controls.TgtCtx (.val .bool)) true
def falseTarget := P.target.setLocal (.there .here : Idx P12Controls.TgtCtx (.val .bool)) false

theorem yes (pipeline : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.execS (MixedAssignmentControls.globals pipeline) {F0 with checked := checked}
      (fuel+3) 0 none (R := []) (M := false)
      (.whileLoop (l := false) (u := false) (.assign (.local .here) (.local (.there .here))) .brk)
      P.source.1).run (.nil,P.source.2) =
      (.ok (Source.Out.normal P12Controls.sourcePost.1),(.nil,P.source.2)) ∧
    (code P.mapping .here (.there .here) rfl rfl : Prog P.C _ _).run P.target =
      .ok ⟨trueTarget,List.prefix_refl _⟩ ∧
    P.mapping.Related P.BindingRel P12Controls.sourcePost.1 trueTarget.env := by
  rcases correct (MixedAssignmentControls.globals pipeline) {F0 with checked := checked}
    fuel 0 none (returns := []) (M := false) (l := false) (u := false)
    P.source P.target P.mapping P.BindingRel P12Controls.initial P12Controls.bool_reflect
    .here (.there .here) rfl rfl rfl rfl with ⟨src,tgt,related,_⟩
  exact ⟨src,tgt,related⟩

theorem no (pipeline : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.execS (MixedAssignmentControls.globals pipeline) {F0 with checked := checked}
      (fuel+3) 0 none (R := []) (M := false)
      (.whileLoop (l := false) (u := false) (.assign (.local (.there .here)) (.local .here)) .brk)
      P.source.1).run (.nil,P.source.2) =
      (.ok (Source.Out.normal AssignmentReturnFlag.Controls.falseSource.1),(.nil,P.source.2)) ∧
    (code P.mapping (.there .here) .here rfl rfl : Prog P.C _ _).run P.target =
      .ok ⟨falseTarget,List.prefix_refl _⟩ ∧
    P.mapping.Related P.BindingRel AssignmentReturnFlag.Controls.falseSource.1 falseTarget.env := by
  rcases correct (MixedAssignmentControls.globals pipeline) {F0 with checked := checked}
    fuel 0 none (returns := []) (M := false) (l := false) (u := false)
    P.source P.target P.mapping P.BindingRel P12Controls.initial P12Controls.bool_reflect
    (.there .here) .here rfl rfl rfl rfl with ⟨src,tgt,related,_⟩
  exact ⟨src,tgt,related⟩

theorem same_slot (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    (Source.execS (MixedAssignmentControls.globals pipeline) F0 (fuel+3) 0 none
      (R := []) (M := false)
      (.whileLoop (l := false) (u := false) (.assign (.local .here) (.local .here)) .brk)
      P.source.1).run (.nil,P.source.2) =
      (.ok (Source.Out.normal P.source.1),(.nil,P.source.2)) ∧
    (code P.mapping .here .here rfl rfl : Prog P.C _ _).run P.target =
      .ok ⟨P.target,List.prefix_refl _⟩ := by
  rcases correct (MixedAssignmentControls.globals pipeline) F0 fuel 0 none
    (returns := []) (M := false) (l := false) (u := false) P.source P.target P.mapping
    P.BindingRel P12Controls.initial P12Controls.bool_reflect .here .here rfl rfl rfl rfl with
      ⟨src,tgt,_,_⟩
  exact ⟨src,tgt⟩

def observe (program : Prog P.C P12Controls.TgtCtx P12Controls.TgtCtx) : TRes Bool :=
  (program.run P.target).map (fun out => TEnv.get .here out.st.env)

theorem write_seen : observe (code P.mapping .here (.there .here) rfl rfl) = .ok true := by
  unfold observe
  rw [(yes .legacy 0 true).2.1]
  rfl

/-- Folding a break loop to skip would lose the real condition assignment. -/
theorem skip_refused : observe (code P.mapping .here (.there .here) rfl rfl) ≠ observe .nil := by
  rw [write_seen]
  change (Except.ok true : TRes Bool) ≠ .ok false
  intro same
  cases same

theorem reference_frame :
    trueTarget.glob = P.target.glob ∧ trueTarget.heap.len P12Controls.memoryRef .dyn = 2 ∧
    TEnv.get (.there (.there (.there (.there .here)))) trueTarget.env = some P12Controls.memoryRef ∧
    TEnv.get (.there (.there (.there (.there (.there .here))))) trueTarget.env =
      some MixedAssignmentControls.storageRef :=
  ⟨rfl,P12Controls.live_memory_and_storage.2.1,rfl,rfl⟩

end Solidity.Lowering.G19.AssignmentWhileBreak.Controls
