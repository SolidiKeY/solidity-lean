import Solidity.Lowering.G19.AssignmentReturnFlag
import Solidity.Lowering.V07.P12Controls

/-! Inhabited map-guided G19 clients over V07's actual mixed Bool/integer/
memory/storage fixture. No custom source/world relation or expected runner. -/
namespace Solidity.Lowering.G19.AssignmentReturnFlag.Controls
open Solidity.Lowering.V07
open Source.SemanticsExamples
namespace P
abbrev C := P12Controls.C
abbrev E := P12Controls.E
abbrev source := P12Controls.source
abbrev target := P12Controls.target
abbrev mapping := P12Controls.mapping
abbrev BindingRel := P12Controls.BindingRel
end P

theorem yes (pipeline : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.execS (MixedAssignmentControls.globals pipeline) {F0 with checked := checked}
      (fuel+3) 0 none (M := false) (k := ⟨false,false⟩)
      (.ifThen (.assign (.local .here) (.local (.there .here))) (.ret rfl)) P.source.1).run
      (.nil,P.source.2) = (.ok (Source.Out.ret P12Controls.sourcePost.1),(.nil,P.source.2)) ∧
    (code P.mapping .here (.there .here) rfl rfl : Prog P.C _ _).run P.target =
      .ok ⟨P12Controls.targetPost,List.prefix_refl _⟩ ∧
    (P.mapping.wk (Thin.drop (t := .val .bool) .refl)).Related P.BindingRel
      P12Controls.sourcePost.1 P12Controls.targetPost.env := by
  rcases correct (MixedAssignmentControls.globals pipeline) {F0 with checked := checked}
    fuel 0 none (M := false) (k := ⟨false,false⟩) P.source P.target P.mapping
    P.BindingRel P12Controls.initial P12Controls.bool_reflect .here (.there .here) rfl rfl rfl rfl with ⟨sourceRun,targetRun,related,_,_⟩
  exact ⟨sourceRun,targetRun,related⟩

def falseSource : Source.EMState P.E P12Controls.SrcCtx :=
  (P.source.1.set (.there .here) (.bool false),P.source.2)
def falseTarget : State P.C (.val .bool :: P12Controls.TgtCtx) :=
  (P.target.setLocal (.there .here) false).push (t := .val .bool) false

theorem no (pipeline : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.execS (MixedAssignmentControls.globals pipeline) {F0 with checked := checked}
      (fuel+3) 0 none (M := false) (k := ⟨false,false⟩)
      (.ifThen (.assign (.local (.there .here)) (.local .here)) (.ret rfl)) P.source.1).run
      (.nil,P.source.2) = (.ok (Source.Out.normal falseSource.1),(.nil,P.source.2)) ∧
    (code P.mapping (.there .here) .here rfl rfl : Prog P.C _ _).run P.target =
      .ok ⟨falseTarget,List.prefix_refl _⟩ ∧
    (P.mapping.wk (Thin.drop (t := .val .bool) .refl)).Related P.BindingRel
      falseSource.1 falseTarget.env := by
  rcases correct (MixedAssignmentControls.globals pipeline) {F0 with checked := checked}
    fuel 0 none (M := false) (k := ⟨false,false⟩) P.source P.target P.mapping
    P.BindingRel P12Controls.initial P12Controls.bool_reflect (.there .here) .here rfl rfl rfl rfl with ⟨sourceRun,targetRun,related,_,_⟩
  exact ⟨sourceRun,targetRun,related⟩

/-- Aliased source destination/RHS remain supported, with the same map. -/
theorem same_slot (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    (Source.execS (MixedAssignmentControls.globals pipeline) F0 (fuel+3) 0 none
      (M := false) (k := ⟨false,false⟩)
      (.ifThen (.assign (.local .here) (.local .here)) (.ret rfl)) P.source.1).run
      (.nil,P.source.2) = (.ok (Source.Out.normal P.source.1),(.nil,P.source.2)) ∧
    (code P.mapping .here .here rfl rfl : Prog P.C _ _).run P.target =
      .ok ⟨P.target.push (t := .val .bool) false,List.prefix_refl _⟩ := by
  rcases correct (MixedAssignmentControls.globals pipeline) F0 fuel 0 none
    (M := false) (k := ⟨false,false⟩) P.source P.target P.mapping P.BindingRel
    P12Controls.initial P12Controls.bool_reflect .here .here rfl rfl rfl rfl with ⟨sourceRun,targetRun,_,_,_⟩
  exact ⟨sourceRun,targetRun⟩

def observed : TRes Bool :=
  ((code P.mapping .here (.there .here) rfl rfl : Prog P.C _ _).run P.target).map
    (fun out => TEnv.get .here out.st.env)

theorem captured_true : observed = .ok true := by
  unfold observed
  rw [(yes .legacy 0 true).2.1]
  rfl

theorem stale_guard_refused : TEnv.get (.here : Idx P12Controls.TgtCtx (.val .bool)) P.target.env ≠
    (true : Bool) := by decide

theorem wrong_map_refused :
    P.mapping.slot (Source.Idx.here : Source.Idx P12Controls.SrcCtx .bool) ≠
      ⟨.val .bool,(Idx.there .here : Idx P12Controls.TgtCtx (.val .bool))⟩ := by
  intro same
  have impossible : 0=1 := congrArg (fun slot : (u : LTy) × Idx P12Controls.TgtCtx u =>
    slot.2.toNat) same
  cases impossible

/-- Existing memory/storage identities remain live in the reused mixed input. -/
theorem nontrivial_input :
    P.source.2.heap.get 0 = some ⟨.bytes .memory,.bytes [0,0]⟩ ∧
    P.target.heap.len P12Controls.memoryRef .dyn = 2 ∧
    P.E.pathTy MixedAssignmentControls.path = some (.bytes .storage) :=
  P12Controls.live_memory_and_storage

end Solidity.Lowering.G19.AssignmentReturnFlag.Controls
