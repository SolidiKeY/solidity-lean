import Solidity.Frontend.ExecutableAst.Shared.Intrinsic

/-! # Exact-output executable obligation capture

Guards against recomputing a builder with public defaults: capture the actual
supplied callbacks/arguments and retain the exact result equation. This is not
source adequacy, request authentication or executable acceptance.
-/
namespace Solidity.Frontend.ExecutableAst.Shared

structure ObligationCaptureV2 (lower : BodyLoopLowerer) (pre : PlainEntryPre)
    (C : Contract) (name : String) (specified box : Bool) where
  formula : Fml C []
  equation : obligation lower pre C name specified box = .ok formula

/-- Invoke the unchanged computation once, retaining its error verbatim. -/
def obligationCaptureV2 (lower : BodyLoopLowerer) (pre : PlainEntryPre)
    (C : Contract) (name : String) (specified box : Bool) :
    Except String (ObligationCaptureV2 lower pre C name specified box) :=
  match h : obligation lower pre C name specified box with
  | .error error => .error error
  | .ok formula => .ok ⟨formula, h⟩

theorem obligationCaptureV2_forget (lower : BodyLoopLowerer) (pre : PlainEntryPre)
    (C : Contract) (name : String) (specified box : Bool) :
    (obligationCaptureV2 lower pre C name specified box).map (fun r => r.formula) =
      obligation lower pre C name specified box := by
  unfold obligationCaptureV2
  split <;> rename_i h <;> exact h.symm

end Solidity.Frontend.ExecutableAst.Shared
