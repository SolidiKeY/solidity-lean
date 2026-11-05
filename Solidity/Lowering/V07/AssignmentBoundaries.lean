import Solidity.Lowering.V07.MixedAssignmentControls

namespace Solidity.Lowering.V07.AssignmentBoundaries
open Source.SemanticsExamples

def signedSource : Source.EMState E0 [.int Controls.i8,.int Controls.i8] :=
  (.cons (.int (-2) (by decide)) (.cons (.int 3 (by decide)) .nil),s0)
def signedTarget : State (default : Contract) [.val .int,.val .int] :=
  ((State.init default).push (integerValue Controls.i8 3 (by decide))).push
    (integerValue Controls.i8 (-2) (by decide))
def delta (p : Roadmap.Pipeline) : Int := -2-(if p = .legacy then 3 else -2)

theorem signed_delta_range (p : Roadmap.Pipeline) : Controls.i8.lo ≤ delta p ∧ delta p ≤ Controls.i8.hi := by
  unfold delta
  by_cases h : p = .legacy
  · simp only [h,if_true]; decide
  · simp only [h,if_false]; decide

theorem signed_transport (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.evalE (G0 p) {F0 with checked := checked} (fuel+4)
      (.binary .sub (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run signedSource =
      (.ok (.val (.int (delta p) (signed_delta_range p))),
        (signedSource.1.set (.there .here) (.int (-2) (by decide)),signedSource.2)) ∧
    (assignReadSubOperand p Controls.i8 (.there .here) .here).run signedTarget =
      .ok (⟨signedTarget.setLocal (.there .here) (integerValue Controls.i8 (-2) (by decide)),List.prefix_refl _⟩,
        .prim (integerValue Controls.i8 (delta p) (signed_delta_range p))) ∧
    IntValueRel Controls.i8 (.int (delta p) (signed_delta_range p) : Source.Val E0.layout (.int Controls.i8))
      (integerValue Controls.i8 (delta p) (signed_delta_range p)) :=
  assignment_subtraction_transport (G0 p) {F0 with checked := checked} fuel signedSource signedTarget
    Controls.i8 (.there .here) .here (.there .here) .here (-2) 3
    (by decide) (by decide) rfl rfl rfl rfl (signed_delta_range p)

theorem signed_order_difference : delta .legacy = -5 ∧ delta .viaIR = 0 := ⟨rfl,rfl⟩

theorem unsigned_underflow_checked {D : Source.Layout} :
    Source.binVal true .sub (.int 0 (by decide) : Source.Val D (.int .u8)) (.int 1 (by decide)) =
      .error (.revert (Source.panicData .arithmetic)) := by
  simp only [Source.binVal,Source.intBin,Source.intRes]
  rfl

theorem unsigned_underflow_unchecked {D : Source.Layout} :
    Source.binVal false .sub (.int 0 (by decide) : Source.Val D (.int .u8)) (.int 1 (by decide)) =
      .ok (.int 255 (by decide)) := by
  simp only [Source.binVal,Source.intBin,Source.intRes]
  rfl

theorem signed_minimum_in_range :
    BinOp.evalT .sub (integer_sub_accepts Controls.i8)
      (integerValue Controls.i8 (-128) (by decide)) (integerValue Controls.i8 0 (by decide)) =
      some (integerValue Controls.i8 (-128) (by decide)) :=
  integer_sub_eval Controls.i8 (-128) 0 (by decide) (by decide) (by decide)

theorem unsigned_maximum_in_range :
    BinOp.evalT .sub (integer_sub_accepts .u8)
      (integerValue .u8 255 (by decide)) (integerValue .u8 1 (by decide)) =
      some (integerValue .u8 254 (by decide)) :=
  integer_sub_eval .u8 255 1 (by decide) (by decide) (by decide)

end Solidity.Lowering.V07.AssignmentBoundaries
