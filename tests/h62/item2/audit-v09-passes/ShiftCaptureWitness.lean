import Solidity.Backend.Passes.ShiftCaptureControls
import tests.h62.item2.«audit-v09-passes».SourceExpressionContext

/-! Guard empty runtime shift-capture admission, recapturing the cleared count,
and replacing successful saturated-zero shifts with modulo counts or refusal.
Reuse shared typed Source constructors and fixed parameters; keep the frozen unchecked
Source evaluation and its real fuel boundary explicit. -/
namespace Solidity.Backend.Passes.AuditShiftCapture
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.Passes
open Backend.PrimitivePackets.Shifts
open Backend.MemoryOps.StructDefaults.WordControls (C bases)
open ShiftCaptureControls

theorem joint (left : Bool) (x k : Fin W) :
    StateRepr 1 1 64 (Frag.init Γ) (state x k) bases (input x k) ∧
    (ShiftCapture.whole (C := C) 1 left i j name).Input 1 64 bases (state x k)
      {(input x k) with stack := []} := by
  refine ⟨ShiftCaptureControls.represented x k, ?_⟩
  obtain ⟨_, _, _, captured, updated, _, _, tails⟩ := ShiftCaptureControls.inhabited left x k
  exact (tails []).1
def represented := @Solidity.Backend.Passes.ShiftCaptureControls.represented
def inhabited := @Solidity.Backend.Passes.ShiftCaptureControls.inhabited
def joined := @Solidity.Backend.Passes.ShiftCaptureControls.joined
def ordered := @Solidity.Backend.Passes.ShiftCaptureControls.ordered
def left_vector := @Solidity.Backend.Passes.ShiftCaptureControls.left_vector
def right_vector := @Solidity.Backend.Passes.ShiftCaptureControls.right_vector
def saturated := @Solidity.Backend.Passes.ShiftCaptureControls.saturated
def wrong_recapture := @Solidity.Backend.Passes.ShiftCaptureControls.wrong_recapture
def wrong_saturated_modulo := @Solidity.Backend.Passes.ShiftCaptureControls.wrong_saturated_modulo
def corrupted_tail := @Solidity.Backend.Passes.ShiftCaptureControls.corrupted_tail
def wrong_public := @Solidity.Backend.Passes.ShiftCaptureControls.wrong_public
def wrong_order_vector := @Solidity.Backend.Passes.ShiftCaptureControls.wrong_order_vector
def wrong_order_source := @Solidity.Backend.Passes.ShiftCaptureControls.wrong_order_source
def insufficient_frame := @Solidity.Backend.Passes.ShiftCaptureControls.insufficient_frame
def input_refused := @Solidity.Backend.Passes.ShiftCaptureControls.input_refused

/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.joint

/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.represented

/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.inhabited

/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.joined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.joined

/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.ordered

/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.left_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.left_vector

/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.right_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.right_vector

/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.saturated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.saturated

/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.wrong_recapture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.wrong_recapture

/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.wrong_saturated_modulo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.wrong_saturated_modulo

/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.corrupted_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.corrupted_tail

/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.wrong_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.wrong_public

/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.wrong_order_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.wrong_order_vector

/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.wrong_order_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.wrong_order_source

/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.insufficient_frame' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.insufficient_frame

/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.input_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.input_refused

def source_expression := @Solidity.Backend.Passes.ShiftCaptureControls.source_expression

namespace SourceCase

def locals (x k : Fin W) : Source.Locals Solidity.Backend.Passes.AuditSourceContext.E.layout
    [.int Source.IntTy.u256,.int Source.IntTy.u256] :=
  .cons (.int (x.val : Int) (word_range x))
    (.cons (.int (k.val : Int) (word_range k)) .nil)

theorem joint (pipeline : Roadmap.Pipeline) (checked : Bool) (extra : Nat)
    (left : Bool) (x k : Fin W) :
    (StateRepr 1 1 64 (Frag.init Γ) (state x k) bases (input x k) ∧
      (ShiftCapture.whole (C := C) 1 left i j name).Input 1 64 bases (state x k)
        {(input x k) with stack := []}) ∧
    ∃ (G : Source.Glob Solidity.Backend.Passes.AuditSourceContext.E) (F : Source.Fr) (s : Source.St Solidity.Backend.Passes.AuditSourceContext.E) (fuel : Nat),
      G.pipeline = pipeline ∧ F.checked = checked ∧ s = Solidity.Backend.Passes.AuditSourceContext.sourceState ∧ fuel = extra+3 ∧
      (Source.evalE G {F with checked := false} fuel
        (Backend.PrimitivePackets.Shifts.General.expression left .here (.there .here))).run (locals x k,s) =
        (.ok (.val (.int ((resultWord left x k).val : Int) (word_range (resultWord left x k)))),
          (locals x k,s)) := by
  refine ⟨AuditShiftCapture.joint left x k, Solidity.Backend.Passes.AuditSourceContext.globals pipeline, Solidity.Backend.Passes.AuditSourceContext.frame checked, Solidity.Backend.Passes.AuditSourceContext.sourceState,
    extra+3, rfl, rfl, rfl, rfl, ?_⟩
  exact ShiftCaptureControls.source_expression (Solidity.Backend.Passes.AuditSourceContext.globals pipeline) (Solidity.Backend.Passes.AuditSourceContext.frame checked) extra left x k Solidity.Backend.Passes.AuditSourceContext.sourceState

theorem short_fuel (pipeline : Roadmap.Pipeline) (checked left : Bool) (x k : Fin W) :
    (Source.evalE (Solidity.Backend.Passes.AuditSourceContext.globals pipeline) {Solidity.Backend.Passes.AuditSourceContext.frame checked with checked := false} 2
      (Backend.PrimitivePackets.Shifts.General.expression left .here (.there .here))).run
        (locals x k,Solidity.Backend.Passes.AuditSourceContext.sourceState) = (.error .timeout,(locals x k,Solidity.Backend.Passes.AuditSourceContext.sourceState)) := by
  cases pipeline <;> cases left <;> rfl

end SourceCase
/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.source_expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.source_expression
/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.SourceCase.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.SourceCase.joint
/-- info: 'Solidity.Backend.Passes.AuditShiftCapture.SourceCase.short_fuel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditShiftCapture.SourceCase.short_fuel
end Solidity.Backend.Passes.AuditShiftCapture
