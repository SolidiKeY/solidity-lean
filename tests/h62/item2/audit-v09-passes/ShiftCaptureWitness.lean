import Solidity.Backend.Passes.ShiftCaptureControls

/-! Guard empty runtime shift-capture admission, recapturing the cleared count,
and replacing successful saturated-zero shifts with modulo counts or refusal.
The Source expression tuple is accounted separately; target witnesses give it no credit. -/
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
end Solidity.Backend.Passes.AuditShiftCapture
