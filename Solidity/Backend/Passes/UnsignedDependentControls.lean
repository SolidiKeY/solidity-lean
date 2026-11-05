import Solidity.Backend.Passes.UnsignedDependentFailure
import Solidity.Backend.PrimitivePackets.UnsignedMul.WideControls

/-! Actual public unsigned dependent captures over an old allocated array,
allocator cursor, caller scalar, reserved cell and nonempty saved stack. -/
namespace Solidity.Backend.Passes.UnsignedDependentControls
open Evm Evm.Memory Evm.Compiler Backend.PrimitivePackets
open UnsignedDependentCapture UnsignedDependentFailure
open UnsignedDiv (modelContext Uint)
open UnsignedMul.WideControls (F target machine represented)
open Source.SemanticsExamples
abbrev Tail : Ctx := [.val .uint,.mem UnsignedMul.WideControls.Seed.A]
def qname : Var := .user "quotient"
def rname : Var := .user "dependentRemainder"
def whole := code (C := UnsignedMul.WideControls.Seed.C) 1 F qname rname

theorem inhabited (x y : Fin W) (divisor : (y.val : Int) ≠ 0) (numerator : (x.val : Int) ≠ 0) :
    type_of% (success qname rname (represented x y) (by decide) divisor numerator) :=
  success qname rname (represented x y) (by decide) divisor numerator

theorem origins (pipeline : Roadmap.Pipeline) (checked : Bool) (fuel : Nat)
    (x y : Fin W) (divisor : (y.val : Int) ≠ 0) (numerator : (x.val : Int) ≠ 0) :
    type_of% (component_origins (G0 pipeline) {F0 with checked := checked} fuel .nil s0
      qname rname (represented x y) (by decide) divisor numerator) :=
  component_origins (G0 pipeline) {F0 with checked := checked} fuel .nil s0
    qname rname (represented x y) (by decide) divisor numerator

def cells : List Nat := [6,5,4,3,2,1,0,16,63,128,129]
def observe : Evm.Out → Option (List Word × List Word)
  | .ok m _ => some (cells.map m.mem,m.stack)
  | _ => none

theorem positive_vector : observe (run whole.code (machine (wmod 17) (wmod 5))) =
    some ([w[3],w[3],w[17],w[5],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

theorem zero_quotient_success : observe (run whole.code (machine (wmod 3) (wmod 17))) =
    some ([w[0],w[0],w[3],w[17],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

theorem first_failure : run whole.code (machine (wmod 17) (wmod 0)) = .revert :=
  (immediate qname rname (represented (wmod 17) (wmod 0)) rfl [w[77]]).2

theorem reached_failure (y : Fin W) (nonzero : (y.val : Int) ≠ 0) :
    type_of% (reached qname rname (represented (wmod 0) y) (by decide) nonzero rfl) :=
  reached qname rname (represented (wmod 0) y) (by decide) nonzero rfl

theorem reached_prefix_vector :
    observe (run (firstCode (C := UnsignedMul.WideControls.Seed.C) 1 F qname).code (machine (wmod 0) (wmod 5))) =
    some ([w[0],w[0],w[0],w[5],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

theorem second_failure : run whole.code (machine (wmod 0) (wmod 5)) = .revert :=
  (revert_iff qname rname (represented (wmod 0) (wmod 5)) (by decide) [w[77]]).mpr (.inr rfl)

theorem wrong_failure_stage :
    run (firstCode (C := UnsignedMul.WideControls.Seed.C) 1 F qname).code (machine (wmod 0) (wmod 5)) ≠ .revert := by
  intro failed
  have observation := reached_prefix_vector
  rw [failed] at observation
  cases observation

theorem stale_context : observe (run whole.code (machine (wmod 17) (wmod 5))) ≠
    some ([w[2],w[3],w[17],w[5],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

theorem corrupted_tail : observe (run whole.code (machine (wmod 17) (wmod 5))) ≠
    some ([w[3],w[3],w[17],w[5],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[88]]) := by decide +kernel

def wrongProgram : Prog UnsignedMul.WideControls.Seed.C (modelContext Tail) (.val .uint :: .val .uint :: modelContext Tail) :=
  .cons (.declLocal .uint rname (some (UnsignedDiv.modelMod UnsignedMul.WideControls.Seed.C Tail)))
    (.cons (.declLocal .uint qname (some (UnsignedDiv.modelDiv UnsignedMul.WideControls.Seed.C (.val .uint :: Tail)))) .nil)
def wrongCode : CompiledProg 1 F wrongProgram := (compileProg 1 F wrongProgram).get (by rfl)
theorem wrong_public : compileProg 1 F wrongProgram = some wrongCode := rfl

theorem wrong_order_vector : observe (run wrongCode.code (machine (wmod 17) (wmod 5))) =
    some ([w[0],w[2],w[17],w[5],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

theorem source_first_panic (pipeline : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :
    type_of% (UnsignedDiv.division_zero_packet (represented (wmod 17) (wmod 0))
      (G0 pipeline) {F0 with checked := checked} fuel .nil s0 rfl) :=
  UnsignedDiv.division_zero_packet (represented (wmod 17) (wmod 0))
    (G0 pipeline) {F0 with checked := checked} fuel .nil s0 rfl

theorem source_second_panic (pipeline : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :
    type_of% (reached_source (G0 pipeline) {F0 with checked := checked} fuel .nil s0
      qname rname (represented (wmod 0) (wmod 5)) (by decide) (by decide) rfl) :=
  reached_source (G0 pipeline) {F0 with checked := checked} fuel .nil s0
    qname rname (represented (wmod 0) (wmod 5)) (by decide) (by decide) rfl

theorem insufficient_frame :
    ¬ (Compilation.memory whole).Input 1 6 UnsignedMul.WideControls.Seed.bases
      (target (wmod 17) (wmod 5)) (machine (wmod 17) (wmod 5)) := by
  intro admitted
  have bound : 7 ≤ 6 := admitted.2.1
  omega

/-- info: 'Solidity.Backend.Passes.UnsignedDependentControls.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inhabited
/-- info: 'Solidity.Backend.Passes.UnsignedDependentControls.origins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms origins
/-- info: 'Solidity.Backend.Passes.UnsignedDependentControls.positive_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms positive_vector
/-- info: 'Solidity.Backend.Passes.UnsignedDependentControls.zero_quotient_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zero_quotient_success
/-- info: 'Solidity.Backend.Passes.UnsignedDependentControls.first_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_failure
/-- info: 'Solidity.Backend.Passes.UnsignedDependentControls.reached_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reached_failure
/-- info: 'Solidity.Backend.Passes.UnsignedDependentControls.reached_prefix_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reached_prefix_vector
/-- info: 'Solidity.Backend.Passes.UnsignedDependentControls.second_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms second_failure
/-- info: 'Solidity.Backend.Passes.UnsignedDependentControls.wrong_failure_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_failure_stage
/-- info: 'Solidity.Backend.Passes.UnsignedDependentControls.stale_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stale_context
/-- info: 'Solidity.Backend.Passes.UnsignedDependentControls.corrupted_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms corrupted_tail
/-- info: 'Solidity.Backend.Passes.UnsignedDependentControls.wrong_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_public
/-- info: 'Solidity.Backend.Passes.UnsignedDependentControls.wrong_order_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_order_vector
/-- info: 'Solidity.Backend.Passes.UnsignedDependentControls.source_first_panic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_first_panic
/-- info: 'Solidity.Backend.Passes.UnsignedDependentControls.source_second_panic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_second_panic
/-- info: 'Solidity.Backend.Passes.UnsignedDependentControls.insufficient_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms insufficient_frame
end Solidity.Backend.Passes.UnsignedDependentControls
