import Solidity.Backend.Passes.UnsignedDependentScope
import Solidity.Backend.Passes.UnsignedDependentControls

/-! Populated caller/heap controls for scope exit and physical slot reuse.
Every vector retains both operands, caller scalar/reference, cursor, reserved
word, sentinel and both old-array cells; cell7 distinguishes a stale context. -/
namespace Solidity.Backend.Passes.UnsignedDependentScopeControls
open Evm Evm.Memory Evm.Compiler Backend.PrimitivePackets
open UnsignedDependentScope
open UnsignedMul.WideControls (F target machine represented)
open UnsignedMul.WideControls.Seed (C bases)
def qn : Var := .user "quotient"
def rn : Var := .user "remainder"
def reuseName : Var := .user "reused"
def actual := whole (C := C) 1 F qn rn reuseName

theorem inhabited (x y : Fin W) (divisor : (y.val : Int) ≠ 0) (numerator : (x.val : Int) ≠ 0) :
    type_of% (reused qn rn reuseName (represented x y) (by decide) divisor numerator) :=
  reused qn rn reuseName (represented x y) (by decide) divisor numerator

def cells : List Nat := [7,6,5,4,3,2,1,0,16,63,128,129]
def observe : Evm.Out → Option (List Word × List Word)
  | .ok m _ => some (cells.map m.mem,m.stack)
  | _ => none

theorem initial_vector : (cells.map (machine (wmod 17) (wmod 5)).mem,(machine (wmod 17) (wmod 5)).stack) =
    ([w[0],w[0],w[0],w[17],w[5],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

theorem scope_vector : observe (run (outer (C := C) 1 F qn rn).code (machine (wmod 17) (wmod 5))) =
    some ([w[0],w[3],w[3],w[17],w[5],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

theorem reused_vector : observe (run actual.code (machine (wmod 17) (wmod 5))) =
    some ([w[0],w[3],w[42],w[17],w[5],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

theorem zero_quotient_success : observe (run actual.code (machine (wmod 3) (wmod 17))) =
    some ([w[0],w[0],w[42],w[3],w[17],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

theorem first_failure (tail : List Word) : run actual.code {(machine (wmod 17) (wmod 0)) with stack := tail} = .revert :=
  (failure qn rn reuseName (represented (wmod 17) (wmod 0)) (by decide) tail).mpr (.inl rfl)
theorem second_failure (tail : List Word) : run actual.code {(machine (wmod 0) (wmod 5)) with stack := tail} = .revert :=
  (failure qn rn reuseName (represented (wmod 0) (wmod 5)) (by decide) tail).mpr (.inr rfl)

/-- This is independently accepted at the stale, pre-drop context. Its actual
write lands at7 instead of the reused quotient slot5. -/
def staleProgram : Prog C (.val .uint :: .val .uint :: UnsignedDiv.modelContext UnsignedDependentControls.Tail)
    (.val .uint :: .val .uint :: .val .uint :: UnsignedDiv.modelContext UnsignedDependentControls.Tail) :=
  .cons (.declLocal .uint reuseName (some (.simple (.lit 42 (by decide))))) .nil
def stale : CompiledProg 1 (UnsignedDependentCapture.code (C := C) 1 F qn rn).frag staleProgram :=
  (Memory.compileProg 1 (UnsignedDependentCapture.code (C := C) 1 F qn rn).frag staleProgram).get (by rfl)
theorem stale_selection : Memory.compileProg 1 (UnsignedDependentCapture.code (C := C) 1 F qn rn).frag staleProgram = some stale := by rfl

theorem stale_vector : observe (run ((outer (C := C) 1 F qn rn).code ++ stale.code) (machine (wmod 17) (wmod 5))) =
    some ([w[42],w[3],w[3],w[17],w[5],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

/-- Reversing the actual emitted stages is a raw-instruction negative,
not a certified typed join across the different local contexts. -/
theorem wrong_order : observe (run ((receiver (C := C) 1 F qn rn reuseName).code ++
    (outer (C := C) 1 F qn rn).code) (machine (wmod 17) (wmod 5))) =
    some ([w[0],w[3],w[3],w[17],w[5],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

theorem corrupted_tail : observe (run actual.code {(machine (wmod 17) (wmod 5)) with stack := [w[88]]}) ≠
    some ([w[0],w[3],w[42],w[17],w[5],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

theorem insufficient_frame : ¬ (Compilation.memory (outer (C := C) 1 F qn rn)).Input 1 6 bases
    (target (wmod 17) (wmod 5)) (machine (wmod 17) (wmod 5)) := by
  intro h
  have bad : 7 ≤ 6 := h.2.1
  omega
theorem initial_input (x y : Fin W) : (Compilation.memory actual).Input 1 64 bases (target x y) (machine x y) :=
  whole_input qn rn reuseName (represented x y) (by decide)

theorem source_first_failure :
    (blockProgram (C := C) qn rn).run (target (wmod 17) (wmod 0)) = .error .revert ∧
    (joined (C := C) qn rn reuseName).run (target (wmod 17) (wmod 0)) = .error .revert :=
  source_failure qn rn reuseName (represented (wmod 17) (wmod 0)) (by decide) (.inl rfl)

theorem source_second_failure :
    (blockProgram (C := C) qn rn).run (target (wmod 0) (wmod 5)) = .error .revert ∧
    (joined (C := C) qn rn reuseName).run (target (wmod 0) (wmod 5)) = .error .revert :=
  source_failure qn rn reuseName (represented (wmod 0) (wmod 5)) (by decide) (.inr rfl)

/-- info: 'Solidity.Backend.Passes.UnsignedDependentScopeControls.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inhabited
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScopeControls.initial_vector' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms initial_vector
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScopeControls.scope_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scope_vector
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScopeControls.reused_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reused_vector
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScopeControls.zero_quotient_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zero_quotient_success
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScopeControls.first_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_failure
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScopeControls.second_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms second_failure
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScopeControls.stale_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stale_selection
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScopeControls.stale_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stale_vector
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScopeControls.wrong_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_order
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScopeControls.corrupted_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms corrupted_tail
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScopeControls.insufficient_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms insufficient_frame
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScopeControls.initial_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms initial_input
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScopeControls.source_first_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_first_failure
/-- info: 'Solidity.Backend.Passes.UnsignedDependentScopeControls.source_second_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_second_failure
end Solidity.Backend.Passes.UnsignedDependentScopeControls
