import Solidity.Backend.Passes.ReturnedMemoryCapture
import Solidity.Backend.Passes.MemoryJoinFrameControls
import Solidity.Backend.Passes.MemoryJoinedAllocationControls

namespace Solidity.Backend.Passes.ReturnedMemoryCapture.Controls
open Evm Evm.Memory Evm.Compiler
open Backend.Passes.Controls.Fixture AllocatingControls MemoryJoinCost.Controls MemoryJoinedAllocation
open MemoryJoinedAllocation.Controls (wholeCode whole_public)

noncomputable def fresh : HRef (suffixOut σ).st.H (.array (.prim .uint)) :=
  (σ.alloc (defaultArray .uint ⟨3,by decide⟩)).2

theorem fresh_bound : TEnv.get .here (suffixOut σ).st.env = some fresh := rfl

theorem whole_input : (Compilation.memory wholeCode).Input 1 6 initialBase (State.init C) initialMachine := by
  apply (MemoryJoinFrame.input_iff (P := ReachabilityControls.populatedBuilder)
    (Q := appendAllocation) wholeCode initialBase (State.init C) initialMachine).mpr
  have budget := MemoryJoinFrame.Controls.actual_budget
  rw [MemoryJoinCost.cost_join] at budget
  exact ⟨initial_repr.1,by decide,by decide,budget⟩

/-- Fresh allocation is real: selection, source run, original admission and
returned reference are derived, not assumed preservation facts. -/
def application := readback wholeCode whole_public whole_input (by rfl) joined_source fresh fresh_bound

def pointerCode : List Evm.Instr := wholeCode.code ++ [.mload 5]
def cells : List Nat := [5,4,2,3,1,6,16,17,18,19,20,21,22,23,24,0]
private def observation : Evm.Out → Option (List Word × List Word)
  | .ok machine 0 => some (cells.map machine.mem,machine.stack)
  | _ => none

theorem complete_pointer_observation : observation
    (run pointerCode {initialMachine with stack := [w[77],w[88]]}) =
    some ([w[21],w[0],w[16],w[16],w[19],w[0],w[2],w[7],w[9],w[1],w[4],w[3],w[0],w[0],w[0],w[25]],
      [w[21],w[77],w[88]]) := by decide +kernel

/-- Using the stale initial map would read zero for the fresh id, not21. -/
theorem stale_initial_map : initialBase fresh.id = ⟨0,by decide⟩ := rfl

theorem stale_readback_refused : observation
    (run pointerCode {initialMachine with stack := [w[77],w[88]]}) ≠
    some ([w[21],w[0],w[16],w[16],w[19],w[0],w[2],w[7],w[9],w[1],w[4],w[3],w[0],w[0],w[0],w[25]],
      [w[0],w[77],w[88]]) := by
  rw [complete_pointer_observation]
  decide

theorem saved_tail_refused : observation
    (run pointerCode {initialMachine with stack := [w[77],w[88]]}) ≠
    some ([w[21],w[0],w[16],w[16],w[19],w[0],w[2],w[7],w[9],w[1],w[4],w[3],w[0],w[0],w[0],w[25]],
      [w[21],w[78],w[88]]) := by
  rw [complete_pointer_observation]
  decide

/-- info: 'Solidity.Backend.Passes.ReturnedMemoryCapture.Controls.application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms application
/-- info: 'Solidity.Backend.Passes.ReturnedMemoryCapture.Controls.complete_pointer_observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms complete_pointer_observation
/-- info: 'Solidity.Backend.Passes.ReturnedMemoryCapture.Controls.stale_readback_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stale_readback_refused
/-- info: 'Solidity.Backend.Passes.ReturnedMemoryCapture.Controls.saved_tail_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms saved_tail_refused
end Solidity.Backend.Passes.ReturnedMemoryCapture.Controls
