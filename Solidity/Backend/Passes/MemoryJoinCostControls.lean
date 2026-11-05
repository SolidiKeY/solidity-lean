import Solidity.Backend.Passes.MemoryJoinCost
import Solidity.Backend.Passes.AllocatingControls
import Solidity.Backend.Passes.MappedTail

namespace Solidity.Backend.Passes.MemoryJoinCost.Controls
open Evm Evm.Memory Evm.Compiler
open Backend.Passes.Controls.Fixture
open AllocatingControls

def appendAllocation : Prog C Γ (.mem (.array (.prim .uint)) :: Γ) :=
  .cons (.declMem (.array (.prim .uint)) (.user "more")
    (some (.newArr (.lit 3 rfl) rfl)) rfl rfl) .nil

def suffixCode : CompiledProg 1 allocationStage.frag appendAllocation :=
  (Memory.compileProg 1 allocationStage.frag appendAllocation).get (by decide)

theorem prefix_public : Memory.compileProg 1 (Frag.init [])
    ReachabilityControls.populatedBuilder = some allocationStage := by
  unfold allocationStage
  exact (Option.some_get _).symm

theorem suffix_public : Memory.compileProg 1 allocationStage.frag appendAllocation = some suffixCode := by
  unfold suffixCode
  exact (Option.some_get _).symm

theorem suffix_cost : allocationCostProg appendAllocation σ = 4 := by decide

theorem total_cost : allocationCostProg (ReachabilityControls.populatedBuilder.join appendAllocation)
    (State.init C) = 9 := by
  rw [successful_prefix _ _ _ _ ReachabilityControls.fresh_state_reaches_fixture]
  change allocationStage.cert.cost (State.init C) + allocationCostProg appendAllocation σ = 9
  rw [reached_cost,suffix_cost]

def joined_selection := public_join allocationStage suffixCode prefix_public suffix_public (State.init C)

/-- Positive allocator ownership is inhabited. The suffix consumes four cells
at the actual selected map/cursor after the five-cell prefix, at every tail. -/
theorem reached_budget :
    ∃ (middle : Machine) (selected : Nat → Fin W), ∀ tail,
      run allocationStage.code {initialMachine with stack := tail} =
        .ok {middle with stack := tail} 0 ∧
      MappedOutput (.memory allocationStage) 1 6 initialBase (State.init C)
        {initialMachine with stack := tail} σ {middle with stack := tail} selected ∧
      {middle with stack := tail}.mem 0 = w[21] ∧
      (Compilation.memory suffixCode).Input 1 6 selected σ {middle with stack := tail} ∧
      AllocationInput 1 6 4 σ selected {middle with stack := tail} := by
  obtain ⟨middle,selected,_,_,allTails⟩ := compilation_success_shared_mapped
    (.memory allocationStage) prefix_input (by rfl) ReachabilityControls.fresh_state_reaches_fixture
  refine ⟨middle,selected,?_⟩
  intro tail
  obtain ⟨ran,mapped⟩ := allTails tail
  change MappedOutput _ 1 _ _ _ _ _ _ _ at mapped
  have budget : AllocationInput 1 6
      (allocationCostProg (ReachabilityControls.populatedBuilder.join appendAllocation) (State.init C))
      (State.init C) initialBase {initialMachine with stack := tail} := by
    refine .inr ⟨by decide,⟨16,by decide⟩,initial_repr.2.mem_eq rfl,?_⟩
    rw [total_cost]
    decide
  have suffixBudget := suffix_allocation_input ReachabilityControls.populatedBuilder appendAllocation
    (State.init C) _ ReachabilityControls.fresh_state_reaches_fixture budget mapped.2.2
  have owner := mapped.2.2 ⟨16,by decide⟩ (by decide) (initial_repr.2.mem_eq rfl)
    (by change 16 + allocationStage.cert.cost (State.init C) < W; rw [reached_cost]; decide)
  have cursor : {middle with stack := tail}.mem 0 = w[21] := by
    simpa only [reached_cost] using owner.arrays.free.cell
  have rightInput : (Compilation.memory suffixCode).Input 1 6 selected σ {middle with stack := tail} :=
    ⟨mapped.1,by decide,suffixBudget⟩
  exact ⟨ran,mapped,cursor,rightInput,by simpa only [suffix_cost] using suffixBudget⟩

private def readCell (n : Nat) : Evm.Out → Option Nat
  | .ok machine _ => match machine.mem n with | .val word => some word.val | _ => none
  | _ => none

private theorem cell0 : readCell 4 (run allocationStage.code initialMachine) = some 0 := by decide +kernel
private theorem cell1 : readCell 2 (run allocationStage.code initialMachine) = some 16 := by decide +kernel
private theorem cell2 : readCell 3 (run allocationStage.code initialMachine) = some 16 := by decide +kernel
private theorem cell3 : readCell 1 (run allocationStage.code initialMachine) = some 19 := by decide +kernel
private theorem cell4 : readCell 17 (run allocationStage.code initialMachine) = some 7 := by decide +kernel
private theorem cell5 : readCell 18 (run allocationStage.code initialMachine) = some 9 := by decide +kernel
private theorem cell6 : readCell 20 (run allocationStage.code initialMachine) = some 4 := by decide +kernel
private theorem cell7 : readCell 0 (run allocationStage.code initialMachine) = some 21 := by decide +kernel

theorem complete_prefix :
    [4,2,3,1,17,18,20,0].mapM (fun n => readCell n (run allocationStage.code initialMachine)) =
      some [0,16,16,19,7,9,4,21] := by
  simp only [List.mapM_cons,List.mapM_nil,cell0,cell1,cell2,cell3,cell4,cell5,cell6,cell7]
  rfl

theorem wrong_total :
    allocationCostProg (ReachabilityControls.populatedBuilder.join appendAllocation) (State.init C) ≠ 5 := by
  rw [total_cost]
  decide

def failPrefix : Prog C [] [] := .cons .revert .nil
def failCode : CompiledProg 1 (Frag.init []) failPrefix :=
  (Memory.compileProg 1 (Frag.init []) failPrefix).get (by decide)

theorem fail_source : failPrefix.run (State.init C) = .error .revert := by rfl

theorem skipped_allocation :
    allocationCostProg (failPrefix.join ReachabilityControls.populatedBuilder) (State.init C) = 0 ∧
    allocationCostProg ReachabilityControls.populatedBuilder (State.init C) = 5 := by
  constructor
  · rw [failed_prefix _ _ _ _ fail_source]
    rfl
  · exact reached_cost

/-- An accepted allocating suffix is unreachable after the actual typed
revert; no suffix success, post-failure map or capacity is assumed. -/
theorem failed_public :
    ∃ joined : CompiledProg 1 (Frag.init []) (failPrefix.join ReachabilityControls.populatedBuilder),
      Memory.compileProg 1 (Frag.init []) (failPrefix.join ReachabilityControls.populatedBuilder) = some joined ∧
      joined.cert.cost (State.init C) = 0 ∧ ∀ tail,
        run joined.code {initialMachine with stack := tail} = .revert := by
  have failPublic : Memory.compileProg 1 (Frag.init []) failPrefix = some failCode := by
    unfold failCode
    exact (Option.some_get _).symm
  obtain ⟨joined,accepted,_,code,cost⟩ :=
    public_join failCode allocationStage failPublic prefix_public (State.init C)
  refine ⟨joined,accepted,skipped_allocation.1,?_⟩
  intro tail
  rw [code]
  apply run_append_revert
  rfl

#print axioms reached_budget
#print axioms failed_public
end Solidity.Backend.Passes.MemoryJoinCost.Controls
