import Solidity.Backend.Passes.MemoryJoinFrame
import Solidity.Backend.Passes.MemoryJoinedAllocation
import Solidity.Backend.Passes.Frame

namespace Solidity.Backend.Passes.MemoryJoinFrame.Controls
open Evm Evm.Memory Evm.Compiler
open Backend.Passes.Controls.Fixture
open AllocatingControls MemoryJoinCost.Controls

theorem actual_budget : AllocationInput 1 6
    (allocationCostProg (ReachabilityControls.populatedBuilder.join appendAllocation) (State.init C))
    (State.init C) initialBase initialMachine := by
  refine .inr ⟨by decide,⟨16,by decide⟩,initial_repr.2,?_⟩
  rw [total_cost]
  decide

def admitted := public_admission allocationStage suffixCode prefix_public suffix_public
  initialBase (State.init C) initialMachine initial_repr.1 (by decide) (by decide) actual_budget

/-- Nonempty actual public join admission supplies its execution certificate;
its canonical output map and cursor remain shared before all saved tails. -/
theorem admitted_execution :
    ∃ joined : CompiledProg 1 (Frag.init [])
      (ReachabilityControls.populatedBuilder.join appendAllocation),
      Memory.compileProg 1 (Frag.init [])
        (ReachabilityControls.populatedBuilder.join appendAllocation) = some joined ∧
      (Compilation.memory joined).Input 1 6 initialBase (State.init C) initialMachine ∧
      MappedBoundaryLink (.memory allocationStage) (.memory suffixCode)
        1 6 initialBase (State.init C) initialMachine ∧
      ∃ (final : Machine) (selected : Nat → Fin W), ∀ tail,
        run joined.code {initialMachine with stack := tail} = .ok {final with stack := tail} 0 ∧
        MappedOutput (.memory joined) 1 6 initialBase (State.init C)
          {initialMachine with stack := tail} (MemoryJoinedAllocation.suffixOut σ).st
          {final with stack := tail} selected ∧
        {final with stack := tail}.mem 0 = w[25] := by
  obtain ⟨joined,accepted,_,_,input,_,link⟩ := admitted
  obtain ⟨final,selected,_,_,allTails⟩ := compilation_success_shared_mapped
    (.memory joined) input (by rfl) MemoryJoinedAllocation.joined_source
  refine ⟨joined,accepted,input,link,final,selected,?_⟩
  intro tail
  obtain ⟨ran,mapped⟩ := allTails tail
  change MappedOutput _ 1 _ _ _ _ _ _ _ at mapped
  have cost : joined.cert.cost (State.init C) = 9 := total_cost
  have grown := mapped.2.2 ⟨16,by decide⟩ (by decide) (initial_repr.2.mem_eq rfl)
    (by rw [cost]; decide)
  refine ⟨ran,mapped,?_⟩
  simpa only [cost] using grown.arrays.free.cell

theorem prefix_only_frame_is_insufficient
    (joined : CompiledProg 1 (Frag.init [])
      (ReachabilityControls.populatedBuilder.join appendAllocation)) :
    1 + frameNeedProg ReachabilityControls.populatedBuilder ≤ 5 ∧
    ¬ (Compilation.memory joined).Input 1 5 initialBase (State.init C) initialMachine := by
  refine ⟨by decide,?_⟩
  intro input
  have capacity := ((input_iff joined initialBase (State.init C) initialMachine).mp input).2.2.1
  change 6 ≤ 5 at capacity
  omega

def locals2 : Prog C [] [.val .uint,.val .uint] :=
  .cons (.declLocal .uint (.user "a") (some (.simple (.lit 11 rfl))))
    (.cons (.declLocal .uint (.user "b") (some (.simple (.lit 12 rfl)))) .nil)
def locals3 : Prog C [] [.val .uint,.val .uint,.val .uint] :=
  .cons (.declLocal .uint (.user "a") (some (.simple (.lit 21 rfl))))
    (.cons (.declLocal .uint (.user "b") (some (.simple (.lit 22 rfl))))
      (.cons (.declLocal .uint (.user "c") (some (.simple (.lit 23 rfl)))) .nil))
def scope2 : Prog C [] [] := .cons (.block locals2) .nil
def scope3 : Prog C [] [] := .cons (.block locals3) .nil

def firstCode : CompiledProg 1 (Frag.init []) scope2 :=
  (Memory.compileProg 1 (Frag.init []) scope2).get (by decide)
def secondCode : CompiledProg 1 firstCode.frag scope3 :=
  (Memory.compileProg 1 firstCode.frag scope3).get (by decide)

theorem scoped_maximum : frameNeedProg (scope2.join scope3) = 3 ∧
    frameNeedProg scope2 + frameNeedProg scope3 = 5 := by decide

theorem scoped_public : ∃ joined : CompiledProg 1 (Frag.init []) (scope2.join scope3),
    Memory.compileProg 1 (Frag.init []) (scope2.join scope3) = some joined ∧
    joined.code = firstCode.code ++ secondCode.code := by
  have left : Memory.compileProg 1 (Frag.init []) scope2 = some firstCode := (Option.some_get _).symm
  have right : Memory.compileProg 1 firstCode.frag scope3 = some secondCode := (Option.some_get _).symm
  obtain ⟨joined,accepted,_,code,_⟩ := MemoryJoinCost.public_join firstCode secondCode left right (State.init C)
  exact ⟨joined,accepted,code⟩

theorem scoped_slot_reuse :
    (match run (firstCode.code ++ secondCode.code) initialMachine with
      | .ok final _ => [final.mem 1,final.mem 2,final.mem 3,final.mem 4,final.mem 0]
      | _ => []) = [w[21],w[22],w[23],w[0],w[16]] := by decide +kernel

def unreachableAllocation : Prog C [] [.mem (.array (.prim .uint))] :=
  .cons (.declMem (.array (.prim .uint)) (.user "never")
    (some (.newArr (.lit 3 rfl) rfl)) rfl rfl) .nil

def unreachableCode : CompiledProg 1 (Frag.init [])
    (MemoryJoinCost.Controls.failPrefix.join unreachableAllocation) :=
  (Memory.compileProg 1 (Frag.init [])
    (MemoryJoinCost.Controls.failPrefix.join unreachableAllocation)).get (by decide)

theorem unreachable_public : Memory.compileProg 1 (Frag.init [])
    (MemoryJoinCost.Controls.failPrefix.join unreachableAllocation) = some unreachableCode := by
  exact (Option.some_get _).symm

theorem unreachable_frame_retained :
    allocationCostProg (MemoryJoinCost.Controls.failPrefix.join unreachableAllocation) (State.init C) = 0 ∧
    allocationCostProg unreachableAllocation (State.init C) = 4 ∧
    frameNeedProg (MemoryJoinCost.Controls.failPrefix.join unreachableAllocation) = 1 ∧
    (MemoryJoinCost.Controls.failPrefix.join unreachableAllocation).run (State.init C) = .error .revert := by
  refine ⟨?_,by decide,by decide,?_⟩
  · rw [MemoryJoinCost.failed_prefix _ _ _ _ MemoryJoinCost.Controls.fail_source]
    rfl
  · rw [DeferredSource.join_run]
    simp only [TRun.seq,MemoryJoinCost.Controls.fail_source]

theorem unreachable_frame_refused :
    ¬ (Compilation.memory unreachableCode).Input 1 1 initialBase (State.init C) initialMachine := by
  intro input
  have capacity := ((input_iff unreachableCode initialBase (State.init C) initialMachine).mp input).2.2.1
  change 2 ≤ 1 at capacity
  omega

/-- Failure execution and zero reached allocation cost do not imply that
an undersized original compiler Input is admitted. Other fields are inhabited. -/
theorem unreachable_other_fields :
    StateRepr 1 1 1 (Frag.init []) (State.init C) initialBase initialMachine ∧
    AllocationInput 1 1 (unreachableCode.cert.cost (State.init C))
      (State.init C) initialBase initialMachine ∧
    run unreachableCode.code initialMachine = .revert := by
  have physical (frame : Nat) (locals : 1 ≤ frame) (small : frame ≤ 6) :
      StateRepr 1 1 frame (Frag.init []) (State.init C) initialBase initialMachine :=
    memory_frame initial_repr.1 locals
      (fun r => Nat.le_trans small (initial_repr.1.heap.above r))
      (fun r => Nat.le_trans small (initial_repr.1.structs.above r))
  have budget : unreachableCode.cert.cost (State.init C) = 0 := unreachable_frame_retained.1
  refine ⟨physical 1 (by decide) (by decide),Or.inl budget,?_⟩
  have input : (Compilation.memory unreachableCode).Input 1 2 initialBase (State.init C) initialMachine :=
    ⟨physical 2 (by decide) (by decide),by decide,Or.inl budget⟩
  exact (compilation_revert_iff (.memory unreachableCode) input (by rfl)).mpr
    (Or.inl unreachable_frame_retained.2.2.2)

#print axioms admitted_execution
#print axioms scoped_slot_reuse
end Solidity.Backend.Passes.MemoryJoinFrame.Controls
