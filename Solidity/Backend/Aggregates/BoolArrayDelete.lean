import Solidity.Backend.Aggregates.BoolArrays
import Solidity.Semantics.Run

/-! G18.05 logical typed deletion consumer. No Source fuel, physical stack,
gas, fetched instruction, or general lowering correspondence is inferred. -/
namespace Solidity.Backend.Aggregates.BoolArrayDelete
open Solidity BoolArrays

def empty (H : HTy) : MObj H boolR := ⟨[], SVal.zero_lt_bound⟩

/-- Actual default copying allocates exactly one empty bool-array object. -/
theorem default_heap {H : HTy} (heap : Heap H) :
    heap.allocDefault boolR rfl =
      Grown.alloc (R := boolR) ⟨List.prefix_refl H, heap, empty H⟩ := by
  simp only [Heap.allocDefault, SVal.dflt_array, SVal.copyStToM_array,
    SVec.copyStToM_nil, empty]

/-- The actual variable deletion result, exposing allocation and rebinding
rather than postulating a simulation or identifying independent heaps. -/
theorem run_var {C : Contract} {Γ : Ctx} (state : State C Γ)
    (index : Idx Γ (.mem boolR)) :
    TRun.deleteMem (.var index rfl) state =
      .ok ⟨(state.alloc (empty state.H)).1.setLocal index
        (some (state.alloc (empty state.H)).2),
        List.prefix_append state.H [boolR]⟩ := by
  simp only [TRun.deleteMem, State.allocDefaultG, Heap.allocDefault, SVal.dflt_array,
    SVal.copyStToM_array, SVec.copyStToM_nil,
    State.grow, State.alloc, empty]
  rfl
end Solidity.Backend.Aggregates.BoolArrayDelete
