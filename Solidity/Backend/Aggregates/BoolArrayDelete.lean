import Solidity.Backend.Aggregates.BoolArrays
import Solidity.Semantics.Run
import Solidity.Source.MemoryLocalDelete

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
/-- Relate the actual independently allocated defaults after sufficient Source
fuel. This derives the new contents relation; old caller/alias preservation is
a separate obligation, and Source timeout is not target logical failure. -/
theorem delete_related {E : Source.Env} {Λ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (frame : Source.Fr) (n : Nat) (source : Source.EMState E Λ)
    (si : Source.Idx Λ sourceTy) (target : State C Γ) (ti : Idx Γ (.mem boolR)) :
    Related ((Source.deleteLoc frame (n+2) (.local si)).run source).2.2.heap source.2.heap.next
      ((target.alloc (empty target.H)).1.setLocal ti (some (target.alloc (empty target.H)).2)).heap
      (target.alloc (empty target.H)).2 := by
  simp only [Source.deleteLocal_array_run, Related]
  refine ⟨[], ?_, ?_⟩
  · simp only [Source.Heap.alloc, Source.Heap.get, if_true]
    congr 3
    funext k
    exact Fin.elim0 k
  · change MObj.elems ArrTy.dyn ((target.heap.alloc (empty target.H)).1.get
        (target.heap.alloc (empty target.H)).2) = []
    rw [Heap.get_alloc_self]
    simp only [empty, MObj.wk, MObj.elems_dyn, List.map_nil]

/-- Preserve an already related object through the actual deletion allocations.
Occupied Source cells imply freshness separation; no extra address inequality
or desired preservation premise is required. This observes heap contents,
not caller-local bindings or a payment/world/fetched execution trace. -/
theorem delete_preserves_related {E : Source.Env} {Λ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (frame : Source.Fr) (n : Nat) (source : Source.EMState E Λ)
    (si : Source.Idx Λ sourceTy) (target : State C Γ) (ti : Idx Γ (.mem boolR))
    (address : Nat) (reference : HRef target.H boolR)
    (before : Related source.2.heap address target.heap reference) :
    Related ((Source.deleteLoc frame (n+2) (.local si)).run source).2.2.heap address
      ((target.alloc (empty target.H)).1.setLocal ti (some (target.alloc (empty target.H)).2)).heap
      (reference.wk (List.prefix_append target.H [boolR])) := by
  obtain ⟨values, occupied, contents⟩ := before
  have old : address ≠ source.2.heap.next := by
    intro same
    subst address
    have fresh := source.2.heap.bounded source.2.heap.next (Nat.le_refl _)
    change source.2.heap.get source.2.heap.next = none at fresh
    rw [fresh] at occupied
    cases occupied
  simp only [Source.deleteLocal_array_run, Related]
  refine ⟨values, ?_, ?_⟩
  · exact (Source.Heap.alloc_other source.2.heap _ old).trans occupied
  · change MObj.elems ArrTy.dyn ((target.heap.alloc (empty target.H)).1.get
        (reference.wk (List.prefix_append target.H [boolR]))) = values.map value
    rw [Heap.keeps_alloc target.heap (empty target.H) reference, MObj.elems_wk,
      List.map_id'' (f := MVal.wk (List.prefix_append target.H [boolR]) (.prim .bool))
        (fun _ => rfl)]
    exact contents

end Solidity.Backend.Aggregates.BoolArrayDelete
