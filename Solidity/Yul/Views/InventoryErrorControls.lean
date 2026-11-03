import Solidity.Yul.Views.InventoryControls

namespace Solidity.Yul.Views.Controls

def inventoryManual0 : OwnedInventoryUpdate mixedPlacement mixedPlacement :=
  ⟨mixedEntry0,⟨.bytes inventoryNewBytes,.bytes 4,.bytes _,.bytes _ (by decide)⟩,by decide⟩
def inventoryManual1 : OwnedInventoryUpdate mixedPlacement mixedPlacement :=
  ⟨mixedEntry1,⟨.string inventoryNewString,.bytes 3,.string _,.string _ (by decide)⟩,by decide⟩
def inventoryManual2 : OwnedInventoryUpdate mixedPlacement mixedPlacement :=
  ⟨mixedEntry2,⟨mixedStatic,.array false 2,.array 2 _ _,mixedStaticImage⟩,by decide⟩

def inventoryFaultHeap : Source.Heap mixedLayout :=
  (((Source.Heap.empty.alloc ⟨.bytes .memory,.bytes mixedChild⟩).1.alloc ⟨.string .memory,.string mixedString⟩).1.alloc ⟨.bytes .memory,.bytes []⟩).1

def inventoryFaultState : Source.EMState mixedEnv [] := ⟨.nil,{mixedState.2 with heap := inventoryFaultHeap}⟩
def inventoryFaultPrefixHeap := (inventoryFaultHeap.write 0 (.bytes inventoryNewBytes) (by rfl)).write 1 (.string inventoryNewString) (by rfl)
def inventoryFaultPrefix := withSourceHeap inventoryFaultState inventoryFaultPrefixHeap

theorem inventory_actual_late_source_error : (runInventoryUpdates [inventoryManual0,inventoryManual1,inventoryManual2]).run inventoryFaultState =
    (.error (.stuck "memory write type"),inventoryFaultPrefix) := by
  simp only [runInventoryUpdates,Source.Hoare.run_bind]
  dsimp only [inventoryManual0,inventoryManual1,inventoryManual2,mixedEntry0,mixedEntry1,mixedEntry2]
  rw [heapPutConcrete_run inventoryFaultState 0 (Source.Data.bytes (l := .memory) inventoryNewBytes) (by rfl)]
  simp only []
  rw [heapPutConcrete_run _ 1 (Source.Data.string (l := .memory) inventoryNewString) (by rfl)]
  simp only []
  rw [heapPutConcrete_error _ 2 mixedStatic (by decide)]
  rfl

theorem inventory_fault_MemOK : Source.MemOK mixedEnv inventoryFaultHeap.ty inventoryFaultState := by
  have every (a : Nat) (x : Σ τ,Source.Data mixedLayout τ) (found : inventoryFaultHeap.get a = some x) :
      Source.DataOK mixedEnv inventoryFaultHeap.ty x.2 ∧ Source.Data.Top (E := mixedEnv) x.2 ∧ Source.Data.Inner (E := mixedEnv) x.2 := by
    cases a with
    | zero => cases found; exact ⟨.bytes _,trivial,trivial⟩
    | succ a => cases a with
      | zero => cases found; exact ⟨.string _,trivial,trivial⟩
      | succ a => cases a with
        | zero => cases found; exact ⟨.bytes _,trivial,trivial⟩
        | succ a =>
          have absent := inventoryFaultHeap.bounded (a+3) (by change 3 ≤ a+3; omega)
          change inventoryFaultHeap.cells (a+3) = some x at found
          rw [absent] at found
          cases found
  exact ⟨⟨⟨fun a x found => (every a x found).1,Source.HeapTy.Le.refl _⟩,trivial⟩,
    (fun a x found => (every a x found).2.1),fun a x found => (every a x found).2.2⟩

theorem inventory_late_error_MemOK (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H inventoryFaultState) : Source.MemOK mixedEnv H inventoryFaultPrefix := by
  have values (u : OwnedInventoryUpdate mixedPlacement mixedPlacement) (member : u ∈ [inventoryManual0,inventoryManual1,inventoryManual2]) : Source.DataOK mixedEnv inventoryFaultHeap.ty u.object.data := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with eq | eq | eq
    · subst u; exact .bytes _
    · subst u; exact .string _
    · subst u; exact .array (fun i => .val (by unfold mixedStaticVals; split <;> trivial))
  have keep := runInventoryUpdates_MemOK [inventoryManual0,inventoryManual1,inventoryManual2] H inventoryFaultState values ok
  rw [inventory_actual_late_source_error] at keep
  exact keep

theorem inventory_late_error_inhabited : Source.MemOK mixedEnv inventoryFaultHeap.ty inventoryFaultPrefix := inventory_late_error_MemOK _ inventory_fault_MemOK

theorem inventory_prefix_cells_world : inventoryFaultPrefix.2.heap.get 0 = some ⟨.bytes .memory,.bytes inventoryNewBytes⟩ ∧
    inventoryFaultPrefix.2.heap.get 1 = some ⟨.string .memory,.string inventoryNewString⟩ ∧ inventoryFaultPrefix.2.heap.get 2 = inventoryFaultHeap.get 2 ∧
    inventoryFaultPrefix.1 = inventoryFaultState.1 ∧ inventoryFaultPrefix.2.ex = inventoryFaultState.2.ex := ⟨rfl,rfl,rfl,rfl,rfl⟩

end Solidity.Yul.Views.Controls
