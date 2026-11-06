import Solidity.Backend.MemoryCopies.SourceStorageFrames

/-! Fresh parent allocation after an actual successful Source storage load.
Nested child allocation is already included in the reached load state. No
physical storage-layout or compiled-code certificate follows from this law. -/
namespace Solidity.Backend.MemoryCopies

/-- The existing Source allocator's reached state, without changing its model. -/
def allocatedState {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (data : Source.Data E.layout τ) (before : Source.EMState E Γ) : Source.EMState E Γ :=
  (before.1, {before.2 with heap := (before.2.heap.alloc ⟨τ, data⟩).1})

theorem allocRef_run {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (data : Source.Data E.layout τ) (memory : τ.loc? = some .memory)
    (before : Source.EMState E Γ) :
    (Source.allocRef (E := E) (Γ := Γ) data).run before =
      (.ok (.memRef memory before.2.heap.next), allocatedState data before) := by
  unfold Source.allocRef
  rw [Source.Hoare.run_bind]
  simp only [dif_pos memory]
  rfl

/-- A successful load's frame is derived, rather than supplied independently. -/
def storageLoadCertificate {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (fuel : Nat) (τ : Source.STy) (path : Source.SPath)
    (before loaded : Source.EMState E Γ) (data : Source.Data E.layout τ)
    (execution : (Source.loadMem (E := E) (Γ := Γ) frame fuel τ path).run before =
      (.ok data, loaded)) : SourceStorageLoadCertificate frame fuel τ path before loaded data := by
  have preserved : AllocationExtension before loaded := by
    have result : AllocationExtension before
        ((Source.loadMem (E := E) (Γ := Γ) frame fuel τ path).run before).2 :=
      loadMem_allocates frame fuel τ path before
    rw [execution] at result
    exact result
  exact ⟨execution, preserved.frame, preserved.growth, preserved.old⟩

/-- Fresh identity and old-object preservation for the complete Source root copy.
Success is an explicit equation for the real load; all Halt outcomes are handled
separately by storageLoadOutcomeCertificate. No shape or capacity selector is added. -/
def storageCopyCertificate {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (fuel : Nat) (τ : Source.STy) (memory : τ.loc? = some .memory)
    (path : Source.SPath) (before loaded : Source.EMState E Γ)
    (data : Source.Data E.layout τ)
    (execution : (Source.loadMem (E := E) (Γ := Γ) frame fuel τ path).run before =
      (.ok data, loaded)) :
    SourceStorageCopyCertificate frame fuel τ memory path before loaded (allocatedState data loaded)
      loaded.2.heap.next data := by
  let load : SourceStorageLoadCertificate frame fuel τ path before loaded data :=
    storageLoadCertificate frame fuel τ path before loaded data execution
  have parent : AllocationExtension loaded (allocatedState data loaded) :=
    AllocatesOnly.alloc data loaded
  have whole : AllocationExtension before (allocatedState data loaded) :=
    (show AllocationExtension before loaded from ⟨load.nonheap, load.growth, load.old⟩).trans parent
  refine ⟨load, allocRef_run data memory loaded, ?_, load.growth, ?_, whole.frame, whole.old⟩
  · simp only [Source.loadElem, Source.STy.byRef, memory, Option.isSome_some, if_true]
    rw [Source.Hoare.run_bind, execution]
    exact allocRef_run data memory loaded
  · exact Source.Heap.alloc_get loaded.2.heap ⟨τ, data⟩

#print axioms allocRef_run
#print axioms storageLoadCertificate
#print axioms storageCopyCertificate
end Solidity.Backend.MemoryCopies
