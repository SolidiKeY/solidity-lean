import Solidity.Backend.MemoryCopies.SourceFramesCore

/-! Allocation-frame preservation for every existing storage-load traversal.
A mapping refusal and every partially allocated timeout keep their actual Halt
and reached state; no layout-success or traversal-success premise is added. -/
namespace Solidity.Backend.MemoryCopies
open AllocatesOnly

variable {E : Source.Env} {Γ : Source.RCtx}

mutual

theorem loadMem_allocates (frame : Source.Fr) : ∀ (fuel : Nat) (τ : Source.STy) (path : Source.SPath),
    AllocatesOnly (Source.loadMem (E := E) (Γ := Γ) frame fuel τ path)
  | 0, _, _ => halt _
  | fuel + 1, τ, path => by
    simp only [Source.loadMem]
    split
    · exact bind (readLen frame path) (fun length =>
        bind (loadBytes_allocates frame fuel path 0 length) (fun _ => pure' _))
    · exact bind (readLen frame path) (fun length =>
        bind (loadBytes_allocates frame fuel path 0 length) (fun _ => pure' _))
    · exact bind (readLen frame path) (fun length =>
        bind (loadElems_allocates frame fuel _ path 0 length) (fun _ => pure' _))
    · exact bind (loadElems_allocates frame fuel _ path 0 _) (fun _ => pure' _)
    · exact bind (loadFields_allocates frame fuel _ path 0) (fun _ => pure' _)
    · exact halt _
    · exact bind (readAt frame path _) (fun _ => pure' _)

theorem loadElem_allocates (frame : Source.Fr) : ∀ (fuel : Nat) (τ : Source.STy) (path : Source.SPath),
    AllocatesOnly (Source.loadElem (E := E) (Γ := Γ) frame fuel τ path)
  | 0, _, _ => halt _
  | fuel + 1, τ, path => by
    simp only [Source.loadElem]
    split
    · exact bind (loadMem_allocates frame fuel τ path) (fun data => allocRef data)
    · exact readAt frame path τ

theorem loadElems_allocates (frame : Source.Fr) :
    ∀ (fuel : Nat) (τ : Source.STy) (path : Source.SPath) (index length : Nat),
    AllocatesOnly (Source.loadElems (E := E) (Γ := Γ) frame fuel τ path index length)
  | 0, _, _, _, length => by cases length <;> exact halt _
  | _ + 1, _, _, _, 0 => pure' _
  | fuel + 1, τ, path, index, length + 1 =>
    bind (loadElem_allocates frame fuel τ _) (fun _ =>
      bind (loadElems_allocates frame fuel τ path (index + 1) length) (fun _ => pure' _))

theorem loadFields_allocates (frame : Source.Fr) :
    ∀ (fuel : Nat) (types : List Source.STy) (path : Source.SPath) (index : Nat),
    AllocatesOnly (Source.loadFields (E := E) (Γ := Γ) frame fuel types path index)
  | 0, types, _, _ => by cases types <;> exact halt _
  | _ + 1, [], _, _ => pure' _
  | fuel + 1, τ :: types, path, index =>
    bind (loadElem_allocates frame fuel τ _) (fun _ =>
      bind (loadFields_allocates frame fuel types path (index + 1)) (fun _ => pure' _))

theorem loadBytes_allocates (frame : Source.Fr) :
    ∀ (fuel : Nat) (path : Source.SPath) (index length : Nat),
    AllocatesOnly (Source.loadBytes (E := E) (Γ := Γ) frame fuel path index length)
  | 0, _, _, length => by cases length <;> exact halt _
  | _ + 1, _, _, 0 => pure' _
  | fuel + 1, path, index, length + 1 => by
    apply bind (readAt frame (path.go (.index index)) (.fixedBytes 1 (by decide)))
    intro value
    cases value with
    | fixedBytes bytes bound =>
      exact bind (loadBytes_allocates frame fuel path (index + 1) length) (fun _ => pure' _)
    | memRef impossible _ => cases impossible
    | storRef impossible _ => cases impossible
    | cdRef impossible _ _ => cases impossible

end

/-- An inhabited certificate for every storage-load traversal and horizon. -/
def storageTraversalFrames (E : Source.Env) (Γ : Source.RCtx) (frame : Source.Fr) :
    StorageTraversalFrameCertificate E Γ frame :=
  ⟨loadMem_allocates frame, loadElem_allocates frame, loadElems_allocates frame,
    loadFields_allocates frame, loadBytes_allocates frame⟩

def storageLoadOutcomeCertificate {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (fuel : Nat) (τ : Source.STy) (path : Source.SPath)
    (before : Source.EMState E Γ) :
    SourceStorageLoadOutcomeCertificate frame fuel τ path before
      ((Source.loadMem (E := E) (Γ := Γ) frame fuel τ path).run before).2
      ((Source.loadMem (E := E) (Γ := Γ) frame fuel τ path).run before).1 := by
  have preserved : AllocationExtension before
      ((Source.loadMem (E := E) (Γ := Γ) frame fuel τ path).run before).2 :=
    loadMem_allocates frame fuel τ path before
  exact ⟨rfl, preserved.frame, preserved.growth, preserved.old⟩

#print axioms storageTraversalFrames
#print axioms storageLoadOutcomeCertificate
end Solidity.Backend.MemoryCopies
