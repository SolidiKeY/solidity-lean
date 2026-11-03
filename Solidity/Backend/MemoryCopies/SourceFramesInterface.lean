import Solidity.Backend.MemoryCopies.SourceInterface

/-! Allocation-frame obligations over the existing Source interpreter. These
certificates preserve every outcome, including a halt after child allocation.
They do not assert termination, successful layout resolution or emitted code. -/
namespace Solidity.Backend.MemoryCopies

/-- Source allocation changes only the heap, extends its frontier, and keeps
all previously allocated objects at their original identities and contents. -/
structure AllocationExtension {E : Source.Env} {Γ : Source.RCtx}
    (before after : Source.EMState E Γ) : Prop where
  frame : after = (before.1, {before.2 with heap := after.2.heap})
  growth : before.2.heap.next ≤ after.2.heap.next
  old : ∀ address, address < before.2.heap.next →
    after.2.heap.get address = before.2.heap.get address

/-- An observation of the actual Source run, with no success premise and no
replacement of a partially allocated reached heap by the input heap. -/
def AllocatesOnly {E : Source.Env} {Γ : Source.RCtx} {α : Type}
    (operation : Source.EM E Γ α) : Prop :=
  ∀ before, AllocationExtension before (operation.run before).2

/-- All four mutually recursive default traversals at every horizon/type.
The existing Source semantics decides success, timeout and other halts. -/
structure DefaultTraversalFrameCertificate (E : Source.Env) (Γ : Source.RCtx) : Prop where
  data : ∀ (fuel : Nat) (τ : Source.STy), AllocatesOnly (Source.zeroData (E := E) (Γ := Γ) fuel τ)
  value : ∀ (fuel : Nat) (τ : Source.STy), AllocatesOnly (Source.zeroVal (E := E) (Γ := Γ) fuel τ)
  elements : ∀ (fuel : Nat) (τ : Source.STy) (length : Nat),
    AllocatesOnly (Source.zeroElems (E := E) (Γ := Γ) fuel τ length)
  fields : ∀ (fuel : Nat) (types : List Source.STy), AllocatesOnly (Source.zeroFields (E := E) (Γ := Γ) fuel types)

/-- Storage-load traversal frames at every horizon/type/path, including its
nested children and bytes. This is not a storage-layout correspondence premise. -/
structure StorageTraversalFrameCertificate (E : Source.Env) (Γ : Source.RCtx)
    (frame : Source.Fr) : Prop where
  data : ∀ (fuel : Nat) (τ : Source.STy) (path : Source.SPath), AllocatesOnly (Source.loadMem (E := E) (Γ := Γ) frame fuel τ path)
  value : ∀ (fuel : Nat) (τ : Source.STy) (path : Source.SPath), AllocatesOnly (Source.loadElem (E := E) (Γ := Γ) frame fuel τ path)
  elements : ∀ (fuel : Nat) (τ : Source.STy) (path : Source.SPath) (index length : Nat),
    AllocatesOnly (Source.loadElems (E := E) (Γ := Γ) frame fuel τ path index length)
  fields : ∀ (fuel : Nat) (types : List Source.STy) (path : Source.SPath) (index : Nat),
    AllocatesOnly (Source.loadFields (E := E) (Γ := Γ) frame fuel types path index)
  bytes : ∀ (fuel : Nat) (path : Source.SPath) (index length : Nat),
    AllocatesOnly (Source.loadBytes (E := E) (Γ := Γ) frame fuel path index length)

end Solidity.Backend.MemoryCopies
