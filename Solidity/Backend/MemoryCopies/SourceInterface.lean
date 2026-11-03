import Solidity.Backend.MemoryCopies.Interface
import Solidity.Source.Hoare

/-! Source-only certificates. Hoare/interpreter dependencies are local to this
module; the finite intrinsic Interface does not import the Source evaluator.
Qualified certificate names are preserved. -/
namespace Solidity.Backend.MemoryCopies

/-- Source half of G33, indexed by the actual expected object and fresh root.
It includes the complete run result and all nonheap state, not only a returned
pointer. It accepts any memory STy; no finite-intrinsic-type selector is used.
A compiler/representation certificate is still required separately. -/
structure SourceDefaultCertificate {E : Source.Env} {Γ : Source.RCtx}
    (fuel : Nat) (τ : Source.STy) (memory : τ.loc? = some .memory)
    (before after : Source.EMState E Γ) (root : Nat)
    (data : Source.Data E.layout τ) : Prop where
  execution : (Source.zeroVal (E := E) (Γ := Γ) fuel τ).run before =
    (.ok (.memRef memory root), after)
  frame : after = (before.1, {before.2 with heap := after.2.heap})
  growth : before.2.heap.next ≤ after.2.heap.next
  fresh : before.2.heap.next ≤ root
  object : after.2.heap.get root = some ⟨τ, data⟩
  old : ∀ address, address < before.2.heap.next →
    after.2.heap.get address = before.2.heap.get address

/-- Source half of G35.01 at the actual Source storage path and requested result
type. loadMem returns
parent data and allocates nested children; allocating the parent itself is a
separate allocRef step. This success-only record does not prove failure/timeout or layout agreement;
those remain separate obligations. Consumers must relate the requested type to
the destination memory type/layout before deriving successful allocation. -/
structure SourceStorageLoadCertificate {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (fuel : Nat) (τ : Source.STy) (path : Source.SPath)
    (before after : Source.EMState E Γ) (data : Source.Data E.layout τ) : Prop where
  execution : (Source.loadMem (E := E) (Γ := Γ) frame fuel τ path).run before =
    (.ok data, after)
  nonheap : after = (before.1, {before.2 with heap := after.2.heap})
  growth : before.2.heap.next ≤ after.2.heap.next
  old : ∀ address, address < before.2.heap.next →
    after.2.heap.get address = before.2.heap.get address

/-- Complete Source default outcome, including the exact reached state on a
halt. A timeout after allocating children must not be replaced by the initial
state. This success-or-halt specification is indexed by the expected outcome;
it neither manufactures a successful run nor changes Source admission. -/
structure SourceDefaultOutcomeCertificate {E : Source.Env} {Γ : Source.RCtx}
    (fuel : Nat) (τ : Source.STy) (before after : Source.EMState E Γ)
    (outcome : Source.R (Source.Val E.layout τ)) : Prop where
  execution : (Source.zeroVal (E := E) (Γ := Γ) fuel τ).run before = (outcome, after)
  frame : after = (before.1, {before.2 with heap := after.2.heap})
  growth : before.2.heap.next ≤ after.2.heap.next
  old : ∀ address, address < before.2.heap.next →
    after.2.heap.get address = before.2.heap.get address

/-- Complete Source storage-load outcome. The exact Halt constructor and
reached state remain visible; panic data, empty revert, timeout and stuck
results cannot be collapsed into an undifferentiated failure flag. -/
structure SourceStorageLoadOutcomeCertificate {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (fuel : Nat) (τ : Source.STy) (path : Source.SPath)
    (before after : Source.EMState E Γ)
    (outcome : Source.R (Source.Data E.layout τ)) : Prop where
  execution : (Source.loadMem (E := E) (Γ := Γ) frame fuel τ path).run before =
    (outcome, after)
  nonheap : after = (before.1, {before.2 with heap := after.2.heap})
  growth : before.2.heap.next ≤ after.2.heap.next
  old : ∀ address, address < before.2.heap.next →
    after.2.heap.get address = before.2.heap.get address

/-- Actual Source storage-to-memory root copy, not merely its loadMem data
half. The nested-load intermediate state is explicit, and loadElem must return
the freshly allocated parent. Destination memory layout/path agreement and
compiled execution are separate obligations, not assumed from this record. -/
structure SourceStorageCopyCertificate {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (fuel : Nat) (τ : Source.STy)
    (memory : τ.loc? = some .memory) (path : Source.SPath)
    (before loaded after : Source.EMState E Γ) (root : Nat)
    (data : Source.Data E.layout τ) : Prop where
  load : SourceStorageLoadCertificate frame fuel τ path before loaded data
  allocation : (Source.allocRef (E := E) (Γ := Γ) data).run loaded =
    (.ok (.memRef memory root), after)
  execution : (Source.loadElem (E := E) (Γ := Γ) frame (fuel + 1) τ path).run before =
    (.ok (.memRef memory root), after)
  fresh : before.2.heap.next ≤ root
  object : after.2.heap.get root = some ⟨τ, data⟩
  nonheap : after = (before.1, {before.2 with heap := after.2.heap})
  old : ∀ address, address < before.2.heap.next →
    after.2.heap.get address = before.2.heap.get address


end Solidity.Backend.MemoryCopies
