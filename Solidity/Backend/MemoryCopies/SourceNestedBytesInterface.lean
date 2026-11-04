import Solidity.Backend.MemoryCopies.SourceBytes

/-! Nested Source byte-array copying over actual typed persistent storage cells.
The existing Source load traversal and heap remain the only operations. -/
namespace Solidity.Backend.MemoryCopies

structure StoredSourceBytes {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (bytes : List UInt8) : Prop where
  range : Source.IntTy.u256.lo ≤ (bytes.length : Int) ∧ (bytes.length : Int) ≤ Source.IntTy.u256.hi
  length : PersistentSourceCell frame path before (Source.Val.int bytes.length range)
  payload : SourceByteRange frame path before 0 bytes

def SourceByteChildren {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (start : Nat) (children : List (List UInt8)) : Prop :=
  ∀ index : Fin children.length,
    StoredSourceBytes frame (path.go (.index (start + index.val))) before children[index]

/-- A sufficient interpreter horizon, not gas or physical allocation size. -/
def byteChildrenHorizon : List (List UInt8) → Nat
  | [] => 1
  | bytes :: rest => bytes.length + 4 + byteChildrenHorizon rest

/-- Exact actual child traversal, with sequential fresh identities and complete
payload preservation after all sibling allocations. No load run is an input. -/
def SourceByteChildrenResult {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (start slack : Nat)
    (children : List (List UInt8)) : Prop :=
  ∃ (values : Fin children.length → Source.Data E.layout (.bytes .memory)) (after : Source.EMState E Γ),
    (Source.loadElems (E := E) (Γ := Γ) frame (byteChildrenHorizon children + slack)
      (.bytes .memory) path start children.length).run before = (.ok values,after) ∧
    after.2.heap.next = before.2.heap.next + children.length ∧ AllocationExtension before after ∧
    (∀ index, values index = .val (.memRef rfl (before.2.heap.next + index.val))) ∧
    (∀ index, after.2.heap.get (before.2.heap.next + index.val) =
      some ⟨.bytes .memory,Source.Data.bytes children[index]⟩)

end Solidity.Backend.MemoryCopies
