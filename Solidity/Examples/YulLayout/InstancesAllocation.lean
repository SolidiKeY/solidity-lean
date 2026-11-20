import Solidity.Yul.Layout.Instances.Allocation

/-! Checks of the allocation instance facts on small concrete inputs: each
declaration of `Yul/Layout/Instances/Allocation.lean` is used. -/
namespace Solidity.Examples.YulLayout.InstancesAllocation

open Solidity.Goals
open Solidity.Yul.Views
open Solidity.Yul.Layout

/-- Two bytes allocated at a free pointer of 128 take two words: the result is
the existing allocation image, with the free pointer at 192. -/
example (P : Shrink.Params) (m : Shrink.Phys) (here : m.free = 128) :
    view.alloc P .bytes (.blob [1, 2]) m =
      some (128, m.withMemory (byteAllocationView [1, 2] 128 192 (by decide) m.memory)) :=
  Instances.byteAllocation P [1, 2] 128 192 (by decide) m (by decide) here (by decide)

/-- The allocated two bytes hold their length word (`byteAllocation_header`). -/
example (P : Shrink.Params) (m m' : Shrink.Phys) (here : m.free = 128)
    (run : view.alloc P .bytes (.blob [1, 2]) m = some (128, m')) :
    (mload m'.memory 128).val = 2 := by
  have image := Instances.byteAllocation P [1, 2] 128 192 (by decide) m (by decide) here (by decide)
  obtain rfl : m.withMemory (byteAllocationView [1, 2] 128 192 (by decide) m.memory) = m' :=
    congrArg Prod.snd (Option.some.inj (image.symm.trans run))
  exact byteAllocation_header [1, 2] 128 192 (by decide) m.memory

/-- An existing allocation of a bytes object at the old free pointer is a
generic allocation of a `bytes` layout to the same image. -/
example (P : Shrink.Params) {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (free : Roadmap.Word) (fresh : ∀ a, (h.cells a).isSome → p.address a ≠ p.free.val)
    (fits : p.free.val + (MemoryShape.bytes 2).size ≤ free.val) (m : Shrink.Phys)
    (here : m.free = p.free.val) (size : free.val = p.free.val + (MemoryShape.bytes 2).size) :
    ∃ t, Shrink.Layout.Fits .bytes t ∧ view.alloc P .bytes t m =
      some (p.free.val, m.withMemory (byteAllocationView [1, 2] p.free.val free fits m.memory)) :=
  Instances.objectAllocation P h p (heapByteData D false [1, 2]) (heapByteType_memory false)
    (.bytes 2) (heapByteData_shape D false [1, 2]) p.free.val free (Nat.le_refl _) fresh fits m _
    (objectAllocationView_bytes h p false [1, 2] p.free.val free (Nat.le_refl _) fresh fits m.memory)
    here size

/-- An existing allocation of any shaped object is a generic allocation that
returns the old free pointer when the object is placed there. -/
example (P : Shrink.Params) {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    {τ : Source.STy} (data : Source.Data D τ) (memory : τ.loc? = some .memory) (n : Nat)
    (shaped : HasMemoryShape data (.strct n)) (free : Roadmap.Word)
    (fresh : ∀ a, (h.cells a).isSome → p.address a ≠ p.free.val)
    (fits : p.free.val + (MemoryShape.strct n).size ≤ free.val) (m : Shrink.Phys) (image : ByteView)
    (encoded : objectAllocationView h p data memory (.strct n) shaped p.free.val free (Nat.le_refl _)
      fresh fits m.memory = some image)
    (here : m.free = p.free.val) (size : free.val = p.free.val + (MemoryShape.strct n).size) :
    ∃ t a m', view.alloc P (.struct (List.replicate n (.scalar 32))) t m =
      some (a, m') ∧ a = p.free.val :=
  let ⟨t, _, run⟩ := Instances.objectAllocation P h p data memory (.strct n) shaped p.free.val free
    (Nat.le_refl _) fresh fits m image encoded here size
  ⟨t, _, _, run, rfl⟩

end Solidity.Examples.YulLayout.InstancesAllocation
