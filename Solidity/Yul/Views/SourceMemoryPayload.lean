import Solidity.Yul.Views.AllocatedObjectMemory

namespace Solidity.Yul.Views

/-- Exact bytes of an ACTUAL owned source object in its computed complete
heap view. Coverage/no-duplication are derived, not caller law fields. Header
and rounded padding are excluded, including the empty-object boundary. -/
theorem encodedSourceBytes {E Γ} (H : Source.HeapTy) (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (residual : ByteView) (ok : Source.MemOK E H s)
    (supported : ∀ a τ d, s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (a : Nat) (bs : Roadmap.Bytes) (found : s.2.heap.get a=some ⟨.bytes .memory,Source.Data.bytes bs⟩) :
    readBytes (encodeMixedHeap p (generatedHeapEntries p) residual) (p.address a+32) bs.length=bs := by
  have prepared := ownerMemOK_prepares_inventory H s p ok supported
  have facts := prepareHeapInventory_ok p _ prepared
  apply List.ext_getElem
  · simp only [readBytes,List.length_map,List.length_range]
  · intro i hi hj
    have byte := encodeMixedHeap_source_byte p _ facts.2.2 facts.2.1 residual a (.bytes .memory) (.bytes bs)
      found (32+i) bs[i] (ObjectByte.bytes bs ⟨i,hj⟩)
    simpa only [readBytes,List.getElem_map,List.getElem_range,Nat.add_assoc] using byte

/-- This is the SAME actual field, not an assumed hash-output agreement or
collision-freedom premise. All bounded Fixed parameters are covered. -/
theorem fixedHash_physical (fixed : Roadmap.Fixed) (memory : ByteView) (a n : Nat) (bs : Roadmap.Bytes)
    (bytes : readBytes memory a n=bs) : keccak256 fixed.evm memory a n=fixed.hash bs := by
  apply Fin.ext
  exact congrArg fixed.evm.keccak bytes

/-- Constructive source-object hash agreement using the actual encoded
view and source lookup. No final byte/hash/view law is supplied as a premise. -/
theorem encodedSourceBytes_hash {E Γ} (H : Source.HeapTy) (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (residual : ByteView) (ok : Source.MemOK E H s)
    (supported : ∀ a τ d, s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (a : Nat) (bs : Roadmap.Bytes) (found : s.2.heap.get a=some ⟨.bytes .memory,Source.Data.bytes bs⟩)
    (fixed : Roadmap.Fixed) :
    keccak256 fixed.evm (encodeMixedHeap p (generatedHeapEntries p) residual) (p.address a+32) bs.length=fixed.hash bs :=
  fixedHash_physical fixed _ _ _ bs (encodedSourceBytes H s p residual ok supported a bs found)

end Solidity.Yul.Views
