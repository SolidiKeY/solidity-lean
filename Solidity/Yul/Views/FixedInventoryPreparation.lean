import Solidity.Yul.Views.FixedInventoryUnchanged
import Solidity.Yul.Views.NominalInventoryPreparation
import Solidity.Yul.Views.HeapPreparationMemOK

/-! Existing finite heap preparation for the extended fixed decoder profile. Images,
coverage and unique root enumeration are derived from the actual heap and owner
MemOK, never supplied as output laws or a replacement ownership model. -/
namespace Solidity.Yul.Views.FixedInventory

theorem fixed_element_exists {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (f : Source.FixTy) (v : Source.Val E.layout (.fixed f)) : ∃ w,MemoryElement p v w := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases v with
  | fixed n range => exact ⟨Source.intWord n,.scalar _ _ rfl⟩
  | memRef loc _ | storRef loc _ | cdRef loc _ _ => cases loc

theorem fixed_image_prepared {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (a : Nat) (f : Source.FixTy) (k : Option Nat)
    (d : Source.Data E.layout (.array .memory (.fixed f) k))
    (found : h.get a=some ⟨_,d⟩)
    (inner : Source.Data.Inner d) : (prepareHeapImage p a _ d found).isSome := by
  cases d with
  | val v => exact False.elim (no_value_memory_shape v _ (p.typed a _ _ found))
  | array n hl xs =>
    change ((prepareFin n _ (fun i => prepareMember p (xs i))).map _).isSome
    rw [Option.isSome_map]
    apply prepareFin_isSome
    intro i
    obtain ⟨v,same⟩ := inner i
    rw [same]
    obtain ⟨w,encoded⟩ := fixed_element_exists p f v
    exact prepareMember_complete p v w encoded

theorem image_prepared {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (a : Nat) (τ : Source.STy) (d : Source.Data E.layout τ) (found : h.get a=some ⟨τ,d⟩)
    (supported : TypeSupported E τ) (inner : Source.Data.Inner d) (ok : Source.DataOK E h.ty d) :
    (prepareHeapImage p a τ d found).isSome := by
  cases τ with
  | array l υ k =>
    cases l with
    | memory =>
      cases υ with
      | fixed f => exact fixed_image_prepared p a f k d found inner
      | _ => exact NominalInventory.image_prepared p a _ d found supported inner ok
    | storage | calldata => exact NominalInventory.image_prepared p a _ d found supported inner ok
  | _ => exact NominalInventory.image_prepared p a _ d found supported inner ok

theorem owner_prepares {E : Source.Env} {Γ : Source.RCtx} (H : Source.HeapTy)
    (s : Source.EMState E Γ) (p : Placement s.2.heap) (ok : Source.MemOK E H s)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → TypeSupported E τ) :
    prepareHeapInventory p=.ok (generatedHeapEntries p) := by
  have represented : HeapImageRepresentable p := by
    intro a τ d found
    obtain ⟨image,_⟩ := Option.isSome_iff_exists.mp (image_prepared p a τ d found (supported a τ d found)
      (ok.2.2 a ⟨τ,d⟩ found) (ok.1.1.heap a ⟨τ,d⟩ found))
    exact ⟨image⟩
  unfold prepareHeapInventory
  rw [representable_no_unsupported p represented]

/-- No supplied complete inventory: successful owner preparation computes it. -/
theorem generated_roundtrip {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin)
    (p : Placement s.2.heap) (history : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → TypeSupported E τ) (residual : ByteView) :
    prepareHeapInventory p=.ok (generatedHeapEntries p) ∧
    writeback s allocated p history (generatedHeapEntries p)
      (encodeMixedHeap p (generatedHeapEntries p) residual)=some (.ok (),s) := by
  have prepared := owner_prepares H s p ok supported
  obtain ⟨_,coverage,distinct⟩ := prepareHeapInventory_ok p _ prepared
  exact ⟨prepared,writeback_encoded s allocated p history _ coverage distinct
    (fun e _ => supported e.id e.ty e.data e.found) residual⟩

end Solidity.Yul.Views.FixedInventory
