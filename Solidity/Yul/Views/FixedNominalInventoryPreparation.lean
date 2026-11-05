import Solidity.Yul.Views.FixedNominalInventoryUnchanged
import Solidity.Yul.Views.FixedInventoryPreparation
import Solidity.Yul.Views.HeapPreparationMemOK

/-! Existing finite heap preparation for the nominal decoder profile. Images,
coverage and unique root enumeration are derived from the actual heap and owner
MemOK, never supplied as output laws or a replacement ownership model. -/
namespace Solidity.Yul.Views.FixedNominalInventory

theorem scalar_no_location {D : Source.Layout} {τ : Source.STy}
    (supported : FixedNominalMemory.ScalarSupported D τ) : τ.loc?=none := by
  first
  | solve | simp only [FixedNominalMemory.ScalarSupported,CanonicalScalarType] at supported ⊢
  | solve | rfl
  | cases τ <;> first | rfl | cases supported

theorem supported_scalar_element {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (τ : Source.STy) (supported : FixedNominalMemory.ScalarSupported E.layout τ)
    (v : Source.Val E.layout τ) : ∃ w,MemoryElement p v w := by
  first | solve | simp only
        | cases τ <;> first
          | exact FixedInventory.fixed_element_exists p _ v
          | apply supportedElement_exists p
            · exact Or.inr supported
            · exact Source.Val.refOK_of_loc (scalar_no_location supported) v

theorem nominal_element_exists {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (name : Source.DeclName) (supported : FixedNominalMemory.ScalarSupported E.layout (E.layout.underlying name))
    (v : Source.Val E.layout (.udvt name)) : ∃ w,MemoryElement p v w := by
  cases v with
  | udvt inner =>
    have noLoc := scalar_no_location supported
    obtain ⟨w,element⟩ := supported_scalar_element p _ supported inner
    have encoded : inner.word=some w := by
      cases element with
      | scalar _ _ word => exact word
      | pointer loc _ _ _ _ => rw [noLoc] at loc; cases loc
    exact ⟨w,.scalar _ w encoded⟩
  | memRef loc _ | storRef loc _ | cdRef loc _ _ => cases loc

theorem nominal_image_prepared {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (a : Nat) (name : Source.DeclName) (k : Option Nat)
    (d : Source.Data E.layout (.array .memory (.udvt name) k))
    (found : h.get a=some ⟨_,d⟩)
    (supported : FixedNominalMemory.ScalarSupported E.layout (E.layout.underlying name))
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
    obtain ⟨w,encoded⟩ := nominal_element_exists p name supported v
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
      | udvt name => exact nominal_image_prepared p a name k d found supported.2 inner
      | _ => exact FixedInventory.image_prepared p a _ d found supported inner ok
    | storage | calldata => exact FixedInventory.image_prepared p a _ d found supported inner ok
  | _ => exact FixedInventory.image_prepared p a _ d found supported inner ok

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

end Solidity.Yul.Views.FixedNominalInventory
