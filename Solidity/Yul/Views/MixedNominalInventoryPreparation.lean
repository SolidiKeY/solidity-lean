import Solidity.Yul.Views.MixedNominalInventoryUnchanged
import Solidity.Yul.Views.FixedNominalInventoryPreparation

/-! Actual owner invariants compute mixed struct images through the existing
heap preparer. Field-word existence reuses fixed, nominal and pointer facts;
coverage/unique enumeration and Source roundtrip are derived, not supplied. -/
namespace Solidity.Yul.Views.MixedNominalInventory

theorem member_exists {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (τ : Source.STy) (supported : FixedNominalMember.Supported E τ) (v : Source.Val E.layout τ)
    (ok : Source.Val.RefOK E h.ty v) : ∃ w,MemoryElement p v w := by
  first | solve | simp only
        | cases τ with
          | fixed f => exact FixedInventory.fixed_element_exists p f v
          | udvt name => exact FixedNominalInventory.nominal_element_exists p name supported.2 v
          | _ => exact supportedElement_exists p supported v ok

theorem prepareFields_supported {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    {τs : List Source.STy} (fs : Source.DataList E.layout τs) (supported : ∀ τ ∈ τs, FixedNominalMember.Supported E τ)
    (inner : fs.AllVal) (ok : Source.DataListOK E h.ty fs) : (prepareFields p τs fs).isSome := by
  induction τs with
  | nil => cases fs; rfl
  | cons τ τs ih =>
    cases fs with
    | cons d ds =>
      obtain ⟨⟨v,same⟩,restInner⟩ := inner
      subst d
      cases ok with
      | cons headOK tailOK =>
        cases headOK with
        | val refOK =>
          obtain ⟨w,element⟩ := member_exists p τ (supported τ List.mem_cons_self) v refOK
          obtain ⟨head,one⟩ := Option.isSome_iff_exists.mp (prepareMember_complete p v w element)
          obtain ⟨tail,rest⟩ := Option.isSome_iff_exists.mp (ih ds (fun σ member => supported σ (List.mem_cons_of_mem _ member)) restInner tailOK)
          change ((prepareMember p (.val v)).bind _).isSome
          rw [one]
          simp only [Option.bind_some,rest,Option.map_some,Option.isSome_some]

theorem image_prepared {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (a : Nat) (τ : Source.STy) (d : Source.Data E.layout τ) (found : h.get a=some ⟨τ,d⟩)
    (supported : TypeSupported E τ) (inner : Source.Data.Inner d) (ok : Source.DataOK E h.ty d) :
    (prepareHeapImage p a τ d found).isSome := by
  first | solve | simp only
        | cases τ with
          | struct l name =>
            cases d with
            | val v => exact False.elim (no_value_memory_shape v _ (p.typed a _ _ found))
            | struct fs =>
              change ((prepareFields p _ fs).map _).isSome
              rw [Option.isSome_map]
              cases ok with
              | struct fieldsOK => exact prepareFields_supported p fs supported inner fieldsOK
          | _ => exact FixedNominalInventory.image_prepared p a _ d found supported inner ok

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

end Solidity.Yul.Views.MixedNominalInventory
