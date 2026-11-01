import Solidity.Yul.Views.HeapEnumerationLaws

namespace Solidity.Yul.Views

theorem extendedMember_location {D : Source.Layout} {τ : Source.STy} (supported : ExtendedMemberType D τ) :
    τ.loc? = none ∨ τ.loc? = some .memory := by
  rcases supported with old | scalar
  · rcases old with eq | eq | loc
    · subst τ; exact Or.inl rfl
    · subst τ; exact Or.inl rfl
    · exact Or.inr loc
  · cases τ <;> simp only [CanonicalScalarType] at scalar <;> try cases scalar
    all_goals exact Or.inl rfl

theorem supportedElement_exists {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    {τ : Source.STy} (supported : ExtendedMemberType E.layout τ) (v : Source.Val E.layout τ)
    (ok : Source.Val.RefOK E h.ty v) : ∃ w, MemoryElement p v w := by
  cases v with
  | memRef loc a =>
    obtain ⟨σ,owned,shape⟩ := ok
    exact ⟨_,.pointer loc a σ owned shape⟩
  | storRef loc path =>
    rcases extendedMember_location supported with no | memory
    · rw [loc] at no; cases no
    · rw [loc] at memory; cases memory
  | cdRef loc off => exact False.elim ok
  | udvt v =>
    simp only [ExtendedMemberType,OrdinaryMemberType,CanonicalScalarType,Source.STy.loc?,reduceCtorEq,or_self] at supported
  | internalFn name =>
    simp only [ExtendedMemberType,OrdinaryMemberType,CanonicalScalarType,Source.STy.loc?,reduceCtorEq,or_self] at supported
  | externalFn a sel length =>
    simp only [ExtendedMemberType,OrdinaryMemberType,CanonicalScalarType,Source.STy.loc?,reduceCtorEq,or_self] at supported
  | _ => exact ⟨_,.scalar _ _ rfl⟩

theorem prepareFields_supported {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    {τs : List Source.STy} (fs : Source.DataList E.layout τs) (supported : ∀ τ ∈ τs, ExtendedMemberType E.layout τ)
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
          obtain ⟨w,element⟩ := supportedElement_exists p (supported τ List.mem_cons_self) v refOK
          obtain ⟨head,one⟩ := Option.isSome_iff_exists.mp (prepareMember_complete p v w element)
          obtain ⟨tail,rest⟩ := Option.isSome_iff_exists.mp (ih ds (fun σ member => supported σ (List.mem_cons_of_mem _ member)) restInner tailOK)
          change ((prepareMember p (.val v)).bind _).isSome
          rw [one]
          simp only [Option.bind_some,rest,Option.map_some,Option.isSome_some]

/-- Owner invariants supply real bare members and child lookup/shape ownership.
Only the documented canonical member families are a support premise; no image,
read/inverse/coverage/final-state theorem is supplied by the caller. -/
theorem prepareHeapImage_supported {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (a : Nat) (τ : Source.STy) (d : Source.Data E.layout τ) (found : h.get a = some ⟨τ,d⟩)
    (supported : InventoryTypeSupported E τ) (inner : Source.Data.Inner d) (ok : Source.DataOK E h.ty d) :
    (prepareHeapImage p a τ d found).isSome := by
  cases d with
  | val v => exact False.elim (no_value_memory_shape v _ (p.typed a _ _ found))
  | @bytes l bs => cases l <;> cases supported <;> rfl
  | @string l bs => cases l <;> cases supported <;> rfl
  | @array l σ k n hl xs =>
    change ((prepareFin n _ (fun i => prepareMember p (xs i))).map _).isSome
    rw [Option.isSome_map]
    apply prepareFin_isSome
    intro i
    obtain ⟨v,same⟩ := inner i
    have dataOK : Source.DataOK E h.ty (xs i) := by cases ok with | array elements => exact elements i
    rw [same] at dataOK ⊢
    cases dataOK with
    | val refOK =>
      obtain ⟨w,element⟩ := supportedElement_exists p supported v refOK
      exact prepareMember_complete p v w element
  | @struct l name fs =>
    change ((prepareFields p _ fs).map _).isSome
    rw [Option.isSome_map]
    cases ok with
    | struct fieldsOK => exact prepareFields_supported p fs supported inner fieldsOK
  | mapping m => cases supported

theorem ownerMemOK_prepares_inventory {E : Source.Env} {Γ : Source.RCtx} (H : Source.HeapTy)
    (s : Source.EMState E Γ) (p : Placement s.2.heap) (ok : Source.MemOK E H s)
    (supported : ∀ a τ d, s.2.heap.get a = some ⟨τ,d⟩ → InventoryTypeSupported E τ) :
    prepareHeapInventory p = .ok (generatedHeapEntries p) := by
  have represented : HeapImageRepresentable p := by
    intro a τ d found
    obtain ⟨image,_⟩ := Option.isSome_iff_exists.mp (prepareHeapImage_supported p a τ d found (supported a τ d found)
      (ok.2.2 a ⟨τ,d⟩ found) (ok.1.1.heap a ⟨τ,d⟩ found))
    exact ⟨image⟩
  unfold prepareHeapInventory
  rw [representable_no_unsupported p represented]

end Solidity.Yul.Views
