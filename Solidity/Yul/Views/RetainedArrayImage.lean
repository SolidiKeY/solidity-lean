import Solidity.Yul.Views.RetainedArrayLength

namespace Solidity.Yul.Views

abbrev RetainedElementPack {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a) (fixed : Roadmap.Evm.Fixed) :=
  (i : Nat) × RetainedChildPack child (r.path.go (.index i)) a (r.childCursor fixed i)

def RetainedArrayLayout.prepareElements? {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a)
    (fixed : Roadmap.Evm.Fixed) : List Nat → Option (List (RetainedElementPack r fixed))
  | [] => some []
  | i::rest => do
    let stride := (AggregateStorageDeclaration.ordinary child).stride
    if stride=0 ∨ fixedLayoutHash fixed (.data r.header.slot.val)+(i+1)*stride>2^256 then none else do
      let here ← prepareRetainedChild? child (r.path.go (.index i)) a (r.childCursor fixed i)
      let tail ← r.prepareElements? fixed rest
      pure (⟨i,here⟩::tail)

theorem RetainedArrayLayout.prepareElements_indices {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a)
    (fixed : Roadmap.Evm.Fixed) (indices elements) (computed : r.prepareElements? fixed indices = some elements) :
    elements.map Sigma.fst=indices := by
  induction indices generalizing elements with
  | nil => cases computed; rfl
  | cons i rest ih =>
    unfold prepareElements? at computed
    dsimp only at computed
    split at computed
    · cases computed
    · obtain ⟨here,_,next⟩ := Option.bind_eq_some_iff.mp computed
      obtain ⟨tail,prepared,same⟩ := Option.bind_eq_some_iff.mp next
      cases same
      exact congrArg (i::·) (ih _ prepared)

/-- Actual generated child computation only; no read/inverse/coverage law field. -/
structure RetainedArrayImage {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a)
    (fixed : Roadmap.Evm.Fixed) (history : RetainedIndexHistory r) (length : Roadmap.Word) where
  elements : List (RetainedElementPack r fixed)
  computed : r.prepareElements? fixed (retainedVisitIndices history length.val) = some elements

def prepareRetainedArrayImage? {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a)
    (fixed : Roadmap.Evm.Fixed) (history : RetainedIndexHistory r) (length : Roadmap.Word) : Option (RetainedArrayImage r fixed history length) :=
  match computed : r.prepareElements? fixed (retainedVisitIndices history length.val) with
  | none => none
  | some elements => some ⟨elements,computed⟩

theorem RetainedArrayImage.visited {E τ b child active a r fixed history length}
    (image : @RetainedArrayImage E τ b child active a r fixed history length) :
    image.elements.map Sigma.fst=retainedVisitIndices history length.val := r.prepareElements_indices fixed _ _ image.computed

theorem RetainedArrayImage.visited_once {E τ b child active a r fixed history length}
    (image : @RetainedArrayImage E τ b child active a r fixed history length) : (image.elements.map Sigma.fst).Nodup := by
  rw [image.visited]
  exact retainedVisitIndices_unique _ _

def RetainedArrayImage.registrations {E τ b child active a r fixed history length}
    (image : @RetainedArrayImage E τ b child active a r fixed history length) :=
  r.header :: image.elements.flatMap (fun element => element.2.registrations)

def RetainedArrayImage.snapshot {E τ b child active a r fixed history length}
    (image : @RetainedArrayImage E τ b child active a r fixed history length) (m : SlotView) :=
  r.header :: image.elements.flatMap (fun element => element.2.snapshot fixed m)

def retainedChildrenSource? {E τ b child active Γ} {F : Source.Fr} {r : @RetainedArrayLayout E τ b child active F.this}
    (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ) :
    List (RetainedElementPack r fixed) → Option (List (ScalarPath E.layout (E.lay F.this)))
  | [] => some []
  | element::rest => do
    let here ← element.2.sourceInventory? fixed F s rfl
    let tail ← retainedChildrenSource? fixed s rest
    pure (here++tail)

def RetainedArrayImage.sourceInventory? {E τ b child active Γ} {F : Source.Fr} {r fixed history length}
    (image : @RetainedArrayImage E τ b child active F.this r fixed history length) (s : Source.EMState E Γ) :=
  (retainedChildrenSource? fixed s image.elements).map (r.header::·)

theorem retainedChildrenSource_roots {E τ b child active Γ} {F : Source.Fr} {r : @RetainedArrayLayout E τ b child active F.this}
    (fixed) (s : Source.EMState E Γ) (elements : List (RetainedElementPack r fixed)) (old)
    (computed : retainedChildrenSource? fixed s elements=some old) (c)
    (member : c ∈ elements.flatMap (fun e => e.2.registrations)) : c ∈ old := by
  induction elements generalizing old with
  | nil => cases member
  | cons element rest ih =>
    obtain ⟨here,hereComputed,next⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨tail,tailComputed,same⟩ := Option.bind_eq_some_iff.mp next
    cases same
    rcases List.mem_append.mp member with head | tail
    · exact List.mem_append_left _ (element.2.source_roots fixed F s rfl _ hereComputed c head)
    · exact List.mem_append_right _ (ih _ tailComputed tail)

theorem RetainedArrayImage.source_roots {E τ b child active Γ} {F : Source.Fr} {r fixed history length}
    (image : @RetainedArrayImage E τ b child active F.this r fixed history length) (s : Source.EMState E Γ) (old)
    (computed : image.sourceInventory? s=some old) (c) (member : c ∈ image.registrations) : c ∈ old := by
  obtain ⟨tail,tailComputed,same⟩ := Option.map_eq_some_iff.mp computed
  rw [←same]
  rcases List.mem_cons.mp member with same | child
  · exact List.mem_cons.mpr (Or.inl same)
  · exact List.mem_cons.mpr (Or.inr (retainedChildrenSource_roots fixed s _ _ tailComputed c child))

theorem RetainedArrayImage.snapshot_roots {E τ b child active a r fixed history length}
    (image : @RetainedArrayImage E τ b child active a r fixed history length) (m c) (member : c ∈ image.registrations) : c ∈ image.snapshot m := by
  rcases List.mem_cons.mp member with same | inside
  · exact List.mem_cons.mpr (Or.inl same)
  · obtain ⟨element,em,cm⟩ := List.mem_flatMap.mp inside
    exact List.mem_cons.mpr (Or.inr (List.mem_flatMap.mpr ⟨element,em,List.mem_append_left _ cm⟩))

end Solidity.Yul.Views
