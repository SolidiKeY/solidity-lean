import Solidity.Yul.Views.RetainedEntryRun

namespace Solidity.Yul.Views

/-- A checked image from LIVE, historically formed, and observed ENTRY/RETURN
paths. The only certificate is the existing concrete child packing computation;
no final coverage, inverse, read or safety law is accepted as a field. -/
structure CapturedArrayImage {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a)
    (fixed : Roadmap.Evm.Fixed) (history : RetainedIndexHistory r)
    (scopes : List (EntryReferenceScope E)) (length : Roadmap.Word) where
  elements : List (RetainedElementPack r fixed)
  computed : r.prepareElements? fixed (capturedVisitIndices r history scopes length.val)=some elements

def prepareCapturedArrayImage? {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a)
    (fixed : Roadmap.Evm.Fixed) (history : RetainedIndexHistory r)
    (scopes : List (EntryReferenceScope E)) (length : Roadmap.Word) : Option (CapturedArrayImage r fixed history scopes length) :=
  match computed : r.prepareElements? fixed (capturedVisitIndices r history scopes length.val) with
  | none => none
  | some elements => some ⟨elements,computed⟩

theorem CapturedArrayImage.prepared {E τ b child active a r fixed history scopes length}
    (image : @CapturedArrayImage E τ b child active a r fixed history scopes length) :
    prepareCapturedArrayImage? r fixed history scopes length=some image := by
  unfold prepareCapturedArrayImage?
  split
  · rename_i missing
    rw [image.computed] at missing
    cases missing
  · rename_i elements found
    have same : elements=image.elements := Option.some.inj (found.symm.trans image.computed)
    subst elements
    rfl

theorem CapturedArrayImage.visited {E τ b child active a r fixed history scopes length}
    (image : @CapturedArrayImage E τ b child active a r fixed history scopes length) :
    image.elements.map Sigma.fst=capturedVisitIndices r history scopes length.val :=
  r.prepareElements_indices fixed _ _ image.computed

theorem CapturedArrayImage.unique {E τ b child active a r fixed history scopes length}
    (image : @CapturedArrayImage E τ b child active a r fixed history scopes length) :
    (image.elements.map Sigma.fst).Nodup := by
  rw [image.visited]
  exact capturedVisitIndices_unique _ _ _ _

def CapturedArrayImage.registrations {E τ b child active a r fixed history scopes length}
    (image : @CapturedArrayImage E τ b child active a r fixed history scopes length) :=
  r.header::image.elements.flatMap (fun e => e.2.registrations)

def CapturedArrayImage.snapshot {E τ b child active a r fixed history scopes length}
    (image : @CapturedArrayImage E τ b child active a r fixed history scopes length) (m : SlotView) :=
  r.header::image.elements.flatMap (fun e => e.2.snapshot fixed m)

def CapturedArrayImage.sourceInventory? {E τ b child active Γ} {F : Source.Fr} {r fixed history scopes length}
    (image : @CapturedArrayImage E τ b child active F.this r fixed history scopes length) (s : Source.EMState E Γ) :=
  (retainedChildrenSource? fixed s image.elements).map (r.header::·)

theorem CapturedArrayImage.source_roots {E τ b child active Γ} {F : Source.Fr} {r fixed history scopes length}
    (image : @CapturedArrayImage E τ b child active F.this r fixed history scopes length)
    (s : Source.EMState E Γ) (old) (computed : image.sourceInventory? s=some old)
    (c) (member : c ∈ image.registrations) : c ∈ old := by
  obtain ⟨tail,tailComputed,same⟩ := Option.map_eq_some_iff.mp computed
  rw [←same]
  rcases List.mem_cons.mp member with same | child
  · exact List.mem_cons.mpr (Or.inl same)
  · exact List.mem_cons.mpr (Or.inr (retainedChildrenSource_roots fixed s _ _ tailComputed c child))

theorem CapturedArrayImage.source_view {E τ b child active Γ} {F : Source.Fr} {r fixed history scopes length}
    (image : @CapturedArrayImage E τ b child active F.this r fixed history scopes length)
    (s : Source.EMState E Γ) (m : SlotView)
    (view : finiteView image.registrations (s.2.ex.world.accounts F.this).storage m) :
    image.sourceInventory? s=some (image.snapshot m) := by
  unfold sourceInventory?
  rw [retainedChildrenSource_view fixed s m image.elements (fun c member => view c (List.mem_cons_of_mem _ member))]
  rfl

def capturedSnapshotWriteback {E τ b child active a} {r fixed history scopes length}
    (image : @CapturedArrayImage E τ b child active a r fixed history scopes length)
    (m : SlotView) (store : Source.Storage E.layout (E.lay a)) :=
  if packedSeparationCheck (image.snapshot m) then packedStoreWriteback (image.snapshot m) m store else none

theorem capturedSnapshot_reencode {E τ b child active a} {r fixed history scopes length}
    (image : @CapturedArrayImage E τ b child active a r fixed history scopes length)
    (m : SlotView) (store out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : capturedSnapshotWriteback image m store=some (out,residual)) :
    finiteEncode (image.snapshot m) out residual=some m := by
  unfold capturedSnapshotWriteback at step
  split at step
  · exact packedStoreWriteback_reencode _ _ _ _ _ ((packedSeparationCheck_iff _).mp (by assumption)) step
  · cases step

theorem capturedSnapshot_unchanged {E τ b child active a} {r fixed history scopes length}
    (image : @CapturedArrayImage E τ b child active a r fixed history scopes length)
    (m : SlotView) (store : Source.Storage E.layout (E.lay a))
    (checked : packedSeparationCheck (image.snapshot m)=true) (view : finiteView (image.snapshot m) store m) :
    capturedSnapshotWriteback image m store=some (store,packedMask (image.snapshot m) m) := by
  unfold capturedSnapshotWriteback
  rw [checked]
  exact packedStoreWriteback_unchanged _ _ _ _ view rfl

end Solidity.Yul.Views
