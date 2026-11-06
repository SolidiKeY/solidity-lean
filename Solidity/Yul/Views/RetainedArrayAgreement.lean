import Solidity.Yul.Views.RetainedArrayImage

namespace Solidity.Yul.Views

theorem retainedChildrenSource_view {E τ b child active Γ} {F : Source.Fr}
    {r : @RetainedArrayLayout E τ b child active F.this} (fixed) (s : Source.EMState E Γ) (m : SlotView)
    (elements : List (RetainedElementPack r fixed))
    (view : finiteView (elements.flatMap (fun e => e.2.registrations)) (s.2.ex.world.accounts F.this).storage m) :
    retainedChildrenSource? fixed s elements = some (elements.flatMap (fun e => e.2.snapshot fixed m)) := by
  induction elements with
  | nil => rfl
  | cons element rest ih =>
    have bank : E.transientRoot (r.path.go (.index element.1))=false := r.bank
    have here : finiteView element.2.registrations (s.2.ex.world.accounts F.this).storage m :=
      fun c member => view c (List.mem_append_left _ member)
    have tail : finiteView (rest.flatMap (fun e => e.2.registrations)) (s.2.ex.world.accounts F.this).storage m :=
      fun c member => view c (List.mem_append_right _ member)
    rw [retainedChildrenSource?,element.2.source_view fixed F s rfl m bank here,ih tail]
    rfl

theorem RetainedArrayImage.source_view {E τ b child active Γ} {F : Source.Fr} {r fixed history length}
    (image : @RetainedArrayImage E τ b child active F.this r fixed history length) (s : Source.EMState E Γ) (m : SlotView)
    (view : finiteView image.registrations (s.2.ex.world.accounts F.this).storage m) :
    image.sourceInventory? s=some (image.snapshot m) := by
  unfold sourceInventory?
  rw [retainedChildrenSource_view fixed s m image.elements (fun c member => view c (List.mem_cons_of_mem _ member))]
  rfl

/-- Complete actual source traversal: outer readLen chooses current indices;
retained event indices add dormant children BEFORE the common typed traversal. -/
def RetainedArrayLayout.sourceInventory? {E τ b child active Γ} {F : Source.Fr}
    (r : @RetainedArrayLayout E τ b child active F.this) (fixed : Roadmap.Evm.Fixed)
    (history : RetainedIndexHistory r) (s : Source.EMState E Γ) := do
  let n ← aggregateSourceLengths F s r.header
  let image ← prepareRetainedArrayImage? r fixed history n
  image.sourceInventory? s

def RetainedArrayLayout.snapshot? {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a)
    (fixed : Roadmap.Evm.Fixed) (history : RetainedIndexHistory r) (m : SlotView) := do
  let image ← prepareRetainedArrayImage? r fixed history (m r.header.slot)
  pure (image.snapshot m)

/-- Derived traversal agreement covers EVERY encountered descendant header,
including dormant paths. Premises are actual preparation and canonical header
views, not an assumed oracle/final-inventory equality. -/
theorem RetainedArrayLayout.source_snapshot {E τ b child active Γ} {F : Source.Fr}
    (r : @RetainedArrayLayout E τ b child active F.this) (fixed history) (s : Source.EMState E Γ) (m : SlotView)
    (image : RetainedArrayImage r fixed history (m r.header.slot))
    (prepared : prepareRetainedArrayImage? r fixed history (m r.header.slot)=some image)
    (view : finiteView image.registrations (s.2.ex.world.accounts F.this).storage m) :
    r.sourceInventory? fixed history s = r.snapshot? fixed history m := by
  unfold sourceInventory? snapshot?
  rw [r.sourceLength_view s m (view _ List.mem_cons_self),prepared]
  dsimp only [Bind.bind,Option.bind,Pure.pure]
  rw [prepared]
  exact image.source_view s m view

theorem RetainedArrayImage.snapshot_header {E τ b child active a r fixed history length}
    (image : @RetainedArrayImage E τ b child active a r fixed history length) (m) : r.header ∈ image.snapshot m := List.mem_cons_self

def retainedSnapshotWriteback {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a)
    (fixed history m) (s : Source.Storage E.layout (E.lay a)) := do
  let cs ← r.snapshot? fixed history m
  if packedSeparationCheck cs then packedStoreWriteback cs m s else none

theorem retainedSnapshot_reencode {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a)
    (fixed history m) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : retainedSnapshotWriteback r fixed history m s=some (out,residual)) :
    ∃ cs, r.snapshot? fixed history m=some cs ∧ finiteEncode cs out residual=some m := by
  unfold retainedSnapshotWriteback at step
  obtain ⟨cs,computed,next⟩ := Option.bind_eq_some_iff.mp step
  split at next
  · exact ⟨cs,computed,packedStoreWriteback_reencode _ _ _ _ _ ((packedSeparationCheck_iff _).mp (by assumption)) next⟩
  · cases next

theorem retainedSnapshot_unchanged {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a)
    (fixed history m) (s : Source.Storage E.layout (E.lay a)) (cs)
    (computed : r.snapshot? fixed history m=some cs) (checked : packedSeparationCheck cs=true) (view : finiteView cs s m) :
    retainedSnapshotWriteback r fixed history m s=some (s,packedMask cs m) := by
  unfold retainedSnapshotWriteback
  rw [computed]
  dsimp only [Bind.bind,Option.bind]
  rw [checked]
  exact packedStoreWriteback_unchanged _ _ _ _ view rfl

end Solidity.Yul.Views
