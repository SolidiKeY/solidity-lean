import Solidity.Yul.Views.MixedNominalInventoryView
import Solidity.Yul.Views.FixedNominalInventoryTransport

/-! Actual mixed member/field decoder transport follows the existing realizer's
pointer agreement. Fixed/nominal scalar branches are independent of placement;
public realization laws require no desired output decoder agreement. -/
namespace Solidity.Yul.Views.MixedNominalInventory

theorem member_transport {E : Source.Env} {h h' : Source.Heap E.layout}
    (p : Placement h) (q : Placement h') (es : List (MixedHeapEntry p)) (qs : List (MixedHeapEntry q))
    (members : ∀ τ w,decodeExtendedMemoryMember q qs τ w=decodeExtendedMemoryMember p es τ w)
    (τ : Source.STy) (w : Roadmap.Word) :
    FixedNominalMember.decode q qs τ w=FixedNominalMember.decode p es τ w := by
  first | solve | simp only [FixedNominalMember.decode]
        | cases τ <;> simp only [FixedNominalMember.decode] <;> first | rfl | exact members _ w

theorem fields_transport {E : Source.Env} {h h' : Source.Heap E.layout}
    (p : Placement h) (q : Placement h') (es : List (MixedHeapEntry p)) (qs : List (MixedHeapEntry q))
    (members : ∀ τ w,decodeExtendedMemoryMember q qs τ w=decodeExtendedMemoryMember p es τ w)
    (τs : List Source.STy) (m : ByteView) (base : Nat) :
    FixedNominalMember.decodeFields q qs τs m base=FixedNominalMember.decodeFields p es τs m base := by
  first | solve | simp only [FixedNominalMember.decodeFields]
        | unfold FixedNominalMember.decodeFields
          have eq : FixedNominalMember.decode q qs=FixedNominalMember.decode p es :=
            funext (fun τ=>funext (member_transport p q es qs members τ))
          rw [eq]

theorem snapshot_transport {E : Source.Env} {h h' : Source.Heap E.layout}
    (p : Placement h) (q : Placement h') (types : h'.ty=h.ty) (addresses : q.address=p.address)
    (es : List (MixedHeapEntry p)) (qs : List (MixedHeapEntry q))
    (members : ∀ τ w,decodeExtendedMemoryMember q qs τ w=decodeExtendedMemoryMember p es τ w)
    (l : Source.DataLoc) (name : Source.DeclName) (m : ByteView) (base : Nat) :
    FixedNominalMember.snapshotStruct q qs l name m base=
      (FixedNominalMember.snapshotStruct p es l name m base).map (InventoryObject.transport q types addresses) := by
  first | solve | simp only [FixedNominalMember.snapshotStruct]
        | unfold FixedNominalMember.snapshotStruct
          have stable := fields_transport p q es qs members (E.layout.fields name) m base
          by_cases absent : FixedNominalMember.decodeFields p es (E.layout.fields name) m base=none
          · rw [Option.pmap_none' (stable.trans absent),Option.pmap_none' absent]; rfl
          · obtain ⟨fs,decoded⟩ := Option.ne_none_iff_exists'.mp absent
            rw [Option.pmap_some' (stable.trans decoded),Option.pmap_some' decoded,Option.map_some]
            rfl

theorem decode_transport {E : Source.Env} {h h' : Source.Heap E.layout}
    (p : Placement h) (q : Placement h') (types : h'.ty=h.ty) (addresses : q.address=p.address)
    (es : List (MixedHeapEntry p)) (qs : List (MixedHeapEntry q))
    (members : ∀ τ w,decodeExtendedMemoryMember q qs τ w=decodeExtendedMemoryMember p es τ w)
    (τ : Source.STy) (m : ByteView) (base : Nat) :
    decode q qs τ m base=(decode p es τ m base).map (InventoryObject.transport q types addresses) := by
  unfold decode
  split <;> first
    | exact snapshot_transport p q types addresses es qs members _ _ m base
    | exact FixedNominalInventory.decode_transport p q types addresses es qs members _ m base

/-- Complete refresh agreement after the actual finite write sequence. No
caller-supplied member-decoder agreement is needed here. -/
theorem realized_decode {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (history : RetainedAllocation allocated p)
    (us : List (OwnedInventoryUpdate allocated p)) (es : List (MixedHeapEntry p))
    (τ : Source.STy) (m : ByteView) (base : Nat) :
    let r := realizeInventory allocated p history us h p history rfl es
    decode r.placement r.entries τ m base=(decode p es τ m base).map
      (InventoryObject.transport r.placement
        (realizeInventory_types allocated p history us h p history rfl es)
        (realizeInventory_choices allocated p history us h p history rfl es).1) := by
  exact decode_transport p _ _ _ es _
    (realizeInventory_decoder allocated p history us h p history rfl es) τ m base

/-- Any actual finite prefix has both its exact complete source result and
fresh decoder transport. `take` selects a prefix; it imposes no execution cap. -/
theorem prefix_transport {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (us : List (OwnedInventoryUpdate allocated p))
    (es : List (MixedHeapEntry p)) (count : Nat) :
    let selected := us.take count
    let r := realizeInventory allocated p history selected s.2.heap p history rfl es
    (runInventoryUpdates selected).run s=(.ok (),withSourceHeap s r.heap) ∧
    (∀ τ m base,decode r.placement r.entries τ m base=(decode p es τ m base).map
      (InventoryObject.transport r.placement
        (realizeInventory_types allocated p history selected s.2.heap p history rfl es)
        (realizeInventory_choices allocated p history selected s.2.heap p history rfl es).1)) := by
  exact ⟨realizeInventory_run allocated p history (us.take count) s p history rfl es,
    fun τ m base => realized_decode allocated p history (us.take count) es τ m base⟩

end Solidity.Yul.Views.MixedNominalInventory
