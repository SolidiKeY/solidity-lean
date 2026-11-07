import Solidity.Yul.Views.FixedInventoryView
import Solidity.Yul.Views.NominalInventoryTransport

/-! Fixed/nominal decoding transported through actual typed heap/image refresh.
The internal member equation is instantiated by the existing concrete realizer;
it is not an inverse, output-view or safety premise at the public entry point. -/
namespace Solidity.Yul.Views.FixedInventory

theorem snapshot_transport {E : Source.Env} {h h' : Source.Heap E.layout}
    (p : Placement h) (q : Placement h') (types : h'.ty=h.ty) (addresses : q.address=p.address)
    (f : Source.FixTy) (k : Option Nat) (m : ByteView) (base : Nat) :
    snapshot q f k m base=(snapshot p f k m base).map (InventoryObject.transport q types addresses) := by
  first
  | solve | simp only [snapshot]
  | solve | decide
  | solve | omega
  | solve | rfl
  | unfold snapshot
    by_cases bound : arrayLengthChoice k m base<2^256
    · simp only [dif_pos bound]
      by_cases absent : FixedMemory.decodeArray E.layout f (arrayLengthChoice k m base) m
          (base+arrayPayloadOffset k)=none
      · rw [Option.pmap_none' absent,Option.pmap_none' absent]
        rfl
      · obtain ⟨values,decoded⟩ := Option.ne_none_iff_exists'.mp absent
        rw [Option.pmap_some' decoded,Option.pmap_some' decoded]
        rfl
    · simp only [dif_neg bound,Option.map_none]

theorem decode_transport {E : Source.Env} {h h' : Source.Heap E.layout}
    (p : Placement h) (q : Placement h') (types : h'.ty=h.ty) (addresses : q.address=p.address)
    (es : List (MixedHeapEntry p)) (qs : List (MixedHeapEntry q))
    (members : ∀ τ w,decodeExtendedMemoryMember q qs τ w=decodeExtendedMemoryMember p es τ w)
    (τ : Source.STy) (m : ByteView) (base : Nat) :
    decode q qs τ m base=(decode p es τ m base).map (InventoryObject.transport q types addresses) := by
  unfold decode
  split <;> first
    | exact snapshot_transport p q types addresses _ _ m base
    | exact NominalInventory.decode_transport p q types addresses es qs members _ m base

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

end Solidity.Yul.Views.FixedInventory
