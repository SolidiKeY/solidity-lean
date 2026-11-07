import Solidity.Yul.Views.MixedNominalInventoryLaws
import Solidity.Yul.Views.FixedNominalInventoryUnchanged

/-! Mixed struct unchanged writeback derives original data from actual field
images. Coverage and retained original extents remain genuine premises; this
partial decoder profile does not restrict language admission. -/
namespace Solidity.Yul.Views.MixedNominalInventory

def TypeSupported (E : Source.Env) : Source.STy → Prop
  | .struct _ name => ∀ τ∈E.layout.fields name,FixedNominalMember.Supported E τ
  | τ => FixedNominalInventory.TypeSupported E τ

theorem struct_object_unchanged {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (root : Nat)
    (l : Source.DataLoc) (name : Source.DeclName) (d : Source.Data E.layout (.struct l name))
    (found : h.get root=some ⟨_,d⟩) (image : MemoryImage p d)
    (supported : ∀ τ∈E.layout.fields name,FixedNominalMember.Supported E τ)
    (m : ByteView) (reads : image.Reads m (p.address root)) :
    ∃ o,FixedNominalMember.snapshotStruct p es l name m (p.address root)=some o ∧ o.data=d := by
  first | solve | simp only
        | cases image with
          | words data ws encoded =>
            cases encoded with
            | value v w element => exact False.elim (no_value_memory_shape v _ (p.typed root _ _ found))
            | strct fs ws fields =>
              have dec := FixedNominalMember.decodeFields_reads p es coverage fields supported m (p.address root) reads
              have mapData : (FixedNominalMember.snapshotStruct p es l name m (p.address root)).map InventoryObject.data=some (.struct fs) := by
                unfold FixedNominalMember.snapshotStruct
                rw [Option.pmap_some' dec,Option.map_some]
              exact Option.map_eq_some_iff.mp mapData

theorem object_unchanged {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (e : MixedHeapEntry p)
    (supported : TypeSupported E e.ty) (m : ByteView) (reads : e.image.Reads m (p.address e.id)) :
    ∃ o,decode p es e.ty m (p.address e.id)=some o ∧ o.data=e.data := by
  first | solve | simp only [decode]
        | rcases e with ⟨id,τ,data,found,image⟩
          cases τ <;> first
            | exact struct_object_unchanged p es coverage id _ _ data found image supported m reads
            | exact FixedNominalInventory.object_unchanged p es coverage ⟨id,_,data,found,image⟩ supported m reads

theorem update_unchanged {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (history : RetainedAllocation allocated p)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (e : MixedHeapEntry p)
    (supported : TypeSupported E e.ty) (m : ByteView) (reads : e.image.Reads m (p.address e.id)) :
    ∃ u,update allocated p es e m=some u ∧ h.get u.entry.id=some ⟨u.entry.ty,u.object.data⟩ := by
  obtain ⟨o,decoded,same⟩ := object_unchanged p es coverage e supported m reads
  have shape : o.shape=p.shape e.id := memoryShape_unique (same ▸ o.shaped) (p.typed e.id _ _ e.found)
  have present : (h.cells e.id).isSome := by change (h.get e.id).isSome=true; rw [e.found]; rfl
  have capacity : o.shape.size≤(allocated.shape e.id).size := by rw [shape]; exact history.fits e.id present
  refine ⟨⟨e,o,capacity⟩,?_,?_⟩
  · unfold update
    rw [decoded]
    change (if fits : o.shape.size≤(allocated.shape e.id).size then some (OwnedInventoryUpdate.mk e o fits) else none)=some (OwnedInventoryUpdate.mk e o capacity)
    rw [dif_pos capacity]
  · change h.get e.id=some ⟨e.ty,o.data⟩
    rw [same]
    exact e.found

theorem updates_unchanged {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (history : RetainedAllocation allocated p)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (entries : List (MixedHeapEntry p))
    (supported : ∀ e ∈ entries,TypeSupported E e.ty) (m : ByteView)
    (reads : ∀ e ∈ entries,e.image.Reads m (p.address e.id)) :
    ∃ us,updates allocated p es entries m=some us ∧
      ∀ u ∈ us,h.get u.entry.id=some ⟨u.entry.ty,u.object.data⟩ := by
  induction entries with
  | nil => exact ⟨[],rfl,fun u member => by cases member⟩
  | cons e entries ih =>
    obtain ⟨u,one,old⟩ := update_unchanged allocated p history es coverage e
      (supported e List.mem_cons_self) m (reads e List.mem_cons_self)
    obtain ⟨rest,tail,same⟩ := ih (fun v member => supported v (List.mem_cons_of_mem _ member))
      (fun v member => reads v (List.mem_cons_of_mem _ member))
    refine ⟨u::rest,?_,?_⟩
    · unfold updates
      rw [one,tail]
      rfl
    · intro v member
      rcases List.mem_cons.mp member with eq | later
      · subst v; exact old
      · exact same v later

theorem writeback_unchanged {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (supported : ∀ e ∈ es,TypeSupported E e.ty)
    (m : ByteView) (reads : ∀ e ∈ es,e.image.Reads m (p.address e.id)) :
    writeback s allocated p history es m=some (.ok (),s) := by
  obtain ⟨us,decoded,same⟩ := updates_unchanged allocated p history es coverage es supported m reads
  unfold writeback
  rw [decoded,Option.map_some,runInventoryUpdates_unchanged us s same]

/-- Physical encoding followed by preparation and real source writes is the
identity on the entire source state, with arbitrary residual bytes. -/
theorem writeback_encoded {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (distinct : (es.map MixedHeapEntry.id).Nodup)
    (supported : ∀ e ∈ es,TypeSupported E e.ty) (residual : ByteView) :
    writeback s allocated p history es (encodeMixedHeap p es residual)=some (.ok (),s) :=
  writeback_unchanged s allocated p history es coverage supported _
    (encodeMixedHeap_reads p es distinct residual)

end Solidity.Yul.Views.MixedNominalInventory
