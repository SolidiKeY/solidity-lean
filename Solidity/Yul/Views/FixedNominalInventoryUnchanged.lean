import Solidity.Yul.Views.FixedNominalInventoryLaws
import Solidity.Yul.Views.FixedInventoryUnchanged

/-! Unchanged nominal-array inventory preparation preserves the complete actual
source state. The profile describes only this partial decoder, not language
admission. Pointer candidates still need actual coverage; encoded-view reads
still use the existing distinct-root condition. -/
namespace Solidity.Yul.Views.FixedNominalInventory

def TypeSupported (E : Source.Env) : Source.STy → Prop
  | .array .memory (.udvt name) _ =>
      NominalMemory.declaredUDVT E name=true ∧
      FixedNominalMemory.ScalarSupported E.layout (E.layout.underlying name)
  | τ => FixedInventory.TypeSupported E τ

theorem element_word {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {name : Source.DeclName} {v : Source.Val D (.udvt name)} {w : Roadmap.Word}
    (encoded : MemoryElement p v w) : v.word=some w := by
  cases encoded with
  | scalar _ _ word => exact word
  | pointer loc _ _ _ _ => cases loc

theorem nominal_object_unchanged {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (root : Nat) (name : Source.DeclName) (k : Option Nat)
    (d : Source.Data E.layout (.array .memory (.udvt name) k))
    (found : h.get root=some ⟨_,d⟩) (image : MemoryImage p d)
    (declared : NominalMemory.declaredUDVT E name=true)
    (supported : FixedNominalMemory.ScalarSupported E.layout (E.layout.underlying name))
    (m : ByteView) (reads : image.Reads m (p.address root)) :
    ∃ o, snapshot p name k m (p.address root)=some o ∧ o.data=d := by
  cases image with
  | words data ws encoded =>
    cases encoded with
    | value v w element =>
      exact False.elim (no_value_memory_shape v _ (p.typed root _ _ found))
    | array n hl bound values words elements =>
      obtain ⟨header,elementReads⟩ := inventory_array_reads k n hl bound words m (p.address root) reads
      have encoded : ∀ i,(values i).word=some (mload m (p.address root+arrayPayloadOffset k+i.val*32)) := by
        intro i
        rw [elementReads i]
        exact element_word (elements i)
      exact Option.map_eq_some_iff.mp
        (snapshot_encode p name k n hl bound values m (p.address root) declared supported header encoded)

theorem object_unchanged {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (e : MixedHeapEntry p)
    (supported : TypeSupported E e.ty) (m : ByteView)
    (reads : e.image.Reads m (p.address e.id)) :
    ∃ o,decode p es e.ty m (p.address e.id)=some o ∧ o.data=e.data := by
  rcases e with ⟨id,τ,data,found,image⟩
  cases τ with
  | array l υ k =>
    cases l with
    | memory =>
      cases υ with
      | udvt name =>
        exact nominal_object_unchanged p id name k data found image supported.1 supported.2 m reads
      | _ => exact FixedInventory.object_unchanged p es coverage ⟨id,_,data,found,image⟩ supported m reads
    | storage | calldata =>
      exact FixedInventory.object_unchanged p es coverage ⟨id,_,data,found,image⟩ supported m reads
  | _ => exact FixedInventory.object_unchanged p es coverage ⟨id,_,data,found,image⟩ supported m reads

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

end Solidity.Yul.Views.FixedNominalInventory
