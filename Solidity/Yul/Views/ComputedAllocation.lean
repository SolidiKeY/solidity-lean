import Solidity.Yul.Views.ComputedPlacement
import Solidity.Yul.Views.ObjectMemoryAllocation

/-! Transport the checked mathematical placement witness through the actual
Source heap allocation. This derives geometric base/freshness facts; it does
not identify the selected witness with the target allocator or prove universal
allocation refinement. Existing allocation and placement APIs stay unchanged. -/
namespace Solidity.Yul.Views.ComputedPlacement

theorem alloc_shape_old {D : Source.Layout} (h : Source.Heap D) (x : Σ τ, Source.Data D τ)
    (a : Nat) (different : a≠h.next) : shapeAt (h.alloc x).1 a=shapeAt h a := by
  simp only [shapeAt,Source.Heap.alloc_other h x different]

theorem alloc_position_prefix {D : Source.Layout} (h : Source.Heap D) (x : Σ τ, Source.Data D τ)
    (a : Nat) (bound : a≤h.next) : position (h.alloc x).1 a=position h a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    have different : a≠h.next := by omega
    have old := Source.Heap.alloc_other h x different
    change position (h.alloc x).1 a+_=position h a+_
    rw [ih (by omega),old,alloc_shape_old h x a different]

theorem alloc_shape_new {D : Source.Layout} (h : Source.Heap D) (x : Σ τ, Source.Data D τ)
    (shape : MemoryShape) (found : objectShape x.2=some shape) : shapeAt (h.alloc x).1 h.next=shape := by
  have fresh : (h.alloc x).1.get h.next=some x := Source.Heap.alloc_get h x
  simp only [shapeAt,fresh,Option.bind_some,found,Option.getD_some]

/-- Exact unsupported-ID accounting, even for allocations that cannot be
prepared. No old unsupported object is dropped or relabeled. -/
theorem alloc_unsupported {D : Source.Layout} (h : Source.Heap D) (x : Σ τ, Source.Data D τ) :
    unsupported (h.alloc x).1=unsupported h ++ (if (objectShape x.2).isNone then [h.next] else []) := by
  unfold unsupported
  change (List.range (h.next+1)).filter _=_
  rw [List.range_succ,List.filter_append]
  have old : (List.range h.next).filter (fun a=>match (h.alloc x).1.get a with
      | none=>false | some d=>(objectShape d.2).isNone)=
      (List.range h.next).filter (fun a=>match h.get a with
      | none=>false | some d=>(objectShape d.2).isNone) := by
    apply List.filter_congr
    intro a member
    have different : a≠h.next := by have bound:=List.mem_range.mp member;omega
    rw [Source.Heap.alloc_other h x different]
  congr 1
  · rw [List.filter_cons,List.filter_nil]
    have fresh : (h.alloc x).1.get h.next=some x := Source.Heap.alloc_get h x
    simp only [fresh]

theorem alloc_end {D : Source.Layout} (h : Source.Heap D) (x : Σ τ, Source.Data D τ)
    (shape : MemoryShape) (found : objectShape x.2=some shape) :
    position (h.alloc x).1 (h.alloc x).1.next=position h h.next+max 1 shape.size := by
  change position (h.alloc x).1 (h.next+1)=_
  rw [position,alloc_position_prefix h x h.next (Nat.le_refl _),alloc_shape_new h x shape found]
  have fresh : (h.alloc x).1.get h.next=some x := Source.Heap.alloc_get h x
  rw [fresh]
  rfl


theorem alloc_clear {D : Source.Layout} (h : Source.Heap D) (x : Σ τ, Source.Data D τ)
    (clear : unsupported h=[]) (shape : MemoryShape) (found : objectShape x.2=some shape) :
    unsupported (h.alloc x).1=[] := by
  rw [alloc_unsupported,clear,found]
  rfl

theorem objectShape_memory {D : Source.Layout} {τ : Source.STy} (data : Source.Data D τ)
    (shape : MemoryShape) (found : objectShape data=some shape) : τ.loc?=some .memory := by
  cases data with
  | val _ | mapping _ => cases found
  | @bytes l bs => cases l with
    | memory => rfl
    | storage | calldata => cases found
  | @string l bs => cases l with
    | memory => rfl
    | storage | calldata => cases found
  | @array l σ n len hl xs => cases l with
    | memory => rfl
    | storage | calldata => cases found
  | @struct l name fs => cases l with
    | memory => rfl
    | storage | calldata => cases found

theorem objectShape_top {E : Source.Env} {τ : Source.STy} (data : Source.Data E.layout τ)
    (shape : MemoryShape) (found : objectShape data=some shape) : Source.Data.Top (E:=E) data := by
  have shaped := objectShape_sound data shape found
  cases shaped <;> trivial

/-- One actual logical allocation with derived mathematical physical choices.
No allocator-address, freshness, inverse or safety result is supplied. The
new Word bound is the exact computed extent, not a language admission cap. -/
theorem allocRef_geometry {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (s : Source.EMState E Γ) (data : Source.Data E.layout τ) (shape : MemoryShape)
    (found : objectShape data=some shape) (clear : unsupported s.2.heap=[])
    (oldBound : position s.2.heap s.2.heap.next<2^256)
    (newBound : position s.2.heap s.2.heap.next+max 1 shape.size<2^256)
    (valid : Source.DataOK E s.2.heap.ty data) (inner : Source.Data.Inner (E:=E) data) :
    ∃ (p : Placement s.2.heap) (q : Placement (objectAllocatedState s data).2.heap),
      prepare s.2.heap=.ok p ∧ prepare (objectAllocatedState s data).2.heap=.ok q ∧
      (Source.allocRef data).run s=
        (.ok (Source.Val.memRef (objectShape_memory data shape found) s.2.heap.next),objectAllocatedState s data) ∧
      q.address s.2.heap.next=p.free.val ∧ q.free.val=p.free.val+max 1 shape.size ∧
      (∀ a,(s.2.heap.cells a).isSome → q.address a=p.address a ∧ q.shape a=p.shape a) ∧
      (∀ H : Source.HeapTy,Source.MemOK E H s → Source.MemOK E H (objectAllocatedState s data)) := by
  let p := build s.2.heap clear oldBound
  have nextClear := alloc_clear s.2.heap ⟨τ,data⟩ clear shape found
  have nextBound : position (s.2.heap.alloc ⟨τ,data⟩).1 (s.2.heap.alloc ⟨τ,data⟩).1.next<2^256 := by
    rw [alloc_end s.2.heap ⟨τ,data⟩ shape found]
    exact newBound
  let q := build (s.2.heap.alloc ⟨τ,data⟩).1 nextClear nextBound
  refine ⟨p,q,prepare_success _ _ _,prepare_success _ _ _,objectAllocRef_run s data (objectShape_memory data shape found),?_,?_,?_,?_⟩
  · exact alloc_position_prefix s.2.heap ⟨τ,data⟩ s.2.heap.next (Nat.le_refl _)
  · exact alloc_end s.2.heap ⟨τ,data⟩ shape found
  · intro a present
    have bound := occupied_lt s.2.heap a present
    exact ⟨alloc_position_prefix s.2.heap ⟨τ,data⟩ a (by omega),
      alloc_shape_old s.2.heap ⟨τ,data⟩ a (by omega)⟩
  · intro H ok
    exact (objectAllocRef_MemOK H s data (objectShape_memory data shape found)
      (objectShape_top data shape found) inner valid ok).1

end Solidity.Yul.Views.ComputedPlacement
