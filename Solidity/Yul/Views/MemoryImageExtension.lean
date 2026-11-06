import Solidity.Yul.Views.MemoryImageReadUniqueness
import Solidity.Yul.Views.HeapAllocationCommute

namespace Solidity.Yul.Views

/-- Forward ownership, rather than false equality of the entire heap type map.
Only actual old owned child lookups/addresses are required. -/
theorem MemoryElement.forward {D : Source.Layout} {h h' : Source.Heap D} {p : Placement h}
    (q : Placement h') (extension : ∀ a σ, h.ty a=some σ → h'.ty a=some σ ∧ q.address a=p.address a)
    {τ : Source.STy} {v : Source.Val D τ} {w : Roadmap.Word} (e : MemoryElement p v w) : MemoryElement q v w := by
  cases e with
  | scalar v w encoded => exact .scalar v w encoded
  | pointer loc a σ owned shape =>
    have facts := extension a σ owned
    have same : ownedPointerWord q a σ facts.1=ownedPointerWord p a σ owned := Fin.ext facts.2
    rw [← same]
    exact .pointer loc a σ facts.1 shape

theorem MemoryFields.forward {D : Source.Layout} {h h' : Source.Heap D} {p : Placement h}
    (q : Placement h') (extension : ∀ a σ, h.ty a=some σ → h'.ty a=some σ ∧ q.address a=p.address a)
    {τs : List Source.STy} {fs : Source.DataList D τs} {ws : List Roadmap.Word} (e : MemoryFields p fs ws) : MemoryFields q fs ws := by
  induction e with
  | nil => exact .nil
  | cons v w encoded fs ws rest ih => exact .cons v w (encoded.forward q extension) fs ws ih

theorem MemoryObjectWords.forward {D : Source.Layout} {h h' : Source.Heap D} {p : Placement h}
    (q : Placement h') (extension : ∀ a σ, h.ty a=some σ → h'.ty a=some σ ∧ q.address a=p.address a)
    {τ : Source.STy} {d : Source.Data D τ} {ws : List Roadmap.Word} (e : MemoryObjectWords p d ws) : MemoryObjectWords q d ws := by
  cases e with
  | value v w encoded => exact .value v w (encoded.forward q extension)
  | array n hl bound vs ws encoded => exact .array n hl bound vs ws (fun i => (encoded i).forward q extension)
  | strct fs ws encoded => exact .strct fs ws (encoded.forward q extension)

/-- Same actual indexed data/words; explicit constructor eliminator following
existing MemoryImage.transport. No equation-compiled indexed intermediate. -/
def MemoryImage.forward {D : Source.Layout} {h h' : Source.Heap D} {p : Placement h}
    (q : Placement h') (extension : ∀ a σ, h.ty a=some σ → h'.ty a=some σ ∧ q.address a=p.address a)
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d) : MemoryImage q d := by
  cases image with
  | bytes bs bound => exact .bytes bs bound
  | string bs bound => exact .string bs bound
  | words d ws encoded => exact .words d ws (encoded.forward q extension)

theorem MemoryImage.forward_reads {D : Source.Layout} {h h' : Source.Heap D} {p : Placement h}
    (q : Placement h') (extension : ∀ a σ, h.ty a=some σ → h'.ty a=some σ ∧ q.address a=p.address a)
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d) (m : ByteView) (base : Nat) :
    (image.forward q extension).Reads m base ↔ image.Reads m base := by cases image <;> rfl

theorem heapAlloc_owned_extension {D : Source.Layout} (h : Source.Heap D) (p : Placement h) {τ}
    (data : Source.Data D τ) (shape : MemoryShape) (shaped : HasMemoryShape data shape)
    (base : Nat) (free : Roadmap.Word) (after : p.free.val≤base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a≠base) (fits : base+shape.size≤free.val) :
    ∀ a σ, h.ty a=some σ → (h.alloc ⟨τ,data⟩).1.ty a=some σ ∧
      (heapAllocPlacement h p data shape shaped base free after fresh fits).address a=p.address a := by
  intro a σ owned
  exact ⟨heap_alloc_old_type h ⟨τ,data⟩ a σ owned,
    (heapAllocPlacement_old h p data shape shaped base free after fresh fits a (heap_type_present h a σ owned)).1⟩

end Solidity.Yul.Views
