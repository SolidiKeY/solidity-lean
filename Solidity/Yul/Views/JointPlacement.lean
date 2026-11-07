import Solidity.Yul.Views.JointMemory

-- Retain dependent placement reductions in the existing 4.35 proof bodies.
set_option backward.isDefEq.respectTransparency false

namespace Solidity.Yul.Views

/-- Two actual same-type writes, with proof terms erased by proof irrelevance. -/
def pairWrittenHeap {D : Source.Layout} (h : Source.Heap D) (a : Nat) {τ : Source.STy} (x : Source.Data D τ)
    (ha : h.ty a = some τ) (b : Nat) {σ : Source.STy} (y : Source.Data D σ) (hb : h.ty b = some σ) : Source.Heap D :=
  (h.write a x ha).write b y (by rw [Source.Heap.write_ty]; exact hb)

def pairWrittenPlacement {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) {τ : Source.STy} (x : Source.Data D τ) (ha : h.ty a = some τ)
    (sx : HasMemoryShape x (p.shape a)) (b : Nat) {σ : Source.STy} (y : Source.Data D σ)
    (hb : h.ty b = some σ) (sy : HasMemoryShape y (p.shape b)) : Placement (pairWrittenHeap h a x ha b y hb) :=
  heapWritePlacement _ (heapWritePlacement h p a x ha sx) b y _ sy

theorem pairWritten_preserves {D : Source.Layout} (h : Source.Heap D) (a : Nat) {τ : Source.STy} (x : Source.Data D τ)
    (ha : h.ty a = some τ) (b : Nat) {σ : Source.STy} (y : Source.Data D σ) (hb : h.ty b = some σ) :
    (pairWrittenHeap h a x ha b y hb).ty = h.ty ∧
    (pairWrittenHeap h a x ha b y hb).next = h.next ∧
    (∀ c, h.next ≤ c → (pairWrittenHeap h a x ha b y hb).cells c = none) ∧
    ∀ c, c ≠ a → c ≠ b → (pairWrittenHeap h a x ha b y hb).get c = h.get c := by
  refine ⟨funext (fun c => ?_), rfl, ?_, ?_⟩
  · rw [pairWrittenHeap, Source.Heap.write_ty, Source.Heap.write_ty]
  · exact (pairWrittenHeap h a x ha b y hb).bounded
  · intro c ca cb
    rw [pairWrittenHeap, Source.Heap.write_other _ cb, Source.Heap.write_other _ ca]

theorem pairWritten_readback {D : Source.Layout} (h : Source.Heap D) (a : Nat) {τ : Source.STy} (x : Source.Data D τ)
    (ha : h.ty a = some τ) (b : Nat) {σ : Source.STy} (y : Source.Data D σ) (hb : h.ty b = some σ) (distinct : a ≠ b) :
    (pairWrittenHeap h a x ha b y hb).get a = some ⟨τ,x⟩ ∧ (pairWrittenHeap h a x ha b y hb).get b = some ⟨σ,y⟩ := by
  constructor
  · rw [pairWrittenHeap, Source.Heap.write_other _ distinct, Source.Heap.write_get]
  · exact Source.Heap.write_get _ _ _ _

/-- Build refreshed concrete candidate entries after EACH actual write. The
images are intrinsic constructor encodings, not a read/inverse premise. -/
def pairWrittenEntries {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (es : List (MixedHeapEntry p)) (a : Nat) {τ : Source.STy} (x : Source.Data D τ)
    (ha : h.ty a = some τ) (sx : HasMemoryShape x (p.shape a)) (ix : MemoryImage p x)
    (b : Nat) {σ : Source.STy} (y : Source.Data D σ) (hb : h.ty b = some σ)
    (sy : HasMemoryShape y (p.shape b)) (iy : MemoryImage p y) : List (MixedHeapEntry (pairWrittenPlacement h p a x ha sx b y hb sy)) :=
  let p1 := heapWritePlacement h p a x ha sx
  let t1 := funext (fun c => Source.Heap.write_ty h a c x ha)
  let p2 := pairWrittenPlacement h p a x ha sx b y hb sy
  let t2 := (pairWritten_preserves h a x ha b y hb).1
  refreshMixedEntries p1 b y _ p2 rfl (iy.transport p2 t2 rfl)
    (refreshMixedEntries p a x ha p1 rfl (ix.transport p1 t1 rfl) es)

theorem pairWrittenEntries_coverage {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (a : Nat) {τ : Source.STy} (x : Source.Data D τ)
    (ha : h.ty a = some τ) (sx : HasMemoryShape x (p.shape a)) (ix : MemoryImage p x)
    (b : Nat) {σ : Source.STy} (y : Source.Data D σ) (hb : h.ty b = some σ)
    (sy : HasMemoryShape y (p.shape b)) (iy : MemoryImage p y) :
    CoversMixedHeap (pairWrittenEntries h p es a x ha sx ix b y hb sy iy) := by
  exact refreshMixedEntries_coverage _ _ _ _ _ _ _ _ (refreshMixedEntries_coverage p a x ha _ _ _ es coverage)

theorem pairWrittenEntries_decoder {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (es : List (MixedHeapEntry p)) (a : Nat) {τ : Source.STy} (x : Source.Data D τ)
    (ha : h.ty a = some τ) (sx : HasMemoryShape x (p.shape a)) (ix : MemoryImage p x)
    (b : Nat) {σ : Source.STy} (y : Source.Data D σ) (hb : h.ty b = some σ)
    (sy : HasMemoryShape y (p.shape b)) (iy : MemoryImage p y) (υ : Source.STy) (w : Roadmap.Word) :
    decodeExtendedMemoryMember (pairWrittenPlacement h p a x ha sx b y hb sy)
      (pairWrittenEntries h p es a x ha sx ix b y hb sy iy) υ w = decodeExtendedMemoryMember p es υ w := by
  unfold pairWrittenEntries
  rw [decodeExtended_refresh, decodeExtended_refresh]

theorem struct_shape_write {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (a : Nat) (name : Source.DeclName)
    (old fs : Source.DataList D (D.fields name)) (found : h.get a = some ⟨.struct .memory name,.struct old⟩) :
    HasMemoryShape (.struct (l := .memory) fs) (p.shape a) := by
  have shape := p.typed a _ _ found
  generalize eq : p.shape a = sh at shape
  cases shape
  exact .strct fs

/-- Concrete joint output placement and entries for the actual struct/array
constructors. Pointer images are transported from the real decoded values. -/
theorem canonicalJoint_geometry {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (a : Nat) (name : Source.DeclName)
    (oldfs fs : Source.DataList E.layout (E.layout.fields name))
    (fa : h.get a = some ⟨.struct .memory name,.struct oldfs⟩)
    (b : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ z, k = some z → z = n)
    (old values : Fin n → Source.Val E.layout τ)
    (fb : h.get b = some ⟨_,memberArrayData E.layout τ k n hl old⟩)
    (m : ByteView) (df : decodeCanonicalFields p es (E.layout.fields name) m (p.address a) = some fs)
    (da : decodeCanonicalArray p es τ n m (p.address b + arrayPayloadOffset k) = some values) :
    let out := pairWrittenHeap h a (.struct fs) (heap_ty_of_get h a _ _ fa) b
      (memberArrayData E.layout τ k n hl values) (heap_ty_of_get h b _ _ fb)
    ∃ q : Placement out, q.address = p.address ∧ q.shape = p.shape ∧ q.free = p.free ∧
      ∃ entries : List (MixedHeapEntry q), CoversMixedHeap entries ∧
        ∀ υ w, decodeExtendedMemoryMember q entries υ w = decodeExtendedMemoryMember p es υ w := by
  obtain ⟨ws, fields, reads⟩ := decodeCanonicalFields_representation p es _ m _ fs df
  have sx := struct_shape_write h p a name oldfs fs fa
  have sy : HasMemoryShape (memberArrayData E.layout τ k n hl values) (p.shape b) := by
    rw [memberArray_shape h p b τ k n hl old fb]
    exact .array n hl _
  let ix : MemoryImage p (.struct (l := .memory) fs) := .words _ ws (.strct fs ws fields)
  let iy : MemoryImage p (memberArrayData E.layout τ k n hl values) := .words _ _
    (.array n hl (array_length_from_placement p b n hl _ fb) values
      (fun i => mload m (p.address b + arrayPayloadOffset k + i.val * 32)) (decodeCanonicalArray_sound p es τ n m _ values da))
  refine ⟨pairWrittenPlacement h p a (.struct fs) _ sx b _ _ sy, rfl, rfl, rfl,
    pairWrittenEntries h p es a (.struct fs) _ sx ix b _ _ sy iy,
    pairWrittenEntries_coverage h p es coverage a (.struct fs) _ sx ix b _ _ sy iy, ?_⟩
  exact pairWrittenEntries_decoder h p es a (.struct fs) _ sx ix b _ _ sy iy

theorem placement_choices_ext {D : Source.Layout} {h : Source.Heap D} (p q : Placement h)
    (addresses : p.address = q.address) (shapes : p.shape = q.shape) (free : p.free = q.free) : p = q := by
  cases p
  cases q
  cases addresses
  cases shapes
  cases free
  rfl

/-- Real retained allocation lineage through any same-shape typed write. -/
theorem retainSameShapeWrite {D : Source.Layout} {origin h : Source.Heap D}
    (allocated : Placement origin) (p : Placement h) (history : RetainedAllocation allocated p)
    (a : Nat) {τ : Source.STy} (x : Source.Data D τ) (ha : h.ty a = some τ)
    (shape : HasMemoryShape x (p.shape a)) : RetainedAllocation allocated (heapWritePlacement h p a x ha shape) := by
  have present : (h.cells a).isSome := by
    have yes := congrArg Option.isSome ha
    simpa only [Source.Heap.ty, Option.isSome_map, Option.isSome_some] using yes
  have actual := retainWritten allocated p history a x ha (p.shape a) shape (history.fits a present)
  have eq : retainedWritePlacement allocated p history a x ha (p.shape a) shape (history.fits a present) = heapWritePlacement h p a x ha shape := by
    refine placement_choices_ext (retainedWritePlacement allocated p history a x ha (p.shape a) shape (history.fits a present))
      (heapWritePlacement h p a x ha shape) rfl ?_ rfl
    funext c
    change (if c = a then p.shape a else p.shape c) = p.shape c
    split
    · rename_i same; rw [same]
    · rfl
  rw [eq] at actual
  exact actual

end Solidity.Yul.Views
