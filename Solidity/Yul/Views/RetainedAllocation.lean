import Solidity.Yul.Views.HeapByteResizePlacement

/-! Retained ordinary-object allocation evidence. The origin is an actual typed
heap and valid allocation Placement, never an address gap/free-pointer estimate.
Current shapes remain exact; full original regions remain disjoint. No source
state, owner Placement or existing resize guard is changed. -/
namespace Solidity.Yul.Views

structure RetainedGeometry {D : Source.Layout} {origin h : Source.Heap D}
    (allocated : Placement origin) (current : Placement h) : Prop where
  occupancy : ∀ a, (h.cells a).isSome = (origin.cells a).isSome
  addresses : current.address = allocated.address
  free : current.free = allocated.free
  fits : ∀ a, (h.cells a).isSome → (current.shape a).size ≤ (allocated.shape a).size

def retainGeometryInitial {D : Source.Layout} (h : Source.Heap D) (p : Placement h) : RetainedGeometry p p :=
  ⟨fun _ => rfl, rfl, rfl, fun _ _ => Nat.le_refl _⟩

/-- Construct the current output placement against the original full extents. -/
def retainedGeometryWritePlacement {D : Source.Layout} {origin h : Source.Heap D}
    (allocated : Placement origin) (current : Placement h) (r : RetainedGeometry allocated current)
    (a : Nat) {τ : Source.STy} (d : Source.Data D τ) (ht : h.ty a = some τ)
    (shape : MemoryShape) (typed : HasMemoryShape d shape)
    (capacity : shape.size ≤ (allocated.shape a).size) : Placement (h.write a d ht) where
  address := current.address
  shape b := if b = a then shape else current.shape b
  free := current.free
  free_start := current.free_start
  distinct b c hb hc he := current.distinct b c
    (by rwa [heap_write_occupancy] at hb) (by rwa [heap_write_occupancy] at hc) he
  typed b σ x hb := by
    change (h.write a d ht).get b = some ⟨σ, x⟩ at hb
    by_cases he : b = a
    · subst b
      rw [Source.Heap.write_get] at hb
      cases hb
      simpa only [if_true] using typed
    · simp only [if_neg he]
      exact current.typed b σ x (by rw [Source.Heap.write_other h he] at hb; exact hb)
  starts b hb := current.starts b (by rwa [heap_write_occupancy] at hb)
  ends b hb := by
    have present : (h.cells b).isSome := by rwa [heap_write_occupancy] at hb
    have old := allocated.ends b (by rwa [← r.occupancy b])
    have fit : (if b = a then shape else current.shape b).size ≤ (allocated.shape b).size := by
      by_cases he : b = a
      · subst b; simpa only [if_true] using capacity
      · simpa only [if_neg he] using r.fits b present
    rw [← r.addresses, ← r.free] at old
    exact Nat.le_trans (Nat.add_le_add_left fit _) old
  separate b c hb hc hn := by
    have pb : (h.cells b).isSome := by rwa [heap_write_occupancy] at hb
    have pc : (h.cells c).isSome := by rwa [heap_write_occupancy] at hc
    have old := allocated.separate b c (by rwa [← r.occupancy b]) (by rwa [← r.occupancy c]) hn
    rw [← r.addresses] at old
    have smaller (i : Nat) (hi : (h.cells i).isSome) :
        (if i = a then shape else current.shape i).size ≤ (allocated.shape i).size := by
      by_cases he : i = a
      · subst i; simpa only [if_true] using capacity
      · simpa only [if_neg he] using r.fits i hi
    rcases old with old | old
    · exact Or.inl (Nat.le_trans (Nat.add_le_add_left (smaller b pb) _) old)
    · exact Or.inr (Nat.le_trans (Nat.add_le_add_left (smaller c pc) _) old)

theorem retainGeometryWritten {D : Source.Layout} {origin h : Source.Heap D}
    (allocated : Placement origin) (current : Placement h) (r : RetainedGeometry allocated current)
    (a : Nat) {τ : Source.STy} (d : Source.Data D τ) (ht : h.ty a = some τ)
    (shape : MemoryShape) (typed : HasMemoryShape d shape)
    (capacity : shape.size ≤ (allocated.shape a).size) :
    RetainedGeometry allocated (retainedGeometryWritePlacement allocated current r a d ht shape typed capacity) := by
  refine ⟨?_, r.addresses, r.free, ?_⟩
  · intro b; rw [heap_write_occupancy]; exact r.occupancy b
  · intro b hb
    change (if b = a then shape else current.shape b).size ≤ _
    by_cases he : b = a
    · subst b; simpa only [if_true] using capacity
    · simp only [if_neg he]
      exact r.fits b (by rwa [heap_write_occupancy] at hb)

/-- Constructive lineage from the supplied actual allocation snapshot. Geometry
alone is insufficient provenance: each step records an actual typed Heap.write.
The integrated allocator must establish the initial snapshot/placement. -/
inductive RetainedAllocation {D : Source.Layout} {origin : Source.Heap D} (allocated : Placement origin) :
    {h : Source.Heap D} → Placement h → Prop where
  | initial : RetainedAllocation allocated allocated
  | written {h : Source.Heap D} (current : Placement h) (r : RetainedGeometry allocated current)
      (prior : RetainedAllocation allocated current) (a : Nat) {τ : Source.STy}
      (d : Source.Data D τ) (ht : h.ty a = some τ) (shape : MemoryShape)
      (typed : HasMemoryShape d shape) (capacity : shape.size ≤ (allocated.shape a).size) :
      RetainedAllocation allocated (retainedGeometryWritePlacement allocated current r a d ht shape typed capacity)

def RetainedAllocation.geometry {D : Source.Layout} {origin h : Source.Heap D}
    {allocated : Placement origin} {current : Placement h} (r : RetainedAllocation allocated current) :
    RetainedGeometry allocated current := by
  cases r with
  | initial => exact retainGeometryInitial _ _
  | written current r prior a d ht shape typed capacity => exact retainGeometryWritten _ _ r a d ht shape typed capacity

def RetainedAllocation.occupancy {D : Source.Layout} {origin h : Source.Heap D}
    {allocated : Placement origin} {current : Placement h} (r : RetainedAllocation allocated current) := r.geometry.occupancy
def RetainedAllocation.addresses {D : Source.Layout} {origin h : Source.Heap D}
    {allocated : Placement origin} {current : Placement h} (r : RetainedAllocation allocated current) := r.geometry.addresses
def RetainedAllocation.free {D : Source.Layout} {origin h : Source.Heap D}
    {allocated : Placement origin} {current : Placement h} (r : RetainedAllocation allocated current) := r.geometry.free
def RetainedAllocation.fits {D : Source.Layout} {origin h : Source.Heap D}
    {allocated : Placement origin} {current : Placement h} (r : RetainedAllocation allocated current) := r.geometry.fits

def retainInitial {D : Source.Layout} (h : Source.Heap D) (p : Placement h) : RetainedAllocation p p := .initial

def retainedWritePlacement {D : Source.Layout} {origin h : Source.Heap D}
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a : Nat) {τ : Source.STy} (d : Source.Data D τ) (ht : h.ty a = some τ)
    (shape : MemoryShape) (typed : HasMemoryShape d shape)
    (capacity : shape.size ≤ (allocated.shape a).size) : Placement (h.write a d ht) :=
  retainedGeometryWritePlacement allocated current r.geometry a d ht shape typed capacity

theorem retainWritten {D : Source.Layout} {origin h : Source.Heap D}
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a : Nat) {τ : Source.STy} (d : Source.Data D τ) (ht : h.ty a = some τ)
    (shape : MemoryShape) (typed : HasMemoryShape d shape)
    (capacity : shape.size ≤ (allocated.shape a).size) :
    RetainedAllocation allocated (retainedWritePlacement allocated current r a d ht shape typed capacity) :=
  .written current r.geometry r a d ht shape typed capacity

def retainedByteWriteback {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (_r : RetainedAllocation allocated current)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩) (m : ByteView) : Option (Source.Heap D) :=
  if (MemoryShape.bytes (mload m (current.address a)).val).size ≤ (allocated.shape a).size then
    some (h.write a (decodeHeapByte D string m (current.address a)) (heap_ty_of_get h a _ _ found))
  else none

theorem retainedByte_success {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (m : ByteView) (out : Source.Heap D) (e : retainedByteWriteback h allocated current r a string old found m = some out) :
    (MemoryShape.bytes (mload m (current.address a)).val).size ≤ (allocated.shape a).size ∧
    out = h.write a (decodeHeapByte D string m (current.address a)) (heap_ty_of_get h a _ _ found) := by
  unfold retainedByteWriteback at e
  split at e
  · exact ⟨‹_›, (Option.some.inj e).symm⟩
  · cases e

/-- Existing bounded success is compatible; the old guard itself is unchanged. -/
theorem retainedByte_compat {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (m : ByteView) (out : Source.Heap D) (e : heapByteResizeWriteback h current a string old found m = some out) :
    retainedByteWriteback h allocated current r a string old found m = some out := by
  have success := heapByteResize_success h current a string old found m out e
  have present : (h.cells a).isSome := by change (h.get a).isSome = true; rw [found]; rfl
  have bound := Nat.le_trans success.1 (r.fits a present)
  simp only [retainedByteWriteback, if_pos bound]
  rw [success.2]

def retainedByteResultPlacement {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (m : ByteView) (out : Source.Heap D) (e : retainedByteWriteback h allocated current r a string old found m = some out) : Placement out :=
  (retainedByte_success h allocated current r a string old found m out e).2.symm ▸
    retainedWritePlacement allocated current r a _ _ (.bytes (mload m (current.address a)).val)
      (decodeHeapByte_shape D string m (current.address a))
      (retainedByte_success h allocated current r a string old found m out e).1

theorem retainedByte_result_history {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (m : ByteView) (out : Source.Heap D) (e : retainedByteWriteback h allocated current r a string old found m = some out) :
    RetainedAllocation allocated (retainedByteResultPlacement h allocated current r a string old found m out e) := by
  have he := (retainedByte_success h allocated current r a string old found m out e).2
  subst out
  exact retainWritten allocated current r a _ _ (.bytes (mload m (current.address a)).val)
    (decodeHeapByte_shape D string m (current.address a))
    (retainedByte_success h allocated current r a string old found m _ e).1

theorem retainedByte_encode {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a : Nat) (string : Bool) (old bs : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (hl : bs.length < 2 ^ 256) (capacity : (MemoryShape.bytes bs.length).size ≤ (allocated.shape a).size) (m : ByteView) :
    retainedByteWriteback h allocated current r a string old found (bytesObjectView bs hl m (current.address a)) =
      some (h.write a (heapByteData D string bs) (heap_ty_of_get h a _ _ found)) := by
  simp only [retainedByteWriteback, bytesObject_header, if_pos capacity]
  rw [decodeHeapByte_encode]

theorem retainedByte_unchanged {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩) (m : ByteView)
    (header : (mload m (current.address a)).val = old.length)
    (payload : readBytes m (current.address a + 32) old.length = old) :
    retainedByteWriteback h allocated current r a string old found m = some h :=
  retainedByte_compat h allocated current r a string old found m h
    (heapByteResize_unchanged h current a string old found m header payload)

theorem retainedByte_preservation {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (m : ByteView) (out : Source.Heap D) (e : retainedByteWriteback h allocated current r a string old found m = some out) :
    out.ty = h.ty ∧ out.next = h.next ∧ (∀ b, h.next ≤ b → out.cells b = none) ∧
    (∀ b, b ≠ a → out.get b = h.get b) ∧
    out.get a = some ⟨heapByteType string, decodeHeapByte D string m (current.address a)⟩ := by
  rw [(retainedByte_success h allocated current r a string old found m out e).2]
  exact ⟨funext (fun b => Source.Heap.write_ty _ _ b _ _), rfl,
    fun b hb => (h.write a _ _).bounded b hb,
    fun b hb => Source.Heap.write_other _ hb _ _, Source.Heap.write_get _ _ _ _⟩

theorem retainedByte_full_separation {D : Source.Layout} {origin h : Source.Heap D}
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a b : Nat) (ha : (h.cells a).isSome) (hb : (h.cells b).isSome) (distinct : a ≠ b) :
    128 ≤ current.address a ∧ current.address a + (allocated.shape a).size ≤ current.free.val ∧
    (current.address a + (allocated.shape a).size ≤ current.address b ∨
     current.address b + (allocated.shape b).size ≤ current.address a) := by
  rw [r.addresses, r.free]
  exact ⟨allocated.starts a (by rwa [← r.occupancy a]), allocated.ends a (by rwa [← r.occupancy a]),
    allocated.separate a b (by rwa [← r.occupancy a]) (by rwa [← r.occupancy b]) distinct⟩

theorem retainedByte_other_region {D : Source.Layout} {origin h : Source.Heap D}
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a b : Nat) (ha : (h.cells a).isSome) (hb : (h.cells b).isSome) (distinct : a ≠ b)
    (bs : List UInt8) (hl : bs.length < 2 ^ 256)
    (capacity : (MemoryShape.bytes bs.length).size ≤ (allocated.shape a).size)
    (m : ByteView) (off : Nat) (hoff : off < (allocated.shape b).size) :
    bytesObjectView bs hl m (current.address a) (current.address b + off) = m (current.address b + off) := by
  have sep := (retainedByte_full_separation allocated current r a b ha hb distinct).2.2
  have live := byte_shape_live_bound bs.length
  apply bytesObject_residual
  omega

def retainedByteStateWriteback {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (current : Placement s.2.heap)
    (r : RetainedAllocation allocated current) (a : Nat) (string : Bool) (old : List UInt8)
    (found : s.2.heap.get a = some ⟨heapByteType string, heapByteData E.layout string old⟩)
    (m : ByteView) : Option (Source.EMState E Γ) :=
  (retainedByteWriteback s.2.heap allocated current r a string old found m).map (withSourceHeap s)

theorem retainedByteState_MemOK (E : Source.Env) {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s out : Source.EMState E Γ) (allocated : Placement origin)
    (current : Placement s.2.heap) (r : RetainedAllocation allocated current)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : s.2.heap.get a = some ⟨heapByteType string, heapByteData E.layout string old⟩)
    (m : ByteView) (e : retainedByteStateWriteback s allocated current r a string old found m = some out)
    (ok : Source.MemOK E H s) : Source.MemOK E H out := by
  obtain ⟨heap, hw, hs⟩ := Option.map_eq_some_iff.mp e
  subst out
  rw [(retainedByte_success s.2.heap allocated current r a string old found m heap hw).2, decodeHeapByte_data]
  exact heapByte_write_MemOK E H s a string _ _ ok

theorem retainedByte_result_choices {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (m : ByteView) (out : Source.Heap D) (e : retainedByteWriteback h allocated current r a string old found m = some out) :
    let q := retainedByteResultPlacement h allocated current r a string old found m out e
    q.address = current.address ∧ q.free = current.free ∧ q.shape a = .bytes (mload m (current.address a)).val ∧
      ∀ b, b ≠ a → q.shape b = current.shape b := by
  have he := (retainedByte_success h allocated current r a string old found m out e).2
  subst out
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp only [retainedByteResultPlacement, retainedWritePlacement, retainedGeometryWritePlacement, if_true]
  · intro b hb
    simp only [retainedByteResultPlacement, retainedWritePlacement, retainedGeometryWritePlacement, if_neg hb]

theorem retainedByte_live_view {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (r : RetainedAllocation allocated current)
    (a : Nat) (string : Bool) (old : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (m : ByteView) (out : Source.Heap D) (e : retainedByteWriteback h allocated current r a string old found m = some out) :
    ∃ bs : List UInt8, ∃ hl : bs.length < 2 ^ 256,
      out.get a = some ⟨heapByteType string, heapByteData D string bs⟩ ∧
      (mload m (current.address a)).val = bs.length ∧
      (∀ i (hi : i < bs.length), bs[i] = m (current.address a + 32 + i)) ∧
      bytesObjectView bs hl m (current.address a) = m := by
  let bs := readBytes m (current.address a + 32) (mload m (current.address a)).val
  have length : bs.length = (mload m (current.address a)).val := by
    simp only [bs, readBytes, List.length_map, List.length_range]
  refine ⟨bs, by rw [length]; exact (mload m (current.address a)).isLt, ?_, length.symm, ?_, ?_⟩
  · rw [(retainedByte_preservation h allocated current r a string old found m out e).2.2.2.2, decodeHeapByte_data]
  · intro i hi
    simp only [bs, readBytes, List.getElem_map, List.getElem_range]
  · exact bytesObject_decode_reencode m (current.address a)

theorem bytesObject_disjoint_commute (xs ys : List UInt8)
    (hx : xs.length < 2 ^ 256) (hy : ys.length < 2 ^ 256) (m : ByteView) (a b : Nat)
    (separate : a + 32 + xs.length ≤ b ∨ b + 32 + ys.length ≤ a) :
    bytesObjectView ys hy (bytesObjectView xs hx m a) b =
      bytesObjectView xs hx (bytesObjectView ys hy m b) a := by
  funext i
  by_cases xp : a + 32 ≤ i ∧ i < a + 32 + xs.length
  · have yp : ¬ (b + 32 ≤ i ∧ i < b + 32 + ys.length) := by omega
    have yh : ¬ (b ≤ i ∧ i < b + 32) := by omega
    simp only [bytesObjectView, copyBytes, if_pos xp, if_neg yp, mstore, dif_neg yh]
  · by_cases yp : b + 32 ≤ i ∧ i < b + 32 + ys.length
    · have xh : ¬ (a ≤ i ∧ i < a + 32) := by omega
      simp only [bytesObjectView, copyBytes, if_pos yp, if_neg xp, mstore, dif_neg xh]
    · by_cases xh : a ≤ i ∧ i < a + 32
      · have yh : ¬ (b ≤ i ∧ i < b + 32) := by omega
        simp only [bytesObjectView, copyBytes, if_neg xp, if_neg yp, mstore, dif_pos xh, dif_neg yh]
      · by_cases yh : b ≤ i ∧ i < b + 32
        · simp only [bytesObjectView, copyBytes, if_neg xp, if_neg yp, mstore, dif_neg xh, dif_pos yh]
        · simp only [bytesObjectView, copyBytes, if_neg xp, if_neg yp, mstore, dif_neg xh, dif_neg yh]

end Solidity.Yul.Views
