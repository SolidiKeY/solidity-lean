import Solidity.Yul.Views.AggregateMemoryObjects

namespace Solidity.Yul.Views

inductive MemoryImage {D : Source.Layout} {h : Source.Heap D} (p : Placement h) :
    {τ : Source.STy} → Source.Data D τ → Type where
  | bytes (bs : List UInt8) (bound : bs.length < 2 ^ 256) : MemoryImage p (.bytes (l := .memory) bs)
  | string (bs : List UInt8) (bound : bs.length < 2 ^ 256) : MemoryImage p (.string (l := .memory) bs)
  | words {τ : Source.STy} (d : Source.Data D τ) (ws : List Roadmap.Word)
      (encoded : MemoryObjectWords p d ws) : MemoryImage p d

def memoryArrayImage {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (a : Nat)
    {l : Source.DataLoc} {τ : Source.STy} {n : Option Nat} (len : Nat)
    (hl : ∀ k, n = some k → k = len) (values : Fin len → Source.Val D τ)
    (words : Fin len → Roadmap.Word) (encoded : ∀ i, MemoryElement p (values i) (words i))
    (found : h.get a = some ⟨.array l τ n, .array len hl (fun i => .val (values i))⟩) :
    MemoryImage p (.array (l := l) len hl (fun i => .val (values i))) :=
  .words _ _ (.array len hl (array_length_from_placement p a len hl _ found) values words encoded)

-- Explicit constructor eliminators; no new equation-compiled indexed match.
def MemoryImage.span {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d) : Nat := by
  cases image with
  | bytes bs _ => exact 32 + bs.length
  | string bs _ => exact 32 + bs.length
  | words _ ws _ => exact ws.length * 32

def MemoryImage.encode {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d) (m : ByteView) (base : Nat) : ByteView := by
  cases image with
  | bytes bs bound => exact bytesObjectView bs bound m base
  | string bs bound => exact bytesObjectView bs bound m base
  | words _ ws _ => exact wordListView ws m base

def MemoryImage.Reads {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d) (m : ByteView) (base : Nat) : Prop := by
  cases image with
  | bytes bs bound => exact (mload m base).val = bs.length ∧ readBytes m (base + 32) bs.length = bs
  | string bs bound => exact (mload m base).val = bs.length ∧ readBytes m (base + 32) bs.length = bs
  | words _ ws _ => exact ∀ i w, ws[i]? = some w → mload m (base + i * 32) = w

theorem MemoryImage.encode_reads {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d) (m : ByteView) (base : Nat) :
    image.Reads (image.encode m base) base := by
  cases image with
  | bytes bs bound => exact ⟨congrArg Fin.val (bytesObject_header bs bound m base), bytesObject_payload_list bs bound m base⟩
  | string bs bound => exact ⟨congrArg Fin.val (bytesObject_header bs bound m base), bytesObject_payload_list bs bound m base⟩
  | words d ws e => exact fun i w found => wordList_read ws m base i w found

theorem MemoryImage.fits {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (a : Nat) {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d)
    (found : h.get a = some ⟨τ, d⟩) : image.span ≤ (p.shape a).size := by
  cases image with
  | bytes bs bound =>
    rw [heapByte_placement_shape h p a false bs found]
    exact byte_shape_live_bound _
  | string bs bound =>
    rw [heapByte_placement_shape h p a true bs found]
    exact byte_shape_live_bound _
  | words d ws e => exact e.fits p a found

theorem MemoryImage.residual {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d) (m : ByteView) (base a : Nat)
    (outside : a < base ∨ base + image.span ≤ a) : image.encode m base a = m a := by
  cases image with
  | bytes bs bound => exact bytesObject_residual bs bound m base a (by simpa only [MemoryImage.span, Nat.add_assoc] using outside)
  | string bs bound => exact bytesObject_residual bs bound m base a (by simpa only [MemoryImage.span, Nat.add_assoc] using outside)
  | words d ws e => exact wordList_residual ws m base a outside

theorem MemoryImage.reads_congr {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d) (m m' : ByteView) (base : Nat)
    (same : ∀ i, i < image.span → m (base + i) = m' (base + i))
    (reads : image.Reads m' base) : image.Reads m base := by
  cases image with
  | bytes bs bound =>
    refine ⟨?_, ?_⟩
    · have eq := mload_congr m m' base (fun i => same i.val (by have hi := i.isLt; change i.val < 32 + bs.length; omega))
      exact (congrArg Fin.val eq).trans reads.1
    · rw [readBytes_congr_on m m' (base + 32) bs.length (fun i hi => by
        simpa only [Nat.add_assoc] using same (32 + i) (by change 32 + i < 32 + bs.length; omega))]
      exact reads.2
  | string bs bound =>
    refine ⟨?_, ?_⟩
    · have eq := mload_congr m m' base (fun i => same i.val (by have hi := i.isLt; change i.val < 32 + bs.length; omega))
      exact (congrArg Fin.val eq).trans reads.1
    · rw [readBytes_congr_on m m' (base + 32) bs.length (fun i hi => by
        simpa only [Nat.add_assoc] using same (32 + i) (by change 32 + i < 32 + bs.length; omega))]
      exact reads.2
  | words d ws e =>
    intro i w found
    have hi : i < ws.length := by
      apply Nat.lt_of_not_le
      intro no
      rw [List.getElem?_eq_none (by omega)] at found
      cases found
    rw [mload_congr m m' (base + i * 32) (fun j => by
      have hj := j.isLt
      simpa only [Nat.add_assoc] using same (i * 32 + j.val) (by change i * 32 + j.val < ws.length * 32; omega))]
    exact reads i w found

theorem MemoryImage.unchanged {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d) (m : ByteView) (base : Nat)
    (reads : image.Reads m base) : image.encode m base = m := by
  cases image with
  | bytes bs bound =>
    apply bytesObject_unchanged
    · exact Fin.ext reads.1
    · intro i hi
      have eq := congrArg (fun xs => xs[i]?) reads.2
      rw [List.getElem?_eq_getElem (by simp only [readBytes, List.length_map, List.length_range]; exact hi),
        List.getElem?_eq_getElem hi] at eq
      have value := Option.some.inj eq
      simpa only [readBytes, List.getElem_map, List.getElem_range] using value.symm
  | string bs bound =>
    apply bytesObject_unchanged
    · exact Fin.ext reads.1
    · intro i hi
      have eq := congrArg (fun xs => xs[i]?) reads.2
      rw [List.getElem?_eq_getElem (by simp only [readBytes, List.length_map, List.length_range]; exact hi),
        List.getElem?_eq_getElem hi] at eq
      have value := Option.some.inj eq
      simpa only [readBytes, List.getElem_map, List.getElem_range] using value.symm
  | words d ws e => exact wordList_unchanged ws m base reads

theorem MemoryImage.source_word {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d) (m : ByteView) (base off : Nat)
    (reads : image.Reads m base) (w : Roadmap.Word) (read : ObjectWord p.address d off w) :
    mload m (base + off) = w := by
  cases image with
  | bytes bs bound => cases read; apply Fin.ext; simpa only [Nat.add_zero] using reads.1
  | string bs bound => cases read; apply Fin.ext; simpa only [Nat.add_zero] using reads.1
  | words d ws e =>
    obtain ⟨i, nth, eq⟩ := e.read off w read
    rw [eq]
    exact reads i w nth

theorem readBytes_element (m : ByteView) (base : Nat) (bs : List UInt8)
    (read : readBytes m base bs.length = bs) (i : Fin bs.length) : m (base + i.val) = bs[i.val] := by
  have eq := congrArg (fun xs => xs[i.val]?) read
  rw [List.getElem?_eq_getElem (by simp only [readBytes, List.length_map, List.length_range]; exact i.isLt),
    List.getElem?_eq_getElem i.isLt] at eq
  have value := Option.some.inj eq
  simpa only [readBytes, List.getElem_map, List.getElem_range] using value

theorem MemoryImage.source_byte {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d) (m : ByteView) (base off : Nat)
    (reads : image.Reads m base) (v : UInt8) (read : ObjectByte d off v) : m (base + off) = v := by
  cases image with
  | bytes bs bound => cases read with
    | bytes _ i => simpa only [← Nat.add_assoc] using readBytes_element m (base + 32) bs reads.2 i
  | string bs bound => cases read with
    | string _ i => simpa only [← Nat.add_assoc] using readBytes_element m (base + 32) bs reads.2 i
  | words d ws e => cases e <;> cases read

theorem MemoryImage.reserved {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d) (m : ByteView) (base : Nat)
    (free : Roadmap.Word) (start : 128 ≤ base) (reserved : ReservedOK m free) :
    ReservedOK (image.encode m base) free := by
  constructor
  · have eq := mload_congr (image.encode m base) m 64 (fun i => image.residual m base (64 + i.val) (Or.inl (by have hi := i.isLt; omega)))
    exact (congrArg Fin.val eq).trans reserved.1
  · intro i
    rw [image.residual m base (96 + i.val) (Or.inl (by have hi := i.isLt; omega))]
    exact reserved.2 i

end Solidity.Yul.Views
