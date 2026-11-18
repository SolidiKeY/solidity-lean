import Solidity.Yul.Layout.Geometry
import Solidity.Yul.Views.MemberArray
import Solidity.Yul.Views.EnumeratedMemory

/-!
# The memory instance facts of the layout view

The four memory fields of `Shrink.LayoutView.Instances`, for `geometry`:
`wordList`, `memberArray`, `bytesObject` and `enumerated`. Each statement is
the field's, with `geometry` for `V.geometry`; none mentions an allocator.

A memory object of words is read word by word (`read_words`) and occupies
exactly its words (`elem_cells`). The footprint of a dynamic object depends on
its stored length word, so `enumerated` reads that word back from the image
(`header`) before it uses `Placement.separate`.
-/
namespace Solidity.Yul.Layout.Instances

open Solidity.Goals
open Solidity.Yul.Views

/-- A memory word is below `256 ^ 32`, the bound of a 32-byte scalar. -/
private theorem mloadNat_lt (b : ByteView) (a : Nat) : mloadNat b a < 256 ^ 32 :=
  (by decide : (256 : Nat) ^ 32 = 2 ^ 256) ▸ (mload b a).isLt

/-- A memory word reads as `mloadNat`, cleaned or not, at every offset mark. -/
private theorem read_word (P : Shrink.Params) (a o : Nat) (m : Shrink.Phys) :
    geometry.read P (.scalar 32) ⟨.memory, a, o⟩ m = some (.leaf (mloadNat m.memory a)) := by
  simp only [Shrink.Geometry.read, geometry, if_true, Nat.mod_eq_of_lt (mloadNat_lt _ _), ite_self,
    Option.map_some]

/-- A run of memory words reads as their `mloadNat`s. -/
private theorem read_words (P : Shrink.Params) (base n i : Nat) (m : Shrink.Phys) :
    geometry.readElems P (.scalar 32) ⟨.memory, base, 0⟩ n i m =
      some ((List.range' i n).map fun j => .leaf (mloadNat m.memory (base + 32 * j))) := by
  induction n generalizing i with
  | zero => simp only [Shrink.Geometry.readElems, List.range'_zero, List.map_nil]
  | succ n ih =>
    have el : geometry.elem P (.scalar 32) ⟨.memory, base, 0⟩ i = ⟨.memory, base + 32 * i, 0⟩ := rfl
    simp only [Shrink.Geometry.readElems, el, read_word, ih, List.range'_succ, List.map_cons]
    rfl

/-- The words of a serialized list, read back. -/
private theorem words_eq (b : ByteView) (base : Nat) (ws : List Roadmap.Word)
    (reads : ∀ i w, ws[i]? = some w → mload b (base + i * 32) = w) :
    ((List.range' 0 ws.length).map fun j => Shrink.Tree.leaf (mloadNat b (base + 32 * j))) =
      ws.map fun w => .leaf w.val := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range']
  · intro i _ hi
    have hw : i < ws.length := by simpa only [List.length_map] using hi
    simp only [List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul]
    rw [Nat.mul_comm]
    exact congrArg (fun w : Roadmap.Word => Shrink.Tree.leaf w.val)
      (reads i ws[i] (List.getElem?_eq_getElem hw))

/-- A run of memory words occupies exactly its bytes. -/
private theorem elem_cells (P : Shrink.Params) (base n i : Nat) (m : Shrink.Phys) (c : Shrink.Cell) :
    geometry.elemCells P (.scalar 32) ⟨.memory, base, 0⟩ n i m c ↔
      Shrink.objectCells (base + 32 * i) (n * 32) c := by
  induction n generalizing i with
  | zero => cases c <;> simp only [Shrink.Geometry.elemCells, Shrink.objectCells, false_iff] <;> omega
  | succ n ih =>
    have el : geometry.elem P (.scalar 32) ⟨.memory, base, 0⟩ i = ⟨.memory, base + 32 * i, 0⟩ := rfl
    have sc : geometry.scalarCells P 32 ⟨.memory, base + 32 * i, 0⟩ c =
        Shrink.objectCells (base + 32 * i) 32 c := rfl
    simp only [Shrink.Geometry.elemCells, Shrink.Geometry.cells, el, sc, ih]
    cases c <;> simp only [Shrink.objectCells, or_self] <;> omega

/-- **`wordListView`**: a fixed array of words, and exactly its bytes. -/
theorem wordList (P : Shrink.Params) (ws : List Roadmap.Word) (r : ByteView) (base : Nat)
    (m : Shrink.Phys) :
    geometry.read P (.fixedArray (.scalar 32) ws.length) ⟨.memory, base, 0⟩
        (m.withMemory (wordListView ws r base)) = some (.node (ws.map fun w => .leaf w.val)) ∧
    ∀ x, geometry.cells P (.fixedArray (.scalar 32) ws.length) ⟨.memory, base, 0⟩
        (m.withMemory (wordListView ws r base)) x ↔ Shrink.objectCells base (ws.length * 32) x := by
  refine ⟨?_, fun x => ?_⟩
  · simp only [Shrink.Geometry.read, read_words, Option.map_some, Shrink.Phys.withMemory,
      words_eq _ base ws (wordList_read ws r base)]
  · simp only [Shrink.Geometry.cells, elem_cells, Nat.mul_zero, Nat.add_zero]

/-- **`memberArrayView`** (and so `dynamicUintView`): a dynamic array when
unsized (length word, then words), fixed otherwise, and exactly its bytes. -/
theorem memberArray (P : Shrink.Params) (k : Option Nat) (n : Nat) (bound : n < 2 ^ 256)
    (words : Fin n → Roadmap.Word) (r : ByteView) (base : Nat) (m : Shrink.Phys) :
    geometry.read P (Shrink.memoryShapeLayout (.array k.isNone n)) ⟨.memory, base, 0⟩
        (m.withMemory (memberArrayView k n bound words r base)) =
      some (.node ((List.ofFn words).map fun w => .leaf w.val)) ∧
    ∀ x, geometry.cells P (Shrink.memoryShapeLayout (.array k.isNone n)) ⟨.memory, base, 0⟩
        (m.withMemory (memberArrayView k n bound words r base)) x ↔
      Shrink.objectCells base (MemoryShape.array k.isNone n).size x := by
  cases k with
  | some k =>
    have fixed := wordList P (List.ofFn words) r base m
    simp only [List.length_ofFn] at fixed
    have size : (MemoryShape.array false n).size = n * 32 := Nat.zero_add _
    exact ⟨fixed.1, fun x => (fixed.2 x).trans (size ▸ Iff.rfl)⟩
  | none =>
    have view : memberArrayView none n bound words r base =
        wordListView (⟨n, bound⟩ :: List.ofFn words) r base := rfl
    generalize memberArrayView none n bound words r base = image at view
    have header : mloadNat image base = n :=
      view ▸ congrArg Fin.val (dynamicUint_header n bound words r base)
    have dl : geometry.data P ⟨.memory, base, 0⟩ (m.withMemory image) = ⟨.memory, base + 32, 0⟩ := rfl
    have ln : geometry.length P ⟨.memory, base, 0⟩ (m.withMemory image) = n := header
    refine ⟨?_, fun x => ?_⟩
    · have reads : ∀ i w, (List.ofFn words)[i]? = some w → mload image (base + 32 + i * 32) = w := by
        intro i w found
        have step : base + 32 + i * 32 = base + (i + 1) * 32 := by omega
        rw [step, view]
        exact wordList_read _ r base (i + 1) w found
      have eq := words_eq image (base + 32) (List.ofFn words) reads
      rw [List.length_ofFn] at eq
      simp only [Shrink.memoryShapeLayout, Option.isNone_none, Shrink.Geometry.read, dl, ln,
        read_words, Option.map_some]
      exact congrArg (fun xs => some (Shrink.Tree.node xs)) eq
    · have lc : geometry.lengthCells P ⟨.memory, base, 0⟩ x = Shrink.objectCells base 32 x := rfl
      simp only [Shrink.memoryShapeLayout, Option.isNone_none, Shrink.Geometry.cells, dl, ln, lc,
        elem_cells, MemoryShape.size, if_true]
      cases x <;> simp only [Shrink.objectCells, or_self] <;> omega

/-- **`bytesObjectView`**: a bytes/string object (length word, then bytes); its
footprint lies in the object (padding is not read). -/
theorem bytesObject (P : Shrink.Params) (bs : List UInt8) (bound : bs.length < 2 ^ 256)
    (r : ByteView) (base : Nat) (m : Shrink.Phys) :
    geometry.read P .bytes ⟨.memory, base, 0⟩ (m.withMemory (bytesObjectView bs bound r base)) =
      some (.blob bs) ∧
    ∀ x, geometry.cells P .bytes ⟨.memory, base, 0⟩
        (m.withMemory (bytesObjectView bs bound r base)) x →
      Shrink.objectCells base ((MemoryShape.bytes bs.length).size) x := by
  have header : mloadNat (bytesObjectView bs bound r base) base = bs.length :=
    congrArg Fin.val (bytesObject_header bs bound r base)
  have payload := bytesObject_payload_list bs bound r base
  generalize bytesObjectView bs bound r base = image at header payload
  refine ⟨?_, fun x inside => ?_⟩
  · have bl : geometry.blob P ⟨.memory, base, 0⟩ (m.withMemory image) =
        some (readBytes image (base + 32) (mloadNat image base)) := rfl
    simp only [Shrink.Geometry.read, bl, header, payload, Option.map_some]
  · have lc : geometry.lengthCells P ⟨.memory, base, 0⟩ x = Shrink.objectCells base 32 x := rfl
    have bc : geometry.blobCells P ⟨.memory, base, 0⟩ (m.withMemory image) x =
        Shrink.objectCells (base + 32) (mloadNat image base) x := rfl
    simp only [Shrink.Geometry.cells, lc, bc, header] at inside
    cases x <;> simp only [Shrink.objectCells, or_self, MemoryShape.size] at inside ⊢ <;> omega

/-! ## The placed heap -/

/-- The inline offset of a member of a struct of words. -/
private theorem member_offset (n i : Nat) (le : i ≤ n) :
    memberOffset (List.replicate n (.scalar 32)) i = 32 * i := by
  induction n generalizing i with
  | zero =>
    obtain rfl : i = 0 := by omega
    rfl
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.replicate_succ, memberOffset, memSize, ih i (by omega)]
      omega

/-- Word members read, whatever the member list of the struct. -/
private theorem read_fields (P : Shrink.Params) (all : List Shrink.Layout) (base k i : Nat)
    (m : Shrink.Phys) :
    ∃ xs, Shrink.Layout.FitsFields (List.replicate k (.scalar 32)) xs ∧
      geometry.readFields P all ⟨.memory, base, 0⟩ (List.replicate k (.scalar 32)) i m = some xs := by
  induction k generalizing i with
  | zero =>
    exact ⟨[], by simp only [List.replicate_zero, Shrink.Layout.FitsFields],
      by simp only [List.replicate_zero, Shrink.Geometry.readFields]⟩
  | succ k ih =>
    obtain ⟨xs, fits, read⟩ := ih (i + 1)
    have fl : geometry.field P all ⟨.memory, base, 0⟩ i =
        ⟨.memory, base + memberOffset all i, (all[i]?.map indirect).getD 0⟩ := rfl
    refine ⟨.leaf (mloadNat m.memory (base + memberOffset all i)) :: xs, ?_, ?_⟩
    · simp only [List.replicate_succ, Shrink.Layout.FitsFields, Shrink.Layout.Fits]
      exact ⟨⟨by decide, by decide, mloadNat_lt _ _⟩, fits⟩
    · simp only [List.replicate_succ, Shrink.Geometry.readFields, fl, read_word, read]
      rfl

/-- Words fit the word layout. -/
private theorem fits_words (b : ByteView) (base : Nat) (js : List Nat) :
    Shrink.Layout.FitsAll (.scalar 32) (js.map fun j => .leaf (mloadNat b (base + 32 * j))) := by
  induction js with
  | nil => simp only [List.map_nil, Shrink.Layout.FitsAll]
  | cons j js ih =>
    simp only [List.map_cons, Shrink.Layout.FitsAll, Shrink.Layout.Fits]
    exact ⟨⟨by decide, by decide, mloadNat_lt _ _⟩, ih⟩

/-- Every shape reads, in every memory, to a tree its layout admits. -/
private theorem read_fits (P : Shrink.Params) (s : MemoryShape) (addr : Nat) (m : Shrink.Phys)
    (fixed : ∀ n, s = .array false n → n < 2 ^ 256) :
    ∃ t, (Shrink.memoryShapeLayout s).Fits t ∧
      geometry.read P (Shrink.memoryShapeLayout s) ⟨.memory, addr, 0⟩ m = some t := by
  cases s with
  | bytes n =>
    refine ⟨.blob (readBytes m.memory (addr + 32) (mloadNat m.memory addr)), ?_, ?_⟩
    · simp only [Shrink.memoryShapeLayout, Shrink.Layout.Fits, readBytes, List.length_map,
        List.length_range]
      exact (mload _ _).isLt
    · simp only [Shrink.memoryShapeLayout, Shrink.Geometry.read]
      rfl
  | array dyn n =>
    cases dyn with
    | true =>
      have dl : geometry.data P ⟨.memory, addr, 0⟩ m = ⟨.memory, addr + 32, 0⟩ := rfl
      have ln : geometry.length P ⟨.memory, addr, 0⟩ m = mloadNat m.memory addr := rfl
      refine ⟨.node ((List.range' 0 (mloadNat m.memory addr)).map fun j =>
        .leaf (mloadNat m.memory (addr + 32 + 32 * j))), ?_, ?_⟩
      · simp only [Shrink.memoryShapeLayout, Shrink.Layout.Fits, List.length_map, List.length_range']
        exact ⟨(mload _ _).isLt, fits_words _ _ _⟩
      · simp only [Shrink.memoryShapeLayout, Shrink.Geometry.read, dl, ln, read_words,
          Option.map_some]
    | false =>
      refine ⟨.node ((List.range' 0 n).map fun j => .leaf (mloadNat m.memory (addr + 32 * j))),
        ?_, ?_⟩
      · simp only [Shrink.memoryShapeLayout, Shrink.Layout.Fits, List.length_map, List.length_range']
        exact ⟨trivial, fixed n rfl, fits_words _ _ _⟩
      · simp only [Shrink.memoryShapeLayout, Shrink.Geometry.read, read_words, Option.map_some]
  | strct n =>
    obtain ⟨xs, fits, read⟩ := read_fields P (List.replicate n (.scalar 32)) addr n 0 m
    refine ⟨.node xs, ?_, ?_⟩
    · simpa only [Shrink.memoryShapeLayout, Shrink.Layout.Fits] using fits
    · simp only [Shrink.memoryShapeLayout, Shrink.Geometry.read, read, Option.map_some]

/-- The members of a struct of words lie in the struct. -/
private theorem field_cells (P : Shrink.Params) (n base k i : Nat) (m : Shrink.Phys) (c : Shrink.Cell)
    (le : i + k ≤ n)
    (inside : geometry.fieldCells P (List.replicate n (.scalar 32)) ⟨.memory, base, 0⟩
      (List.replicate k (.scalar 32)) i m c) : Shrink.objectCells base (n * 32) c := by
  induction k generalizing i with
  | zero => simp only [List.replicate_zero, Shrink.Geometry.fieldCells] at inside
  | succ k ih =>
    have sc : geometry.cells P (.scalar 32)
        (geometry.field P (List.replicate n (.scalar 32)) ⟨.memory, base, 0⟩ i) m c =
        Shrink.objectCells (base + memberOffset (List.replicate n (.scalar 32)) i) 32 c := by
      simp only [Shrink.Geometry.cells]
      rfl
    simp only [List.replicate_succ, Shrink.Geometry.fieldCells, sc, member_offset n i (by omega)]
      at inside
    rcases inside with inside | inside
    · cases c <;> simp only [Shrink.objectCells] at inside ⊢ <;> omega
    · exact ih (i + 1) (by omega) inside

/-- The footprint of a shape lies in its object, once a dynamic shape's
stored length word is the shape's length. -/
private theorem cells_within (P : Shrink.Params) (s : MemoryShape) (addr : Nat) (m : Shrink.Phys)
    (bytesHeader : ∀ n, s = .bytes n → mloadNat m.memory addr = n)
    (arrayHeader : ∀ n, s = .array true n → mloadNat m.memory addr = n) (c : Shrink.Cell)
    (inside : geometry.cells P (Shrink.memoryShapeLayout s) ⟨.memory, addr, 0⟩ m c) :
    Shrink.objectCells addr s.size c := by
  have lc : geometry.lengthCells P ⟨.memory, addr, 0⟩ c = Shrink.objectCells addr 32 c := rfl
  cases s with
  | bytes n =>
    have bc : geometry.blobCells P ⟨.memory, addr, 0⟩ m c =
        Shrink.objectCells (addr + 32) (mloadNat m.memory addr) c := rfl
    simp only [Shrink.memoryShapeLayout, Shrink.Geometry.cells, lc, bc, bytesHeader n rfl] at inside
    cases c <;> simp only [Shrink.objectCells, or_self, MemoryShape.size] at inside ⊢ <;> omega
  | array dyn n =>
    cases dyn with
    | true =>
      have dl : geometry.data P ⟨.memory, addr, 0⟩ m = ⟨.memory, addr + 32, 0⟩ := rfl
      have ln : geometry.length P ⟨.memory, addr, 0⟩ m = n := arrayHeader n rfl
      simp only [Shrink.memoryShapeLayout, Shrink.Geometry.cells, lc, dl, ln, elem_cells] at inside
      cases c <;> simp only [Shrink.objectCells, or_self, MemoryShape.size, if_true] at inside ⊢ <;>
        omega
    | false =>
      simp only [Shrink.memoryShapeLayout, Shrink.Geometry.cells, elem_cells] at inside
      cases c <;> simp only [Shrink.objectCells, MemoryShape.size] at inside ⊢ <;> omega
  | strct n =>
    simp only [Shrink.memoryShapeLayout, Shrink.Geometry.cells] at inside
    exact field_cells P n addr n 0 m c (by omega) inside

/-- The enumerated image holds the length word of every live dynamic object. -/
private theorem header {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (r image : ByteView) (view : enumeratedMemoryView p r = .ok image) (a : Nat)
    (live : (h.cells a).isSome) :
    (∀ n, p.shape a = .bytes n → mloadNat image (p.address a) = n) ∧
    (∀ n, p.shape a = .array true n → mloadNat image (p.address a) = n) := by
  unfold enumeratedMemoryView at view
  cases prepared : prepareHeapInventory p with
  | error bad => rw [prepared] at view; cases view
  | ok es =>
    rw [prepared] at view
    cases view
    obtain ⟨_, cover, nodup⟩ := prepareHeapInventory_ok p es prepared
    obtain ⟨⟨τ, d⟩, found⟩ := Option.isSome_iff_exists.mp live
    have ends := p.ends a live
    have free := p.free.isLt
    have typed := p.typed a τ d found
    have word := fun w (ow : ObjectWord p.address d 0 w) =>
      congrArg Fin.val (encodeMixedHeap_source_word p es nodup cover r a τ d found 0 w ow)
    generalize p.shape a = s at typed ends
    cases typed with
    | bytes bs =>
      have bound : bs.length < 2 ^ 256 := by simp only [MemoryShape.size] at ends; omega
      refine ⟨fun n e => ?_, fun n e => by cases e⟩
      cases e
      exact word ⟨bs.length, bound⟩ (.bytesLength bs bound)
    | string bs =>
      have bound : bs.length < 2 ^ 256 := by simp only [MemoryShape.size] at ends; omega
      refine ⟨fun n e => ?_, fun n e => by cases e⟩
      cases e
      exact word ⟨bs.length, bound⟩ (.stringLength bs bound)
    | @array _ _ k len hl xs =>
      refine ⟨fun n e => (by cases e), fun n e => ?_⟩
      cases k with
      | some k => simp only [Option.isNone_some] at e; cases e
      | none =>
        cases e
        have bound : len < 2 ^ 256 := by
          simp only [MemoryShape.size, Option.isNone_none, if_true] at ends; omega
        exact word ⟨len, bound⟩ (.arrayLength len bound hl xs)
    | strct fs => exact ⟨fun n e => (by cases e), fun n e => (by cases e)⟩

/-- **`enumeratedMemoryView`**: every placed live object is readable at its
address with its shape's layout, and `Placement.separate` is footprint
disjointness. -/
theorem enumerated (P : Shrink.Params) {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (r image : ByteView) (m : Shrink.Phys) (view : enumeratedMemoryView p r = .ok image) :
    (∀ a, (h.cells a).isSome → ∃ t, (Shrink.memoryShapeLayout (p.shape a)).Fits t ∧
      geometry.read P (Shrink.memoryShapeLayout (p.shape a)) ⟨.memory, p.address a, 0⟩
        (m.withMemory image) = some t) ∧
    (∀ a b, (h.cells a).isSome → (h.cells b).isSome → a ≠ b →
      Shrink.Apart (geometry.cells P (Shrink.memoryShapeLayout (p.shape a)) ⟨.memory, p.address a, 0⟩
          (m.withMemory image))
        (geometry.cells P (Shrink.memoryShapeLayout (p.shape b)) ⟨.memory, p.address b, 0⟩
          (m.withMemory image))) := by
  refine ⟨fun a live => read_fits P _ _ _ (fun n e => ?_), fun a b la lb ne c both => ?_⟩
  · have ends := p.ends a live
    have free := p.free.isLt
    rw [e] at ends
    simp only [MemoryShape.size] at ends
    omega
  · have ha := header p r image view a la
    have hb := header p r image view b lb
    have ca := cells_within P _ _ (m.withMemory image) ha.1 ha.2 c both.1
    have cb := cells_within P _ _ (m.withMemory image) hb.1 hb.2 c both.2
    cases c with
    | slot => exact ca
    | mem x =>
      have apart := p.separate a b la lb ne
      simp only [Shrink.objectCells] at ca cb
      omega

end Solidity.Yul.Layout.Instances
