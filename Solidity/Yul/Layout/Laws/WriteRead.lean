import Solidity.Yul.Layout.Laws.Read
import Solidity.Yul.Layout.Laws.Write

/-!
# Read after write of the layout geometry

`write_read` is the statement of `Shrink.LayoutView.Laws.write_read` for
`geometry`: a fitting tree whose write succeeds and whose written footprint
is separated is read back. It mentions no allocator.

`write_read` is a mutual recursion over the written tree. A leaf codec reads
back what it wrote. For a sequence, element `i` reads back after its own write
(the recursion), and the later writes keep it: they change only their own
written footprints (`frame`), the read of element `i` depends only on its
read footprint (`local_read`), that footprint lies inside its written
footprint (`cells_sub`), and `Separated` keeps the two apart. The length word
of a dynamic array survives its element writes the same way (`length_agree`).
`Separated` and the footprints are taken in the final state; `written_indep`
moves them to the state after the element's own write, because the footprint
of a successful nested write does not depend on the state. `written_indep`
and `cells_sub` are recursions of the same shape.

The helpers `bind_some`, `writeLength_mem`, `writeBlob_mem`, `data_congr`,
`elem_nested`, `field_nested`, `writeElems_frame` and `writeFields_frame`
restate private lemmas of `Laws/Write.lean`, which this module cannot reach.
-/
namespace Solidity.Yul.Layout

open Solidity.Goals
open Solidity.Yul.Views

/-! ## Leaves -/

private theorem bind_some {α β : Type} {a : Option α} {f : α → Option β} {b : β}
    (h : (a >>= f) = some b) : ∃ x, a = some x ∧ f x = some b := by
  cases a with
  | none => cases h
  | some x => exact ⟨x, rfl, h⟩

private theorem slots_withSlots (m : Shrink.Phys) {r : Shrink.Region} (hr : r ≠ .memory)
    (s : SlotView) : (m.withSlots r s).slots r = s := by
  cases r with
  | memory => exact absurd rfl hr
  | storage => rfl
  | transient => rfl

/-- A stored memory word below `2 ^ 256` loads as itself. -/
private theorem mloadNat_mstore (b : ByteView) (a n : Nat) (hn : n < 2 ^ 256) :
    mloadNat (mstore b a (Shrink.toWord n)) a = n :=
  (congrArg Fin.val (mload_mstore b a (Shrink.toWord n))).trans (Nat.mod_eq_of_lt hn)

/-- A scalar reads back what a fitting write stored. -/
private theorem scalar_write_read (P : Shrink.Params) (w : Nat) (l : Shrink.Loc) (v : Nat)
    (m m' : Shrink.Phys) (hf : 0 < w ∧ w ≤ 32 ∧ v < 256 ^ w)
    (h : geometry.writeScalar P w l v m = some m') : geometry.scalar P w l m' = some v := by
  by_cases hr : l.region = .memory
  · simp only [geometry, if_pos hr, Option.some.injEq] at h ⊢
    subst h
    have hv : v < 2 ^ 256 := Nat.lt_of_lt_of_le hf.2.2
      (Nat.pow_le_pow_right (by decide : 0 < 256) hf.2.1)
    have hl : mloadNat (m.withMemory (mstore m.memory l.word (Shrink.toWord v))).memory l.word
        = v := mloadNat_mstore m.memory l.word v hv
    rw [hl, Nat.mod_eq_of_lt hf.2.2, ite_self]
  · simp only [geometry, if_neg hr] at h ⊢
    cases hfd : slotField w l.offset with
    | none => rw [hfd] at h; cases h
    | some f =>
      rw [hfd] at h
      simp only [Option.bind_some] at h
      split at h
      · cases h
        simp only [Option.map_some, slots_withSlots m hr, patchScalarSlot_find]
      · cases h

private theorem writeLength_mem {P : Shrink.Params} {l : Shrink.Loc} {n : Nat}
    {m m' : Shrink.Phys} (h : geometry.writeLength P l n m = some m')
    (hr : l.region = .memory) : l.offset = 0 := by
  simp only [geometry, if_pos hr] at h
  split at h
  · assumption
  · cases h

/-- The length word holds the written length. -/
private theorem writeLength_length {P : Shrink.Params} {l : Shrink.Loc} {n : Nat}
    {m m' : Shrink.Phys} (h : geometry.writeLength P l n m = some m') (hn : n < 2 ^ 256) :
    geometry.length P l m' = n := by
  by_cases hr : l.region = .memory
  · have ho := writeLength_mem h hr
    simp only [geometry, if_pos hr, if_pos ho, Option.some.injEq] at h ⊢
    subst h
    exact mloadNat_mstore m.memory l.word n hn
  · simp only [geometry, if_neg hr, Option.some.injEq] at h ⊢
    subst h
    rw [slots_withSlots m hr, find_saveSlot]
    exact Nat.mod_eq_of_lt hn

/-- States that agree on the length footprint hold the same length. -/
private theorem length_agree (P : Shrink.Params) (l : Shrink.Loc) (m m' : Shrink.Phys)
    (h : ∀ c, geometry.lengthCells P l c → m.byte c = m'.byte c) :
    geometry.length P l m = geometry.length P l m' := by
  by_cases hr : l.region = .memory
  · simp only [geometry, if_pos hr] at h ⊢
    refine readBE_congr _ _ _ _ fun i hi => UInt8.toNat_inj.mp (h (.mem (l.word + i)) ?_)
    refine ⟨Nat.le_add_right _ _, ?_⟩
    split <;> omega
  · have e := local_read P (.scalar 32) ⟨l.region, l.word, 0⟩ m m' fun c hc => h c (by
      simp only [Shrink.Geometry.cells, geometry, if_neg hr, slotField] at hc ⊢
      obtain ⟨b, hb, _, hlt⟩ := hc
      exact ⟨b, hb, (Nat.zero_add 32 ▸ hlt : b < 32)⟩)
    simp only [Shrink.Geometry.read, geometry, if_neg hr, slotField, Nat.zero_lt_succ,
      Nat.zero_add, Nat.le_refl, and_self, dite_true, Option.map_some, Option.some.injEq,
      Shrink.Tree.leaf.injEq, Field.findWord, Field.find, Field.base, Field.modulus, Nat.pow_zero,
      Nat.div_one] at e
    have lt : ∀ x : Roadmap.Word, x.val % 256 ^ 32 = x.val := fun x => Nat.mod_eq_of_lt x.isLt
    rw [lt, lt] at e
    simp only [geometry, if_neg hr]
    exact e

/-! ## Slot `bytes` -/

/-- Slot data bytes `i, …` keep every field they do not reach. -/
private theorem writeSlotBytes_keep (base : Nat) (wd : Roadmap.Word) (g : Field) :
    ∀ (bs : List UInt8) (i : Nat) (s : SlotView),
      (∀ k, i ≤ k → k < i + bs.length → wd = Shrink.toWord (base + k / 32) →
        31 - k % 32 + 1 ≤ g.offset ∨ g.offset + g.width ≤ 31 - k % 32) →
      g.findWord (writeSlotBytes base bs i s wd) = g.findWord (s wd)
  | [], _, _, _ => rfl
  | b :: bs, i, s, h => by
    rw [writeSlotBytes, writeSlotBytes_keep base wd g bs (i + 1) _ fun k h₁ h₂ =>
      h k (by omega) (by simp only [List.length_cons]; omega)]
    refine patchScalarSlot_other_field _ _ _ _ _ _ ?_
    by_cases hw : Shrink.toWord (base + i / 32) = wd
    · exact .inr (h i (Nat.le_refl i) (by simp only [List.length_cons]; omega) hw.symm)
    · exact .inl hw

/-- Byte `k` of written slot data, when no other written byte shares its slot
by wrapping. -/
private theorem writeSlotBytes_get (base : Nat) :
    ∀ (bs : List UInt8) (i : Nat) (s : SlotView) (k : Nat) (b : UInt8), i ≤ k →
      bs[k - i]? = some b →
      (∀ j, i ≤ j → j < i + bs.length →
        Shrink.toWord (base + k / 32) = Shrink.toWord (base + j / 32) → j / 32 = k / 32) →
      (writeSlotBytes base bs i s (Shrink.toWord (base + k / 32))).val / 256 ^ (31 - k % 32) % 256
        = b.toNat
  | [], _, _, _, _, _, hb, _ => by cases hb
  | x :: bs, i, s, k, b, hi, hb, inj => by
    rw [writeSlotBytes]
    by_cases hk : k = i
    · subst hk
      rw [Nat.sub_self, List.getElem?_cons_zero] at hb
      cases hb
      have keep := writeSlotBytes_keep base (Shrink.toWord (base + k / 32))
        ⟨31 - k % 32, 1, by decide, by omega⟩ bs (k + 1)
        (patchScalarSlot s (Shrink.toWord (base + k / 32)) ⟨31 - k % 32, 1, by decide, by omega⟩
          ⟨x.toNat, x.toNat_lt⟩) fun j h₁ h₂ hw => by
        have same := inj j (by omega) (by simp only [List.length_cons]; omega) hw
        show 31 - j % 32 + 1 ≤ 31 - k % 32 ∨ 31 - k % 32 + 1 ≤ 31 - j % 32
        omega
      exact congrArg Fin.val (keep.trans (patchScalarSlot_find _ _ _ _))
    · have step : k - i = k - (i + 1) + 1 := by omega
      rw [step, List.getElem?_cons_succ] at hb
      exact writeSlotBytes_get base bs (i + 1) _ k b (by omega) hb fun j h₁ h₂ =>
        inj j (by omega) (by simp only [List.length_cons]; omega)

private theorem writeBlob_mem {P : Shrink.Params} {l : Shrink.Loc} {bs : List UInt8}
    {m m' : Shrink.Phys} (h : geometry.writeBlob P l bs m = some m')
    (hr : l.region = .memory) : l.offset = 0 := by
  simp only [geometry, if_pos hr] at h
  split at h
  · split at h
    · assumption
    · cases h
  · cases h

/-- A `bytes` value reads back; in slots, when its head slot is apart from its data. -/
private theorem blob_write_read (P : Shrink.Params) (l : Shrink.Loc) (bs : List UInt8)
    (m m' : Shrink.Phys) (h : geometry.writeBlob P l bs m = some m')
    (hs : Shrink.Apart (geometry.lengthCells P l) (geometry.blobCells P l m')) :
    geometry.blob P l m' = some bs := by
  by_cases hl : bs.length < 2 ^ 256
  · by_cases hr : l.region = .memory
    · have ho := writeBlob_mem h hr
      simp only [geometry, dataLoc, dif_pos hl, if_pos hr, if_pos ho, Option.some.injEq] at h ⊢
      subst h
      have hn : mloadNat (m.withMemory (bytesObjectView bs hl m.memory l.word)).memory l.word =
          bs.length := congrArg Fin.val (bytesObject_header bs hl m.memory l.word)
      rw [hn]
      exact bytesObject_payload_list bs hl m.memory l.word
    · simp only [geometry, dataLoc, dif_pos hl, if_neg hr, Option.some.injEq] at h hs ⊢
      subst h
      rw [slots_withSlots m hr, find_saveSlot]
      apply List.ext_getElem
      · simp only [readSlotBytes, List.length_map, List.length_range]
      · intro i _ hi
        simp only [readSlotBytes, List.getElem_map, List.getElem_range]
        have small : i / 32 < 2 ^ 251 := by omega
        rw [find_saveSlot_other _ _ _ _ fun he => hs (.slot l.region (Shrink.toWord l.word) 0)
          ⟨⟨0, rfl, by decide⟩, ⟨i / 32, 0, small, by decide, by rw [he]⟩⟩]
        apply UInt8.toNat_inj.mp
        rw [UInt8.toNat_ofNat']
        exact writeSlotBytes_get _ bs 0 _ i bs[i] (Nat.zero_le i)
          (by rw [Nat.sub_zero]; exact List.getElem?_eq_getElem hi) fun j _ hj he => by
          have wrap := congrArg Fin.val he
          simp only [Shrink.toWord] at wrap
          omega
  · simp only [geometry, dif_neg hl] at h
    cases h

/-! ## Placements -/

private theorem data_congr {P : Shrink.Params} {l : Shrink.Loc} (m m' : Shrink.Phys)
    (h : l.region = .memory → l.offset = 0) : geometry.data P l m = geometry.data P l m' := by
  show dataLoc P l m = dataLoc P l m'
  by_cases hr : l.region = .memory
  · simp only [dataLoc, if_pos hr, if_pos (h hr)]
  · simp only [dataLoc, if_neg hr]

/-- A memory element carries the offset mark of its layout (`indirect`). -/
private theorem elem_nested (P : Shrink.Params) (e : Shrink.Layout) (l : Shrink.Loc) (i : Nat)
    (h : (geometry.elem P e l i).region = .memory) :
    (geometry.elem P e l i).offset = indirect e := by
  by_cases hr : l.region = .memory
  · simp only [geometry, if_pos hr]
  · simp only [geometry, if_neg hr] at h
    cases e <;> exact absurd h hr

/-- A memory member carries the offset mark of its layout. -/
private theorem field_nested (P : Shrink.Params) (fs : List Shrink.Layout) (l : Shrink.Loc)
    (i : Nat) (f : Shrink.Layout) (hf : fs[i]? = some f)
    (h : (geometry.field P fs l i).region = .memory) :
    (geometry.field P fs l i).offset = indirect f := by
  by_cases hr : l.region = .memory
  · simp only [geometry, if_pos hr, hf, Option.map_some, Option.getD_some]
  · simp only [geometry, if_neg hr] at h
    exact absurd h hr

/-! ## Footprint and separation of a successful nested write: state-independent -/

mutual
private theorem written_indep (P : Shrink.Params) :
    ∀ (t : Shrink.Tree) (L : Shrink.Layout) (l : Shrink.Loc) (m₀ m₀' : Shrink.Phys),
      geometry.write P L l t m₀ = some m₀' →
      (l.region = .memory → l.offset = indirect L) →
      ∀ m₁ m₂ : Shrink.Phys, geometry.cellsT P L l t m₁ = geometry.cellsT P L l t m₂ ∧
        geometry.Separated P L l t m₁ = geometry.Separated P L l t m₂
  | .leaf v, L, l, m₀, m₀', h, _, m₁, m₂ => by
    cases L with
    | scalar w =>
      exact ⟨funext fun c => by rw [Shrink.Geometry.cellsT, Shrink.Geometry.cellsT],
        by simp only [Shrink.Geometry.Separated]⟩
    | _ => simp only [Shrink.Geometry.write, reduceCtorEq] at h
  | .keyed f, L, l, m₀, m₀', h, _, m₁, m₂ => by
    cases L <;> simp only [Shrink.Geometry.write, reduceCtorEq] at h
  | .blob bs, L, l, m₀, m₀', h, hn, m₁, m₂ => by
    cases L with
    | bytes =>
      rw [Shrink.Geometry.write] at h
      have hr : l.region ≠ .memory := fun hr =>
        absurd ((hn hr).symm.trans (writeBlob_mem h hr)) (Nat.succ_ne_zero 0)
      have hb : geometry.blobCells P l m₁ = geometry.blobCells P l m₂ := by
        funext c
        simp only [geometry, dataLoc, if_neg hr]
      exact ⟨funext fun c => by rw [Shrink.Geometry.cellsT, Shrink.Geometry.cellsT, hb],
        by rw [Shrink.Geometry.Separated, Shrink.Geometry.Separated, hb]⟩
    | _ => simp only [Shrink.Geometry.write, reduceCtorEq] at h
  | .node xs, L, l, m₀, m₀', h, hn, m₁, m₂ => by
    cases L with
    | fixedArray e n =>
      rw [Shrink.Geometry.write] at h
      split at h
      · obtain ⟨hc, hs⟩ := writtenElems_indep P xs e l 0 m₀ m₀' h m₁ m₂
        exact ⟨funext fun c => by rw [Shrink.Geometry.cellsT, Shrink.Geometry.cellsT, hc],
          by rw [Shrink.Geometry.Separated, Shrink.Geometry.Separated, hs]⟩
      · cases h
    | dynArray e =>
      rw [Shrink.Geometry.write] at h
      split at h
      · obtain ⟨m, hw, he⟩ := bind_some h
        have hr : l.region = .memory → l.offset = 0 := fun hr =>
          absurd ((hn hr).symm.trans (writeLength_mem hw hr)) (Nat.succ_ne_zero 0)
        obtain ⟨hc, hs⟩ := writtenElems_indep P xs e _ 0 m m₀' he m₁ m₂
        exact ⟨funext fun c => by
            rw [Shrink.Geometry.cellsT, Shrink.Geometry.cellsT, data_congr m₁ m hr,
              data_congr m₂ m hr, hc],
          by rw [Shrink.Geometry.Separated, Shrink.Geometry.Separated, data_congr m₁ m hr,
            data_congr m₂ m hr, hc, hs]⟩
      · cases h
    | struct fs =>
      rw [Shrink.Geometry.write] at h
      obtain ⟨hc, hs⟩ := writtenFields_indep P xs fs fs l 0 m₀ m₀' h
        (fun j => by rw [Nat.zero_add]) m₁ m₂
      exact ⟨funext fun c => by rw [Shrink.Geometry.cellsT, Shrink.Geometry.cellsT, hc],
        by rw [Shrink.Geometry.Separated, Shrink.Geometry.Separated, hs]⟩
    | _ => simp only [Shrink.Geometry.write, reduceCtorEq] at h
private theorem writtenElems_indep (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (e : Shrink.Layout) (l : Shrink.Loc) (i : Nat)
      (m₀ m₀' : Shrink.Phys), geometry.writeElems P e l xs i m₀ = some m₀' →
      ∀ m₁ m₂ : Shrink.Phys,
        geometry.elemCellsT P e l xs i m₁ = geometry.elemCellsT P e l xs i m₂ ∧
        geometry.ElemsSeparated P e l xs i m₁ = geometry.ElemsSeparated P e l xs i m₂
  | [], _, _, _, _, _, _, _, _ =>
    ⟨funext fun c => by rw [Shrink.Geometry.elemCellsT, Shrink.Geometry.elemCellsT],
      by rw [Shrink.Geometry.ElemsSeparated, Shrink.Geometry.ElemsSeparated]⟩
  | x :: xs, e, l, i, m₀, m₀', h, m₁, m₂ => by
    rw [Shrink.Geometry.writeElems] at h
    obtain ⟨m, hx, hxs⟩ := bind_some h
    obtain ⟨c₁, s₁⟩ := written_indep P x e _ m₀ m hx (elem_nested P e l i) m₁ m₂
    obtain ⟨c₂, s₂⟩ := writtenElems_indep P xs e l (i + 1) m m₀' hxs m₁ m₂
    exact ⟨funext fun c => by
        rw [Shrink.Geometry.elemCellsT, Shrink.Geometry.elemCellsT, c₁, c₂],
      by rw [Shrink.Geometry.ElemsSeparated, Shrink.Geometry.ElemsSeparated, c₁, c₂, s₁,
        s₂]⟩
private theorem writtenFields_indep (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (fs all : List Shrink.Layout) (l : Shrink.Loc) (i : Nat)
      (m₀ m₀' : Shrink.Phys), geometry.writeFields P all l fs xs i m₀ = some m₀' →
      (∀ j, all[i + j]? = fs[j]?) →
      ∀ m₁ m₂ : Shrink.Phys,
        geometry.fieldCellsT P all l fs xs i m₁ = geometry.fieldCellsT P all l fs xs i m₂ ∧
        geometry.FieldsSeparated P all l fs xs i m₁ =
          geometry.FieldsSeparated P all l fs xs i m₂
  | [], fs, _, _, _, _, _, _, _, _, _ => by
    cases fs <;>
      exact ⟨funext fun c => by simp only [Shrink.Geometry.fieldCellsT],
        by simp only [Shrink.Geometry.FieldsSeparated]⟩
  | _ :: _, [], _, _, _, _, _, _, _, _, _ =>
    ⟨funext fun c => by simp only [Shrink.Geometry.fieldCellsT],
      by simp only [Shrink.Geometry.FieldsSeparated]⟩
  | x :: xs, f :: fs, all, l, i, m₀, m₀', h, hi, m₁, m₂ => by
    rw [Shrink.Geometry.writeFields] at h
    obtain ⟨m, hx, hxs⟩ := bind_some h
    obtain ⟨c₁, s₁⟩ :=
      written_indep P x f _ m₀ m hx (field_nested P all l i f (hi 0)) m₁ m₂
    obtain ⟨c₂, s₂⟩ := writtenFields_indep P xs fs all l (i + 1) m m₀' hxs
      (fun j => by rw [show i + 1 + j = i + (j + 1) by omega]; exact hi (j + 1)) m₁ m₂
    exact ⟨funext fun c => by
        rw [Shrink.Geometry.fieldCellsT, Shrink.Geometry.fieldCellsT, c₁, c₂],
      by rw [Shrink.Geometry.FieldsSeparated, Shrink.Geometry.FieldsSeparated, c₁, c₂, s₁,
        s₂]⟩
end

/-! ## Later sibling writes change their own footprints only -/

private theorem writeElems_frame (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (e : Shrink.Layout) (l : Shrink.Loc) (i : Nat)
      (m m' : Shrink.Phys), geometry.writeElems P e l xs i m = some m' →
      ∀ c, ¬ geometry.elemCellsT P e l xs i m' c → m'.byte c = m.byte c
  | [], _, _, _, m, m', h, _, _ => by
    rw [Shrink.Geometry.writeElems] at h
    cases h
    rfl
  | x :: xs, e, l, i, m, m', h, c, hc => by
    rw [Shrink.Geometry.writeElems] at h
    obtain ⟨m₁, hx, hxs⟩ := bind_some h
    rw [Shrink.Geometry.elemCellsT] at hc
    exact (writeElems_frame P xs e l (i + 1) m₁ m' hxs c fun hh => hc (.inr hh)).trans
      (frame P e _ x m m₁ hx c fun hh => hc (.inl (Eq.mp
        (congrFun (written_indep P x e _ m m₁ hx (elem_nested P e l i) m₁ m').1 c) hh)))

private theorem writeFields_frame (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (fs all : List Shrink.Layout) (l : Shrink.Loc) (i : Nat)
      (m m' : Shrink.Phys), geometry.writeFields P all l fs xs i m = some m' →
      (∀ j, all[i + j]? = fs[j]?) →
      ∀ c, ¬ geometry.fieldCellsT P all l fs xs i m' c → m'.byte c = m.byte c
  | [], fs, _, _, _, m, m', h, _, _, _ => by
    cases fs with
    | nil =>
      rw [Shrink.Geometry.writeFields] at h
      cases h
      rfl
    | cons => simp only [Shrink.Geometry.writeFields, reduceCtorEq] at h
  | _ :: _, [], _, _, _, _, _, h, _, _, _ => by
    simp only [Shrink.Geometry.writeFields, reduceCtorEq] at h
  | x :: xs, f :: fs, all, l, i, m, m', h, hi, c, hc => by
    rw [Shrink.Geometry.writeFields] at h
    obtain ⟨m₁, hx, hxs⟩ := bind_some h
    rw [Shrink.Geometry.fieldCellsT] at hc
    exact (writeFields_frame P xs fs all l (i + 1) m₁ m' hxs
        (fun j => by rw [show i + 1 + j = i + (j + 1) by omega]; exact hi (j + 1)) c
        fun hh => hc (.inr hh)).trans
      (frame P f _ x m m₁ hx c fun hh => hc (.inl (Eq.mp
        (congrFun (written_indep P x f _ m m₁ hx (field_nested P all l i f (hi 0)) m₁ m').1 c)
        hh)))

/-! ## The read footprint of a written tree lies in its written footprint -/

private theorem map_node {o : Option (List Shrink.Tree)} {xs : List Shrink.Tree}
    (h : o.map Shrink.Tree.node = some (.node xs)) : o = some xs := by
  cases o with
  | none => cases h
  | some ys => cases h; rfl

private theorem readElems_cons {P : Shrink.Params} {e : Shrink.Layout} {l : Shrink.Loc}
    {n i : Nat} {m : Shrink.Phys} {ys : List Shrink.Tree}
    (h : geometry.readElems P e l (n + 1) i m = some ys) :
    ∃ x xs, ys = x :: xs ∧ geometry.read P e (geometry.elem P e l i) m = some x ∧
      geometry.readElems P e l n (i + 1) m = some xs := by
  rw [Shrink.Geometry.readElems] at h
  obtain ⟨x, hx, h⟩ := bind_some h
  obtain ⟨xs, hxs, h⟩ := bind_some h
  cases h
  exact ⟨x, xs, rfl, hx, hxs⟩

private theorem readFields_cons {P : Shrink.Params} {all fs : List Shrink.Layout}
    {f : Shrink.Layout} {l : Shrink.Loc} {i : Nat} {m : Shrink.Phys} {ys : List Shrink.Tree}
    (h : geometry.readFields P all l (f :: fs) i m = some ys) :
    ∃ x xs, ys = x :: xs ∧ geometry.read P f (geometry.field P all l i) m = some x ∧
      geometry.readFields P all l fs (i + 1) m = some xs := by
  rw [Shrink.Geometry.readFields] at h
  obtain ⟨x, hx, h⟩ := bind_some h
  obtain ⟨xs, hxs, h⟩ := bind_some h
  cases h
  exact ⟨x, xs, rfl, hx, hxs⟩

mutual
private theorem cells_sub (P : Shrink.Params) :
    ∀ (t : Shrink.Tree) (L : Shrink.Layout) (l : Shrink.Loc) (m₀ m₀' m : Shrink.Phys),
      geometry.write P L l t m₀ = some m₀' → geometry.read P L l m = some t →
      ∀ c, geometry.cells P L l m c → geometry.cellsT P L l t m c
  | .leaf v, L, l, m₀, m₀', m, h, _, c, hc => by
    cases L with
    | scalar w =>
      rw [Shrink.Geometry.cells] at hc
      rw [Shrink.Geometry.cellsT]
      exact hc
    | _ => simp only [Shrink.Geometry.write, reduceCtorEq] at h
  | .keyed f, L, l, m₀, m₀', m, h, _, c, hc => by
    cases L <;> simp only [Shrink.Geometry.write, reduceCtorEq] at h
  | .blob bs, L, l, m₀, m₀', m, h, _, c, hc => by
    cases L with
    | bytes =>
      rw [Shrink.Geometry.cells] at hc
      rw [Shrink.Geometry.cellsT]
      exact hc
    | _ => simp only [Shrink.Geometry.write, reduceCtorEq] at h
  | .node xs, L, l, m₀, m₀', m, h, hread, c, hc => by
    cases L with
    | fixedArray e n =>
      rw [Shrink.Geometry.write] at h
      split at h
      · rw [Shrink.Geometry.read] at hread
        rw [Shrink.Geometry.cells] at hc
        rw [Shrink.Geometry.cellsT]
        exact elemCells_sub P xs e l n 0 m₀ m₀' m h (map_node hread) c hc
      · cases h
    | dynArray e =>
      rw [Shrink.Geometry.write] at h
      split at h
      · obtain ⟨m₁, hw, he⟩ := bind_some h
        rw [data_congr m₁ m (writeLength_mem hw)] at he
        rw [Shrink.Geometry.read] at hread
        rw [Shrink.Geometry.cells] at hc
        rw [Shrink.Geometry.cellsT]
        exact hc.imp id (elemCells_sub P xs e _ _ 0 m₁ m₀' m he (map_node hread) c)
      · cases h
    | struct fs =>
      rw [Shrink.Geometry.write] at h
      rw [Shrink.Geometry.read] at hread
      rw [Shrink.Geometry.cells] at hc
      rw [Shrink.Geometry.cellsT]
      exact fieldCells_sub P xs fs fs l 0 m₀ m₀' m h (map_node hread) c hc
    | _ => simp only [Shrink.Geometry.write, reduceCtorEq] at h
private theorem elemCells_sub (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (e : Shrink.Layout) (l : Shrink.Loc) (n i : Nat)
      (m₀ m₀' m : Shrink.Phys), geometry.writeElems P e l xs i m₀ = some m₀' →
      geometry.readElems P e l n i m = some xs →
      ∀ c, geometry.elemCells P e l n i m c → geometry.elemCellsT P e l xs i m c
  | _, _, _, 0, _, _, _, _, _, _, _, hc => by
    rw [Shrink.Geometry.elemCells] at hc
    exact hc.elim
  | [], _, _, n + 1, _, _, _, _, _, hread, _, _ => by
    obtain ⟨_, _, e, _⟩ := readElems_cons hread
    cases e
  | x :: xs, e, l, n + 1, i, m₀, m₀', m, h, hread, c, hc => by
    rw [Shrink.Geometry.writeElems] at h
    obtain ⟨m₁, hx, hxs⟩ := bind_some h
    obtain ⟨_, _, same, rx, rxs⟩ := readElems_cons hread
    cases same
    rw [Shrink.Geometry.elemCells] at hc
    rw [Shrink.Geometry.elemCellsT]
    exact hc.imp (cells_sub P x e _ m₀ m₁ m hx rx c)
      (elemCells_sub P xs e l n (i + 1) m₁ m₀' m hxs rxs c)
private theorem fieldCells_sub (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (fs all : List Shrink.Layout) (l : Shrink.Loc) (i : Nat)
      (m₀ m₀' m : Shrink.Phys), geometry.writeFields P all l fs xs i m₀ = some m₀' →
      geometry.readFields P all l fs i m = some xs →
      ∀ c, geometry.fieldCells P all l fs i m c → geometry.fieldCellsT P all l fs xs i m c
  | [], fs, _, _, _, _, _, _, h, _, _, hc => by
    cases fs with
    | nil =>
      rw [Shrink.Geometry.fieldCells] at hc
      exact hc.elim
    | cons => simp only [Shrink.Geometry.writeFields, reduceCtorEq] at h
  | _ :: _, [], _, _, _, _, _, _, h, _, _, _ => by
    simp only [Shrink.Geometry.writeFields, reduceCtorEq] at h
  | x :: xs, f :: fs, all, l, i, m₀, m₀', m, h, hread, c, hc => by
    rw [Shrink.Geometry.writeFields] at h
    obtain ⟨m₁, hx, hxs⟩ := bind_some h
    obtain ⟨_, _, same, rx, rxs⟩ := readFields_cons hread
    cases same
    rw [Shrink.Geometry.fieldCells] at hc
    rw [Shrink.Geometry.fieldCellsT]
    exact hc.imp (cells_sub P x f _ m₀ m₁ m hx rx c)
      (fieldCells_sub P xs fs all l (i + 1) m₁ m₀' m hxs rxs c)
end

/-! ## Read after write -/

mutual
/-- **Read after write** (`LayoutView.Laws.write_read` for `geometry`): a
fitting tree whose write succeeds and whose written footprint is separated is
read back. -/
theorem write_read (P : Shrink.Params) :
    ∀ (L : Shrink.Layout) (l : Shrink.Loc) (t : Shrink.Tree) (m m' : Shrink.Phys),
      L.Fits t → geometry.write P L l t m = some m' → geometry.Separated P L l t m' →
      geometry.read P L l m' = some t
  | L, l, .leaf v, m, m', _, h, _ => by
    cases L with
    | scalar w =>
      rw [Shrink.Geometry.write] at h
      split at h
      · rename_i hw
        rw [Shrink.Geometry.read, scalar_write_read P w l v m m' hw h]
        rfl
      · cases h
    | _ => simp only [Shrink.Geometry.write, reduceCtorEq] at h
  | L, l, .keyed f, m, m', _, h, _ => by
    cases L <;> simp only [Shrink.Geometry.write, reduceCtorEq] at h
  | L, l, .blob bs, m, m', _, h, hs => by
    cases L with
    | bytes =>
      rw [Shrink.Geometry.write] at h
      rw [Shrink.Geometry.Separated] at hs
      rw [Shrink.Geometry.read, blob_write_read P l bs m m' h hs]
      rfl
    | _ => simp only [Shrink.Geometry.write, reduceCtorEq] at h
  | L, l, .node xs, m, m', hf, h, hs => by
    cases L with
    | fixedArray e n =>
      rw [Shrink.Layout.Fits] at hf
      obtain ⟨rfl, hn, hall⟩ := hf
      rw [Shrink.Geometry.write, if_pos ⟨rfl, hn⟩] at h
      rw [Shrink.Geometry.Separated] at hs
      rw [Shrink.Geometry.read, writeElems_read P xs e l 0 m m' hall h hs]
      rfl
    | dynArray e =>
      rw [Shrink.Layout.Fits] at hf
      rw [Shrink.Geometry.write, if_pos hf.1] at h
      obtain ⟨m₁, hw, he⟩ := bind_some h
      have hd := data_congr (P := P) m' m₁ (writeLength_mem hw)
      rw [Shrink.Geometry.Separated, hd] at hs
      have hlen : geometry.length P l m' = xs.length :=
        (length_agree P l m₁ m' fun c hc =>
          (writeElems_frame P xs e _ 0 m₁ m' he c fun hh => hs.2 c ⟨hc, hh⟩).symm).symm.trans
          (writeLength_length hw hf.1)
      rw [Shrink.Geometry.read, hd, hlen, writeElems_read P xs e _ 0 m₁ m' hf.2 he hs.1]
      rfl
    | struct fs =>
      rw [Shrink.Layout.Fits] at hf
      rw [Shrink.Geometry.write] at h
      rw [Shrink.Geometry.Separated] at hs
      rw [Shrink.Geometry.read,
        writeFields_read P xs fs fs l 0 m m' hf h hs fun j => by rw [Nat.zero_add]]
      rfl
    | _ => simp only [Shrink.Geometry.write, reduceCtorEq] at h
private theorem writeElems_read (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (e : Shrink.Layout) (l : Shrink.Loc) (i : Nat)
      (m m' : Shrink.Phys), e.FitsAll xs → geometry.writeElems P e l xs i m = some m' →
      geometry.ElemsSeparated P e l xs i m' →
      geometry.readElems P e l xs.length i m' = some xs
  | [], _, _, _, _, _, _, _, _ => by
    rw [List.length_nil, Shrink.Geometry.readElems]
  | x :: xs, e, l, i, m, m', hf, h, hs => by
    rw [Shrink.Layout.FitsAll] at hf
    rw [Shrink.Geometry.writeElems] at h
    obtain ⟨m₁, hx, hxs⟩ := bind_some h
    rw [Shrink.Geometry.ElemsSeparated] at hs
    obtain ⟨hc, hsep⟩ := written_indep P x e _ m m₁ hx (elem_nested P e l i) m₁ m'
    have rx := write_read P e _ x m m₁ hf.1 hx (hsep.mpr hs.1)
    have keep := local_read P e _ m₁ m' fun c hc' =>
      (writeElems_frame P xs e l (i + 1) m₁ m' hxs c fun hh =>
        hs.2.1 c ⟨Eq.mp (congrFun hc c) (cells_sub P x e _ m m₁ m₁ hx rx c hc'), hh⟩).symm
    rw [List.length_cons, Shrink.Geometry.readElems, ← keep, rx,
      writeElems_read P xs e l (i + 1) m₁ m' hf.2 hxs hs.2.2]
    rfl
private theorem writeFields_read (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (fs all : List Shrink.Layout) (l : Shrink.Loc) (i : Nat)
      (m m' : Shrink.Phys), Shrink.Layout.FitsFields fs xs →
      geometry.writeFields P all l fs xs i m = some m' →
      geometry.FieldsSeparated P all l fs xs i m' → (∀ j, all[i + j]? = fs[j]?) →
      geometry.readFields P all l fs i m' = some xs
  | [], fs, _, _, _, _, _, _, h, _, _ => by
    cases fs with
    | nil => rw [Shrink.Geometry.readFields]
    | cons => simp only [Shrink.Geometry.writeFields, reduceCtorEq] at h
  | _ :: _, [], _, _, _, _, _, _, h, _, _ => by
    simp only [Shrink.Geometry.writeFields, reduceCtorEq] at h
  | x :: xs, f :: fs, all, l, i, m, m', hf, h, hs, hi => by
    rw [Shrink.Layout.FitsFields] at hf
    rw [Shrink.Geometry.writeFields] at h
    obtain ⟨m₁, hx, hxs⟩ := bind_some h
    rw [Shrink.Geometry.FieldsSeparated] at hs
    have next : ∀ j, all[i + 1 + j]? = fs[j]? := fun j => by
      rw [show i + 1 + j = i + (j + 1) by omega]
      exact hi (j + 1)
    obtain ⟨hc, hsep⟩ :=
      written_indep P x f _ m m₁ hx (field_nested P all l i f (hi 0)) m₁ m'
    have rx := write_read P f _ x m m₁ hf.1 hx (hsep.mpr hs.1)
    have keep := local_read P f _ m₁ m' fun c hc' =>
      (writeFields_frame P xs fs all l (i + 1) m₁ m' hxs next c fun hh =>
        hs.2.1 c ⟨Eq.mp (congrFun hc c) (cells_sub P x f _ m m₁ m₁ hx rx c hc'), hh⟩).symm
    rw [Shrink.Geometry.readFields, ← keep, rx,
      writeFields_read P xs fs all l (i + 1) m₁ m' hf.2 hxs hs.2.2 next]
    rfl
end

end Solidity.Yul.Layout
