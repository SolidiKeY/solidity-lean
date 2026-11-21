import Solidity.Yul.Layout.Geometry

/-!
# Write laws of the layout geometry

`illTyped`, `write_total` and `frame`: the statements of the same-named
`Shrink.LayoutView.Laws` fields, for `geometry`. They mention no allocator.

`frame` takes the written footprint in the result state. A sibling write
could move a footprint that depends on the state, so the induction uses
`cellsT_indep`: the footprint of a successful nested write does not depend
on the state. In memory this holds because a nested dynamic array or `bytes`
sits behind an indirect header, where the geometry refuses the write.
In slots no footprint reads the state.
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

theorem write_bind_some_shared : type_of% (@bind_some) := @bind_some

/-- Bytes 32 and up of a word are zero. -/
private theorem word_byte_high (w : Roadmap.Word) {b : Nat} (hb : 32 ≤ b) :
    w.val / 256 ^ b = 0 :=
  Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (w.isLt : w.val < 256 ^ 32)
    (Nat.pow_le_pow_right (by decide : 0 < 256) hb))

/-- A packed update keeps every byte outside its field. -/
private theorem save_byte (f : Field) (w : Nat) (v : f.Value) (b : Nat)
    (h : ¬ (f.offset ≤ b ∧ b < f.offset + f.width)) :
    f.save w v / 256 ^ b % 256 = w / 256 ^ b % 256 := by
  by_cases hb : b < f.offset
  · have hd : 256 ^ (b + 1) ∣ f.base := Nat.pow_dvd_pow 256 hb
    have key : ∀ x, x / 256 ^ b % 256 = x % f.base % 256 ^ (b + 1) / 256 ^ b := fun x => by
      rw [Nat.mod_mod_of_dvd _ hd, Nat.pow_succ, Nat.mod_mul_right_div_self]
    rw [key, key, f.save_low]
  · have he : 256 ^ b = f.base * f.modulus * 256 ^ (b - (f.offset + f.width)) := by
      rw [Field.base, Field.modulus, ← Nat.pow_add, ← Nat.pow_add]
      exact congrArg _ (by omega)
    have key : ∀ x, x / 256 ^ b = x / f.base / f.modulus / 256 ^ (b - (f.offset + f.width)) :=
      fun x => by rw [he, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_assoc]
    rw [key, key, f.save_high]

/-- A memory write keeps the cells whose memory byte it keeps. -/
private theorem withMemory_byte (m : Shrink.Phys) (b : ByteView) (c : Shrink.Cell)
    (h : ∀ x, c = .mem x → b x = m.memory x) : (m.withMemory b).byte c = m.byte c := by
  cases c with
  | mem x => exact congrArg UInt8.toNat (h x rfl)
  | slot r wd k => cases r <;> rfl

/-- A slot write keeps the cells whose slot byte it keeps. -/
private theorem withSlots_byte (m : Shrink.Phys) (r : Shrink.Region) (s : SlotView)
    (c : Shrink.Cell) (hr : r ≠ .memory)
    (h : ∀ wd b, c = .slot r wd b →
      (s wd).val / 256 ^ b % 256 = (m.slots r wd).val / 256 ^ b % 256) :
    (m.withSlots r s).byte c = m.byte c := by
  cases c with
  | mem x => cases r <;> rfl
  | slot r' wd b =>
    cases r <;> cases r' <;> first | exact absurd rfl hr | exact h wd b rfl | rfl

private theorem writeScalar_frame (P : Shrink.Params) (w : Nat) (l : Shrink.Loc) (v : Nat)
    (m m' : Shrink.Phys) (c : Shrink.Cell) (h : geometry.writeScalar P w l v m = some m')
    (hc : ¬ geometry.scalarCells P w l c) : m'.byte c = m.byte c := by
  by_cases hr : l.region = .memory
  · simp only [geometry, if_pos hr, Option.some.injEq] at h hc
    subst h
    refine withMemory_byte _ _ _ fun x hx => mstore_outside _ _ _ _ ?_
    subst hx
    exact hc
  · simp only [geometry, if_neg hr] at h hc
    cases hf : slotField w l.offset with
    | none => rw [hf] at h; cases h
    | some f =>
      rw [hf] at h hc
      simp only [Option.bind_some] at h
      split at h
      · cases h
        refine withSlots_byte _ _ _ _ hr fun wd b hx => ?_
        subst hx
        by_cases hw : wd = Shrink.toWord l.word
        · subst hw
          rw [patchScalarSlot, find_saveSlot]
          exact save_byte f _ _ b fun hb => hc ⟨b, rfl, hb.1, hb.2⟩
        · rw [patchScalarSlot, find_saveSlot_other _ _ _ _ hw]
      · cases h

private theorem writeLength_mem {P : Shrink.Params} {l : Shrink.Loc} {n : Nat}
    {m m' : Shrink.Phys} (h : geometry.writeLength P l n m = some m')
    (hr : l.region = .memory) : l.offset = 0 := by
  simp only [geometry, if_pos hr] at h
  split at h
  · assumption
  · cases h

private theorem writeLength_frame (P : Shrink.Params) (l : Shrink.Loc) (n : Nat)
    (m m' : Shrink.Phys) (c : Shrink.Cell) (h : geometry.writeLength P l n m = some m')
    (hc : ¬ geometry.lengthCells P l c) : m'.byte c = m.byte c := by
  by_cases hr : l.region = .memory
  · have ho := writeLength_mem h hr
    simp only [geometry, if_pos hr, if_pos ho, Option.some.injEq] at h hc
    subst h
    refine withMemory_byte _ _ _ fun x hx => mstore_outside _ _ _ _ ?_
    subst hx
    exact hc
  · simp only [geometry, if_neg hr, Option.some.injEq] at h hc
    subst h
    refine withSlots_byte _ _ _ _ hr fun wd b hx => ?_
    subst hx
    by_cases hw : wd = Shrink.toWord l.word
    · subst hw
      have hb : 32 ≤ b := Nat.le_of_not_lt fun hb => hc ⟨b, rfl, hb⟩
      rw [word_byte_high _ hb, word_byte_high _ hb]
    · rw [find_saveSlot_other _ _ _ _ hw]

/-- Slot data bytes `i, …` leave every slot they do not reach. -/
private theorem writeSlotBytes_other (base : Nat) (wd : Roadmap.Word) :
    ∀ (bs : List UInt8) (i : Nat) (s : SlotView),
      (∀ k, i ≤ k → k < i + bs.length → wd ≠ Shrink.toWord (base + k / 32)) →
      writeSlotBytes base bs i s wd = s wd
  | [], _, _, _ => rfl
  | b :: bs, i, s, h => by
    rw [writeSlotBytes, writeSlotBytes_other base wd bs (i + 1) _ fun k h₁ h₂ =>
        h k (by omega) (by simp only [List.length_cons]; omega),
      patchScalarSlot, find_saveSlot_other _ _ _ _
        (h i (Nat.le_refl i) (by simp only [List.length_cons]; omega))]

private theorem writeBlob_mem {P : Shrink.Params} {l : Shrink.Loc} {bs : List UInt8}
    {m m' : Shrink.Phys} (h : geometry.writeBlob P l bs m = some m')
    (hr : l.region = .memory) : l.offset = 0 := by
  simp only [geometry, if_pos hr] at h
  split at h
  · split at h
    · assumption
    · cases h
  · cases h

private theorem writeBlob_frame (P : Shrink.Params) (l : Shrink.Loc) (bs : List UInt8)
    (m m' : Shrink.Phys) (c : Shrink.Cell) (h : geometry.writeBlob P l bs m = some m')
    (hc : ¬ (geometry.lengthCells P l c ∨ geometry.blobCells P l m' c)) :
    m'.byte c = m.byte c := by
  by_cases hl : bs.length < 2 ^ 256
  · by_cases hr : l.region = .memory
    · have ho := writeBlob_mem h hr
      simp only [geometry, dataLoc, dif_pos hl, if_pos hr, if_pos ho, Option.some.injEq] at h hc
      subst h
      have hn : mloadNat (bytesObjectView bs hl m.memory l.word) l.word = bs.length :=
        congrArg Fin.val (bytesObject_header bs hl m.memory l.word)
      refine withMemory_byte _ _ _ fun x hx => bytesObject_residual bs hl _ _ _ ?_
      subst hx
      refine Classical.byContradiction fun hx => hc ?_
      by_cases h32 : x < l.word + 32
      · exact .inl ⟨by omega, h32⟩
      · exact .inr ⟨by omega, by rw [Shrink.Phys.withMemory, hn]; omega⟩
    · simp only [geometry, dataLoc, dif_pos hl, if_neg hr, Option.some.injEq] at h hc
      subst h
      refine withSlots_byte _ _ _ _ hr fun wd b hx => ?_
      subst hx
      by_cases hb : b < 32
      · rw [find_saveSlot_other _ _ _ _ fun hw => hc (.inl ⟨b, by rw [hw], hb⟩),
          writeSlotBytes_other _ _ _ _ _ fun k _ hk hw =>
            hc (.inr ⟨k / 32, b, by omega, hb, by rw [hw]⟩)]
      · rw [word_byte_high _ (Nat.le_of_not_lt hb), word_byte_high _ (Nat.le_of_not_lt hb)]
  · simp only [geometry, dif_neg hl] at h
    cases h

/-! ## Placements -/

private theorem data_congr {P : Shrink.Params} {l : Shrink.Loc} (m m' : Shrink.Phys)
    (h : l.region = .memory → l.offset = 0) : geometry.data P l m = geometry.data P l m' := by
  show dataLoc P l m = dataLoc P l m'
  by_cases hr : l.region = .memory
  · simp only [dataLoc, if_pos hr, if_pos (h hr)]
  · simp only [dataLoc, if_neg hr]

private theorem data_slotted (P : Shrink.Params) (l : Shrink.Loc) (m : Shrink.Phys)
    (hr : l.region ≠ .memory) : (geometry.data P l m).region ≠ .memory := by
  show (dataLoc P l m).region ≠ .memory
  rw [dataLoc, if_neg hr]
  exact hr

private theorem elem_slotted (P : Shrink.Params) (e : Shrink.Layout) (l : Shrink.Loc) (i : Nat)
    (hr : l.region ≠ .memory) : (geometry.elem P e l i).region ≠ .memory := by
  simp only [geometry, if_neg hr]
  cases e <;> exact hr

/-- A memory element of a dynamic layout is an indirect header. -/
private theorem elem_nested (P : Shrink.Params) (e : Shrink.Layout) (l : Shrink.Loc) (i : Nat)
    (h : (geometry.elem P e l i).region = .memory) :
    (geometry.elem P e l i).offset = indirect e := by
  by_cases hr : l.region = .memory
  · simp only [geometry, if_pos hr]
  · exact absurd h (elem_slotted P e l i hr)

private theorem field_slotted (P : Shrink.Params) (fs : List Shrink.Layout) (l : Shrink.Loc)
    (i : Nat) (hr : l.region ≠ .memory) : (geometry.field P fs l i).region ≠ .memory := by
  simp only [geometry, if_neg hr]
  exact hr

private theorem field_nested (P : Shrink.Params) (fs : List Shrink.Layout) (l : Shrink.Loc)
    (i : Nat) (f : Shrink.Layout) (hf : fs[i]? = some f)
    (h : (geometry.field P fs l i).region = .memory) :
    (geometry.field P fs l i).offset = indirect f := by
  by_cases hr : l.region = .memory
  · simp only [geometry, if_pos hr, hf, Option.map_some, Option.getD_some]
  · exact absurd h (field_slotted P fs l i hr)

/-! ## The written footprint of a successful nested write is state-independent -/

mutual
private theorem cellsT_indep (P : Shrink.Params) :
    ∀ (t : Shrink.Tree) (L : Shrink.Layout) (l : Shrink.Loc) (m₀ m₀' : Shrink.Phys),
      geometry.write P L l t m₀ = some m₀' → (l.region = .memory → l.offset = indirect L) →
      ∀ (m₁ m₂ : Shrink.Phys) (c : Shrink.Cell),
        geometry.cellsT P L l t m₁ c → geometry.cellsT P L l t m₂ c
  | .leaf v, L, l, m₀, m₀', h, _, m₁, m₂, c, hc => by
    cases L with
    | scalar w => rw [Shrink.Geometry.cellsT] at hc ⊢; exact hc
    | _ => simp only [Shrink.Geometry.write, reduceCtorEq] at h
  | .keyed f, L, l, m₀, m₀', h, _, m₁, m₂, c, hc => by
    cases L <;> simp only [Shrink.Geometry.write, reduceCtorEq] at h
  | .blob bs, L, l, m₀, m₀', h, hn, m₁, m₂, c, hc => by
    cases L with
    | bytes =>
      rw [Shrink.Geometry.write] at h
      have hr : l.region ≠ .memory := fun hr =>
        absurd ((hn hr).symm.trans (writeBlob_mem h hr)) (Nat.succ_ne_zero 0)
      simp only [Shrink.Geometry.cellsT, geometry, dataLoc, if_neg hr] at hc ⊢
      exact hc
    | _ => simp only [Shrink.Geometry.write, reduceCtorEq] at h
  | .node xs, L, l, m₀, m₀', h, hn, m₁, m₂, c, hc => by
    cases L with
    | fixedArray e n =>
      rw [Shrink.Geometry.write] at h
      split at h
      · rw [Shrink.Geometry.cellsT] at hc ⊢
        exact elemCellsT_indep P xs e l 0 m₀ m₀' h m₁ m₂ c hc
      · cases h
    | dynArray e =>
      rw [Shrink.Geometry.write] at h
      split at h
      · obtain ⟨m, hw, he⟩ := bind_some h
        have hr : l.region = .memory → l.offset = 0 := fun hr =>
          absurd ((hn hr).symm.trans (writeLength_mem hw hr)) (Nat.succ_ne_zero 0)
        rw [Shrink.Geometry.cellsT, data_congr m₁ m hr] at hc
        rw [Shrink.Geometry.cellsT, data_congr m₂ m hr]
        exact hc.imp id (elemCellsT_indep P xs e _ 0 m m₀' he m₁ m₂ c)
      · cases h
    | struct fs =>
      rw [Shrink.Geometry.write] at h
      rw [Shrink.Geometry.cellsT] at hc ⊢
      exact fieldCellsT_indep P xs fs fs l 0 m₀ m₀' h (fun j => by rw [Nat.zero_add]) m₁ m₂ c hc
    | _ => simp only [Shrink.Geometry.write, reduceCtorEq] at h
private theorem elemCellsT_indep (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (e : Shrink.Layout) (l : Shrink.Loc) (i : Nat)
      (m₀ m₀' : Shrink.Phys), geometry.writeElems P e l xs i m₀ = some m₀' →
      ∀ (m₁ m₂ : Shrink.Phys) (c : Shrink.Cell),
        geometry.elemCellsT P e l xs i m₁ c → geometry.elemCellsT P e l xs i m₂ c
  | [], _, _, _, _, _, _, _, _, _, hc => by
    rw [Shrink.Geometry.elemCellsT] at hc
    exact hc.elim
  | x :: xs, e, l, i, m₀, m₀', h, m₁, m₂, c, hc => by
    rw [Shrink.Geometry.writeElems] at h
    obtain ⟨m, hx, hxs⟩ := bind_some h
    rw [Shrink.Geometry.elemCellsT] at hc ⊢
    exact hc.imp (cellsT_indep P x e _ m₀ m hx (elem_nested P e l i) m₁ m₂ c)
      (elemCellsT_indep P xs e l (i + 1) m m₀' hxs m₁ m₂ c)
private theorem fieldCellsT_indep (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (fs all : List Shrink.Layout) (l : Shrink.Loc) (i : Nat)
      (m₀ m₀' : Shrink.Phys), geometry.writeFields P all l fs xs i m₀ = some m₀' →
      (∀ j, all[i + j]? = fs[j]?) →
      ∀ (m₁ m₂ : Shrink.Phys) (c : Shrink.Cell),
        geometry.fieldCellsT P all l fs xs i m₁ c → geometry.fieldCellsT P all l fs xs i m₂ c
  | [], fs, _, _, _, _, _, _, _, _, _, _, hc => by
    cases fs <;> simp only [Shrink.Geometry.fieldCellsT] at hc
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, hc => by
    simp only [Shrink.Geometry.fieldCellsT] at hc
  | x :: xs, f :: fs, all, l, i, m₀, m₀', h, hi, m₁, m₂, c, hc => by
    rw [Shrink.Geometry.writeFields] at h
    obtain ⟨m, hx, hxs⟩ := bind_some h
    rw [Shrink.Geometry.fieldCellsT] at hc ⊢
    exact hc.imp
      (cellsT_indep P x f _ m₀ m hx (field_nested P all l i f (hi 0)) m₁ m₂ c)
      (fieldCellsT_indep P xs fs all l (i + 1) m m₀' hxs
        (fun j => by rw [show i + 1 + j = i + (j + 1) by omega]; exact hi (j + 1)) m₁ m₂ c)
end

/-! ## Frame -/

mutual
/-- **Frame**: a write changes cells of the written footprint only. -/
theorem frame (P : Shrink.Params) :
    ∀ (L : Shrink.Layout) (l : Shrink.Loc) (t : Shrink.Tree) (m m' : Shrink.Phys),
      geometry.write P L l t m = some m' →
      ∀ c, ¬ geometry.cellsT P L l t m' c → m'.byte c = m.byte c
  | L, l, .leaf v, m, m', h, c, hc => by
    cases L with
    | scalar w =>
      rw [Shrink.Geometry.write] at h
      split at h
      · exact writeScalar_frame P w l v m m' c h hc
      · cases h
    | _ => simp only [Shrink.Geometry.write, reduceCtorEq] at h
  | L, l, .keyed f, m, m', h, c, hc => by
    cases L <;> simp only [Shrink.Geometry.write, reduceCtorEq] at h
  | L, l, .blob bs, m, m', h, c, hc => by
    cases L with
    | bytes =>
      rw [Shrink.Geometry.write] at h
      rw [Shrink.Geometry.cellsT] at hc
      exact writeBlob_frame P l bs m m' c h hc
    | _ => simp only [Shrink.Geometry.write, reduceCtorEq] at h
  | L, l, .node xs, m, m', h, c, hc => by
    cases L with
    | fixedArray e n =>
      rw [Shrink.Geometry.write] at h
      split at h
      · rw [Shrink.Geometry.cellsT] at hc
        exact writeElems_frame P xs e l 0 m m' h c hc
      · cases h
    | dynArray e =>
      rw [Shrink.Geometry.write] at h
      split at h
      · obtain ⟨m₁, hw, he⟩ := bind_some h
        rw [Shrink.Geometry.cellsT, data_congr m' m₁ (writeLength_mem hw)] at hc
        exact (writeElems_frame P xs e _ 0 m₁ m' he c fun hx => hc (.inr hx)).trans
          (writeLength_frame P l _ m m₁ c hw fun hx => hc (.inl hx))
      · cases h
    | struct fs =>
      rw [Shrink.Geometry.write] at h
      rw [Shrink.Geometry.cellsT] at hc
      exact writeFields_frame P xs fs fs l 0 m m' h (fun j => by rw [Nat.zero_add]) c hc
    | _ => simp only [Shrink.Geometry.write, reduceCtorEq] at h
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
      (frame P e _ x m m₁ hx c fun hh =>
        hc (.inl (cellsT_indep P x e _ m m₁ hx (elem_nested P e l i) m₁ m' c hh)))
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
      (frame P f _ x m m₁ hx c fun hh => hc (.inl
        (cellsT_indep P x f _ m m₁ hx (field_nested P all l i f (hi 0)) m₁ m' c hh)))
end

theorem writeElems_frame_shared (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (e : Shrink.Layout) (l : Shrink.Loc) (i : Nat)
      (m m' : Shrink.Phys), geometry.writeElems P e l xs i m = some m' →
      ∀ c, ¬ geometry.elemCellsT P e l xs i m' c → m'.byte c = m.byte c :=
  writeElems_frame P

theorem writeFields_frame_shared (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (fs all : List Shrink.Layout) (l : Shrink.Loc) (i : Nat)
      (m m' : Shrink.Phys), geometry.writeFields P all l fs xs i m = some m' →
      (∀ j, all[i + j]? = fs[j]?) →
      ∀ c, ¬ geometry.fieldCellsT P all l fs xs i m' c → m'.byte c = m.byte c :=
  writeFields_frame P

/-! ## Ill-typed writes fail -/

mutual
/-- **An ill-typed write fails**, never a no-op. -/
theorem illTyped (P : Shrink.Params) :
    ∀ (L : Shrink.Layout) (l : Shrink.Loc) (t : Shrink.Tree) (m : Shrink.Phys),
      ¬ L.Fits t → geometry.write P L l t m = none
  | L, l, .leaf v, m, h => by
    cases L with
    | scalar w =>
      rw [Shrink.Layout.Fits] at h
      rw [Shrink.Geometry.write, if_neg h]
    | _ => simp only [Shrink.Geometry.write]
  | L, l, .keyed f, m, _ => by
    cases L <;> simp only [Shrink.Geometry.write]
  | L, l, .blob bs, m, h => by
    cases L with
    | bytes =>
      rw [Shrink.Layout.Fits] at h
      simp only [Shrink.Geometry.write, geometry, dif_neg h]
    | _ => simp only [Shrink.Geometry.write]
  | L, l, .node xs, m, h => by
    cases L with
    | fixedArray e n =>
      rw [Shrink.Layout.Fits] at h
      rw [Shrink.Geometry.write]
      split
      · rename_i hl
        exact writeElems_illTyped P xs e l 0 m fun ha => h ⟨hl.1, hl.2, ha⟩
      · rfl
    | dynArray e =>
      rw [Shrink.Layout.Fits] at h
      rw [Shrink.Geometry.write]
      split
      · rename_i hl
        cases hw : geometry.writeLength P l xs.length m with
        | none => rfl
        | some m₁ => exact writeElems_illTyped P xs e _ 0 m₁ fun ha => h ⟨hl, ha⟩
      · rfl
    | struct fs =>
      rw [Shrink.Layout.Fits] at h
      rw [Shrink.Geometry.write]
      exact writeFields_illTyped P xs fs fs l 0 m h
    | _ => simp only [Shrink.Geometry.write]
private theorem writeElems_illTyped (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (e : Shrink.Layout) (l : Shrink.Loc) (i : Nat) (m : Shrink.Phys),
      ¬ e.FitsAll xs → geometry.writeElems P e l xs i m = none
  | [], _, _, _, _, h => by
    rw [Shrink.Layout.FitsAll] at h
    exact absurd trivial h
  | x :: xs, e, l, i, m, h => by
    rw [Shrink.Layout.FitsAll] at h
    rw [Shrink.Geometry.writeElems]
    cases hx : geometry.write P e (geometry.elem P e l i) x m with
    | none => rfl
    | some m₁ =>
      exact writeElems_illTyped P xs e l (i + 1) m₁ fun ha => h
        ⟨Classical.byContradiction fun hn =>
          Option.noConfusion (illTyped P e _ x m hn ▸ hx : none = some m₁), ha⟩
private theorem writeFields_illTyped (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (fs all : List Shrink.Layout) (l : Shrink.Loc) (i : Nat)
      (m : Shrink.Phys), ¬ Shrink.Layout.FitsFields fs xs →
      geometry.writeFields P all l fs xs i m = none
  | [], fs, _, _, _, _, h => by
    cases fs with
    | nil =>
      rw [Shrink.Layout.FitsFields] at h
      exact absurd trivial h
    | cons => simp only [Shrink.Geometry.writeFields]
  | _ :: _, [], _, _, _, _, _ => by
    simp only [Shrink.Geometry.writeFields]
  | x :: xs, f :: fs, all, l, i, m, h => by
    rw [Shrink.Layout.FitsFields] at h
    rw [Shrink.Geometry.writeFields]
    cases hx : geometry.write P f (geometry.field P all l i) x m with
    | none => rfl
    | some m₁ =>
      exact writeFields_illTyped P xs fs all l (i + 1) m₁ fun ha => h
        ⟨Classical.byContradiction fun hn =>
          Option.noConfusion (illTyped P f _ x m hn ▸ hx : none = some m₁), ha⟩
end

/-! ## Fitting slot writes succeed -/

private theorem writeScalar_total (P : Shrink.Params) (w : Nat) (l : Shrink.Loc) (v : Nat)
    (m : Shrink.Phys) (hr : l.region ≠ .memory) (hf : 0 < w ∧ w ≤ 32 ∧ v < 256 ^ w) :
    ∃ m', geometry.writeScalar P w l v m = some m' := by
  simp only [geometry, if_neg hr, slotField]
  by_cases h : 0 < w ∧ l.offset + w ≤ 32
  · rw [dif_pos h, Option.bind_some]
    exact ⟨_, dif_pos hf.2.2⟩
  · rw [dif_neg h, dif_pos ⟨hf.1, hf.2.1⟩, Option.bind_some]
    exact ⟨_, dif_pos hf.2.2⟩

mutual
/-- **A fitting mapping-free persistent or transient write succeeds.** -/
theorem write_total (P : Shrink.Params) :
    ∀ (L : Shrink.Layout) (l : Shrink.Loc) (t : Shrink.Tree) (m : Shrink.Phys),
      l.region ≠ .memory → L.NoMapping → L.Fits t → ∃ m', geometry.write P L l t m = some m'
  | L, l, .leaf v, m, hr, _, hf => by
    cases L with
    | scalar w =>
      rw [Shrink.Layout.Fits] at hf
      rw [Shrink.Geometry.write, if_pos hf]
      exact writeScalar_total P w l v m hr hf
    | _ => simp only [Shrink.Layout.Fits] at hf
  | L, l, .keyed f, m, _, hn, hf => by
    cases L with
    | mapping v => rw [Shrink.Layout.NoMapping] at hn; exact hn.elim
    | _ => simp only [Shrink.Layout.Fits] at hf
  | L, l, .blob bs, m, hr, _, hf => by
    cases L with
    | bytes =>
      rw [Shrink.Layout.Fits] at hf
      simp only [Shrink.Geometry.write, geometry, dif_pos hf, if_neg hr]
      exact ⟨_, rfl⟩
    | _ => simp only [Shrink.Layout.Fits] at hf
  | L, l, .node xs, m, hr, hn, hf => by
    cases L with
    | fixedArray e n =>
      rw [Shrink.Layout.Fits] at hf
      rw [Shrink.Layout.NoMapping] at hn
      rw [Shrink.Geometry.write, if_pos ⟨hf.1, hf.2.1⟩]
      exact writeElems_total P xs e l 0 m hr hn hf.2.2
    | dynArray e =>
      rw [Shrink.Layout.Fits] at hf
      rw [Shrink.Layout.NoMapping] at hn
      have hw : ∃ m₁, geometry.writeLength P l xs.length m = some m₁ := by
        simp only [geometry, if_neg hr]
        exact ⟨_, rfl⟩
      obtain ⟨m₁, hw⟩ := hw
      rw [Shrink.Geometry.write, if_pos hf.1, hw]
      exact writeElems_total P xs e _ 0 m₁ (data_slotted P l m₁ hr) hn hf.2
    | struct fs =>
      rw [Shrink.Layout.Fits] at hf
      rw [Shrink.Layout.NoMapping] at hn
      rw [Shrink.Geometry.write]
      exact writeFields_total P xs fs fs l 0 m hr hn hf
    | _ => simp only [Shrink.Layout.Fits] at hf
private theorem writeElems_total (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (e : Shrink.Layout) (l : Shrink.Loc) (i : Nat) (m : Shrink.Phys),
      l.region ≠ .memory → e.NoMapping → e.FitsAll xs →
      ∃ m', geometry.writeElems P e l xs i m = some m'
  | [], _, _, _, m, _, _, _ => ⟨m, by rw [Shrink.Geometry.writeElems]⟩
  | x :: xs, e, l, i, m, hr, hn, hf => by
    rw [Shrink.Layout.FitsAll] at hf
    obtain ⟨m₁, hx⟩ := write_total P e _ x m (elem_slotted P e l i hr) hn hf.1
    rw [Shrink.Geometry.writeElems, hx]
    exact writeElems_total P xs e l (i + 1) m₁ hr hn hf.2
private theorem writeFields_total (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (fs all : List Shrink.Layout) (l : Shrink.Loc) (i : Nat)
      (m : Shrink.Phys), l.region ≠ .memory → (∀ f ∈ fs, f.NoMapping) →
      Shrink.Layout.FitsFields fs xs → ∃ m', geometry.writeFields P all l fs xs i m = some m'
  | [], fs, _, _, _, m, _, _, hf => by
    cases fs with
    | nil => exact ⟨m, by rw [Shrink.Geometry.writeFields]⟩
    | cons => simp only [Shrink.Layout.FitsFields] at hf
  | _ :: _, [], _, _, _, _, _, _, hf => by
    simp only [Shrink.Layout.FitsFields] at hf
  | x :: xs, f :: fs, all, l, i, m, hr, hn, hf => by
    rw [Shrink.Layout.FitsFields] at hf
    obtain ⟨m₁, hx⟩ := write_total P f _ x m (field_slotted P all l i hr)
      (hn f (List.mem_cons_self ..)) hf.1
    rw [Shrink.Geometry.writeFields, hx]
    exact writeFields_total P xs fs all l (i + 1) m₁ hr
      (fun g hg => hn g (List.mem_cons_of_mem _ hg)) hf.2
end

end Solidity.Yul.Layout
