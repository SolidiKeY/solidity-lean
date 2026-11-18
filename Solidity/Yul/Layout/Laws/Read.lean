import Solidity.Yul.Layout.Geometry
import Solidity.Yul.Layout.ReadSequence

/-!
# A read of the geometry depends on its footprint only

`local_read` is the statement of `Shrink.LayoutView.Laws.local_read` for
`geometry`: two states that agree on every cell of `geometry.cells` (taken in
the first state) give the same `geometry.read`. The proof is one mutual
recursion over the layout; each leaf codec is shown to read only the bytes its
footprint names, and the length footprint of a dynamic array or `bytes` fixes the
length and the data location before its payload is compared.
-/
namespace Solidity.Yul.Layout

open Solidity.Goals
open Solidity.Yul.Views

/-- Numbers with the same `k` low base-256 digits agree modulo `256 ^ k`. -/
private theorem mod_of_digits (x y k : Nat)
    (h : ∀ b, b < k → x / 256 ^ b % 256 = y / 256 ^ b % 256) :
    x % 256 ^ k = y % 256 ^ k := by
  induction k with
  | zero => simp only [Nat.pow_zero, Nat.mod_one]
  | succ k ih =>
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, ih (fun b hb => h b (by omega)),
      h k (Nat.lt_succ_self k)]

/-- The same digits `lo, …, lo + k - 1` give the same packed field. -/
private theorem field_of_digits (x y lo k : Nat)
    (h : ∀ b, lo ≤ b → b < lo + k → x / 256 ^ b % 256 = y / 256 ^ b % 256) :
    x / 256 ^ lo % 256 ^ k = y / 256 ^ lo % 256 ^ k := by
  apply mod_of_digits
  intro b hb
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  exact h (lo + b) (by omega) (by omega)

/-- Words with the same 32 bytes are equal. -/
private theorem word_of_digits (x y : Roadmap.Word)
    (h : ∀ b, b < 32 → x.val / 256 ^ b % 256 = y.val / 256 ^ b % 256) : x = y := by
  have hx : x.val < 256 ^ 32 := x.isLt
  have hy : y.val < 256 ^ 32 := y.isLt
  have e := mod_of_digits x.val y.val 32 h
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at e
  exact Fin.ext e

/-- The byte of a slot cell, in a slot region. -/
private theorem byte_slot {r : Shrink.Region} (h : r ≠ .memory) (m : Shrink.Phys)
    (w : Roadmap.Word) (b : Nat) :
    m.byte (.slot r w b) = (m.slots r w).val / 256 ^ b % 256 := by
  cases r with
  | memory => exact absurd rfl h
  | storage => rfl
  | transient => rfl

/-- States that agree on a memory object agree on each of its bytes. -/
private theorem memory_agree (m m' : Shrink.Phys) (a n : Nat)
    (h : ∀ c, Shrink.objectCells a n c → m.byte c = m'.byte c) (i : Nat) (hi : i < n) :
    m.memory (a + i) = m'.memory (a + i) :=
  UInt8.toNat_inj.mp (h (.mem (a + i)) ⟨Nat.le_add_right a i, Nat.add_lt_add_left hi a⟩)

/-- States that agree on every byte of a slot hold the same word there. -/
private theorem slot_agree {r : Shrink.Region} (hr : r ≠ .memory) (m m' : Shrink.Phys)
    (w : Roadmap.Word) (h : ∀ b, b < 32 → m.byte (.slot r w b) = m'.byte (.slot r w b)) :
    m.slots r w = m'.slots r w :=
  word_of_digits _ _ fun b hb => by
    rw [← byte_slot hr, ← byte_slot hr]
    exact h b hb

/-- A scalar read depends on the scalar footprint only. -/
private theorem scalar_local (P : Shrink.Params) (w : Nat) (l : Shrink.Loc) (m m' : Shrink.Phys)
    (h : ∀ c, geometry.scalarCells P w l c → m.byte c = m'.byte c) :
    geometry.scalar P w l m = geometry.scalar P w l m' := by
  by_cases hr : l.region = .memory
  · simp only [geometry, if_pos hr] at h ⊢
    rw [show mloadNat m.memory l.word = mloadNat m'.memory l.word from
      readBE_congr _ _ _ _ (memory_agree m m' l.word 32 h)]
  · simp only [geometry, if_neg hr] at h ⊢
    cases hf : slotField w l.offset with
    | none => rfl
    | some f =>
      rw [hf] at h
      exact congrArg some (field_of_digits _ _ f.offset f.width fun b hlo hhi => by
        rw [← byte_slot hr, ← byte_slot hr]
        exact h _ ⟨b, rfl, hlo, hhi⟩)

/-- The length word fixes the length and the data location. -/
private theorem length_local (P : Shrink.Params) (l : Shrink.Loc) (m m' : Shrink.Phys)
    (h : ∀ c, geometry.lengthCells P l c → m.byte c = m'.byte c) :
    geometry.length P l m = geometry.length P l m' ∧
      geometry.data P l m = geometry.data P l m' := by
  by_cases hr : l.region = .memory
  · simp only [geometry, dataLoc, if_pos hr] at h ⊢
    by_cases ho : l.offset = 0
    · simp only [if_pos ho] at h ⊢
      exact ⟨readBE_congr _ _ _ _ (memory_agree m m' l.word 32 h), trivial⟩
    · simp only [if_neg ho] at h ⊢
      have bytes := memory_agree m m' l.word 64 h
      refine ⟨readBE_congr _ _ _ _ fun i hi => bytes i (by omega), ?_⟩
      rw [show mloadNat m.memory (l.word + 32) = mloadNat m'.memory (l.word + 32) from
        readBE_congr _ _ _ _ fun i hi => by
          rw [Nat.add_assoc]
          exact bytes (32 + i) (by omega)]
  · simp only [geometry, dataLoc, if_neg hr] at h ⊢
    exact ⟨congrArg Fin.val (slot_agree hr m m' _ fun b hb => h _ ⟨b, rfl, hb⟩), trivial⟩

/-- A `bytes` read depends on the length word and the payload footprint only. -/
private theorem blob_local (P : Shrink.Params) (l : Shrink.Loc) (m m' : Shrink.Phys)
    (h : ∀ c, geometry.lengthCells P l c ∨ geometry.blobCells P l m c → m.byte c = m'.byte c) :
    geometry.blob P l m = geometry.blob P l m' := by
  obtain ⟨hl, hd⟩ := length_local P l m m' fun c hc => h c (Or.inl hc)
  have hb := fun c hc => h c (Or.inr hc)
  by_cases hr : l.region = .memory
  · simp only [geometry, if_pos hr] at hl hd hb ⊢
    rw [← hl, ← hd, readBytes_congr_on _ _ _ _ (memory_agree m m' _ _ hb)]
  · simp only [geometry, if_neg hr] at hl hd hb ⊢
    rw [← hl, ← hd]
    refine congrArg some (List.map_congr_left fun i hi => ?_)
    have bound : i < 2 ^ 256 :=
      Nat.lt_trans (List.mem_range.mp hi) (m.slots l.region (Shrink.toWord l.word)).isLt
    rw [slot_agree hr m m' _ fun b hb' => hb _ ⟨i / 32, b, by omega, hb', rfl⟩]

/-- An element's footprint is part of the footprint of its sequence. -/
private theorem elemCells_of (G : Shrink.Geometry) (P : Shrink.Params) (e : Shrink.Layout)
    (l : Shrink.Loc) (n i j : Nat) (m : Shrink.Phys) (c : Shrink.Cell)
    (hi : i ≤ j) (hj : j < i + n) (hc : G.cells P e (G.elem P e l j) m c) :
    G.elemCells P e l n i m c := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    simp only [Shrink.Geometry.elemCells]
    by_cases same : j = i
    · subst same
      exact Or.inl hc
    · exact Or.inr (ih (i + 1) (by omega) (by omega))

mutual
/-- **A read depends on its footprint only** (`LayoutView.Laws.local_read`
for `geometry`). -/
theorem local_read (P : Shrink.Params) : ∀ (L : Shrink.Layout) (l : Shrink.Loc)
    (m m' : Shrink.Phys), (∀ c, geometry.cells P L l m c → m.byte c = m'.byte c) →
    geometry.read P L l m = geometry.read P L l m'
  | .scalar w, l, m, m', h => by
    simp only [Shrink.Geometry.cells] at h
    simp only [Shrink.Geometry.read, scalar_local P w l m m' h]
  | .fixedArray e n, l, m, m', h => by
    simp only [Shrink.Geometry.cells] at h
    simp only [Shrink.Geometry.read]
    rw [readElems_congr geometry P e l n 0 m m' fun j hj hjn =>
      local_read P e _ m m' fun c hc => h c (elemCells_of _ _ _ _ _ _ _ _ _ hj hjn hc)]
  | .dynArray e, l, m, m', h => by
    simp only [Shrink.Geometry.cells] at h
    obtain ⟨hl, hd⟩ := length_local P l m m' fun c hc => h c (Or.inl hc)
    simp only [Shrink.Geometry.read]
    rw [← hl, ← hd, readElems_congr geometry P e _ _ 0 m m' fun j hj hjn =>
      local_read P e _ m m' fun c hc =>
        h c (Or.inr (elemCells_of _ _ _ _ _ _ _ _ _ hj hjn hc))]
  | .bytes, l, m, m', h => by
    simp only [Shrink.Geometry.cells] at h
    simp only [Shrink.Geometry.read, blob_local P l m m' h]
  | .struct fs, l, m, m', h => by
    simp only [Shrink.Geometry.cells] at h
    simp only [Shrink.Geometry.read]
    rw [readFields_local P fs fs l 0 m m' h]
  | .mapping v, l, m, m', h => by
    simp only [Shrink.Geometry.cells] at h
    simp only [Shrink.Geometry.read]
    exact congrArg (fun entry => some (Shrink.Tree.keyed entry))
      (funext fun k => local_read P v _ m m' fun c hc => h c ⟨k, hc⟩)
/-- The member reads of a struct depend on the member footprints only. -/
private theorem readFields_local (P : Shrink.Params) : ∀ (fs all : List Shrink.Layout)
    (l : Shrink.Loc) (i : Nat) (m m' : Shrink.Phys),
    (∀ c, geometry.fieldCells P all l fs i m c → m.byte c = m'.byte c) →
    geometry.readFields P all l fs i m = geometry.readFields P all l fs i m'
  | [], _, _, _, _, _, _ => by simp only [Shrink.Geometry.readFields]
  | f :: fs, all, l, i, m, m', h => by
    simp only [Shrink.Geometry.fieldCells] at h
    simp only [Shrink.Geometry.readFields]
    rw [local_read P f _ m m' fun c hc => h c (Or.inl hc),
      readFields_local P fs all l (i + 1) m m' fun c hc => h c (Or.inr hc)]
end

end Solidity.Yul.Layout
