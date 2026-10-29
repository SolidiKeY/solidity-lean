import Solidity.Language.FixedPoint.Abi

/-!
# Fixed-point values in storage

A storage slot is a 256-bit word.  A fixed-point value occupies `M/8`
bytes of a slot at a byte offset, right-aligned (low-order bytes first),
holding its `M`-bit two's-complement pattern, as solc packs `intM`
(`storageBytes = M/8`, `leftAligned = false`, `Types.h:552–554` at
`v0.8.38`).  The physical layout is not observable (the scope's "Readings":
solc's slot behaviour fixes the logical alias semantics, not the physical
packing), so this layout is a choice; the one chosen is solc's
(`docs/feature-work/fixed-point-semantics.md`, P6 and §6.4).

* `field` / `setField` — a byte range of a word, read and written;
  `field_setField` (read after write), `field_setField_below`,
  `field_setField_above` (writes leave disjoint ranges alone),
  `setField_field` (writing back what is there), `setField_setField`
  (the last write wins), `setField_lt` (the word stays a word).
* `Fx.load` / `Fx.store` — a fixed-point value at an offset:
  `Fx.load_store` (read after write), `Fx.load_store_disjoint`
  (non-interference with any other packed value of any type),
  `Fx.store_load`, `Fx.store_store`.
* `place` — solc's packing of a sequence of value types into slots:
  `place_fits` (each item lies inside its slot), `place_pairwise` (no two
  items overlap).
* `Fx.keyWord` — a mapping key hashes as its padded ABI word, injectively
  (`Fx.keyWord_injective`).
-/

namespace Solidity.Language.FixedPoint

/-! ### Byte ranges of a word -/

/-- The `len` bytes of `w` from byte `off` (counted from the low end). -/
def field (w off len : Nat) : Nat := w / 2 ^ (8 * off) % 2 ^ (8 * len)

/-- `w` with the `len` bytes from byte `off` replaced by `v` (modulo
`2^(8·len)`). -/
def setField (w off len v : Nat) : Nat :=
  w % 2 ^ (8 * off) + v % 2 ^ (8 * len) * 2 ^ (8 * off) +
    w / 2 ^ (8 * (off + len)) * 2 ^ (8 * (off + len))

theorem pow_off_len (off len : Nat) :
    (2 : Nat) ^ (8 * (off + len)) = 2 ^ (8 * off) * 2 ^ (8 * len) := by
  rw [Nat.mul_add, Nat.pow_add]

/-! The three parts of a written word, for any positive `B` and `L`. -/

theorem parts_eq (lo v h B L : Nat) :
    lo + v * B + h * (B * L) = lo + B * (v + h * L) := by
  rw [Nat.mul_add, ← Nat.add_assoc, Nat.mul_comm B v, Nat.mul_left_comm B h L]

theorem parts_mod {lo v h B L : Nat} (hlo : lo < B) : (lo + v * B + h * (B * L)) % B = lo := by
  rw [parts_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]

theorem parts_div {lo v h B L : Nat} (hlo : lo < B) :
    (lo + v * B + h * (B * L)) / B = v + h * L := by
  have hB : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le lo) hlo
  rw [parts_eq, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hlo, Nat.zero_add]

theorem parts_hi {lo v h B L : Nat} (hlo : lo < B) (hv : v < L) :
    (lo + v * B + h * (B * L)) / (B * L) = h := by
  have hB : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le lo) hlo
  have hL : 0 < L := Nat.lt_of_le_of_lt (Nat.zero_le v) hv
  have hBL : 0 < B * L := Nat.mul_pos hB hL
  have h1 : v * B ≤ (L - 1) * B := Nat.mul_le_mul_right _ (by omega)
  have h2 : (L - 1) * B = L * B - B := Nat.sub_one_mul _ _
  have h3 : B ≤ L * B := Nat.le_mul_of_pos_left _ hL
  have h4 : L * B = B * L := Nat.mul_comm L B
  have hlt : lo + v * B < B * L := by omega
  rw [Nat.add_mul_div_right _ _ hBL, Nat.div_eq_of_lt hlt, Nat.zero_add]

theorem setField_parts (w off len v : Nat) : setField w off len v =
    w % 2 ^ (8 * off) + v % 2 ^ (8 * len) * 2 ^ (8 * off) +
      w / (2 ^ (8 * off) * 2 ^ (8 * len)) * (2 ^ (8 * off) * 2 ^ (8 * len)) := by
  rw [setField, pow_off_len]

theorem low_lt (w off : Nat) : w % 2 ^ (8 * off) < 2 ^ (8 * off) := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem val_lt (v len : Nat) : v % 2 ^ (8 * len) < 2 ^ (8 * len) := Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The bytes below `off` of a write. -/
theorem setField_low (w off len v : Nat) :
    setField w off len v % 2 ^ (8 * off) = w % 2 ^ (8 * off) := by
  rw [setField_parts, parts_mod (low_lt w off)]

/-- The bytes from `off` up, shifted down. -/
theorem setField_div (w off len v : Nat) :
    setField w off len v / 2 ^ (8 * off) =
      v % 2 ^ (8 * len) + w / 2 ^ (8 * (off + len)) * 2 ^ (8 * len) := by
  rw [setField_parts, parts_div (low_lt w off), pow_off_len]

/-- The bytes above `off + len` of a write. -/
theorem setField_hi (w off len v : Nat) :
    setField w off len v / 2 ^ (8 * (off + len)) = w / 2 ^ (8 * (off + len)) := by
  rw [setField_parts, pow_off_len, parts_hi (low_lt w off) (val_lt v len)]

/-- Read after write. -/
theorem field_setField (w off len v : Nat) :
    field (setField w off len v) off len = v % 2 ^ (8 * len) := by
  simp only [field, setField_div, Nat.add_mul_mod_self_right, Nat.mod_mod]

/-- `field` depends only on the bytes below its end. -/
theorem field_eq_mod (w off len : Nat) :
    field w off len = w % 2 ^ (8 * (off + len)) / 2 ^ (8 * off) := by
  simp only [field, pow_off_len]
  exact (Nat.mod_mul_right_div_self w _ _).symm

/-- A write leaves the bytes below it alone. -/
theorem field_setField_below {w off len v off' len' : Nat} (h : off' + len' ≤ off) :
    field (setField w off len v) off' len' = field w off' len' := by
  have hd : 2 ^ (8 * (off' + len')) ∣ 2 ^ (8 * off) :=
    Nat.pow_dvd_pow 2 (Nat.mul_le_mul_left 8 h)
  have hm : setField w off len v % 2 ^ (8 * (off' + len')) = w % 2 ^ (8 * (off' + len')) := by
    rw [← Nat.mod_mod_of_dvd (setField w off len v) hd, setField_low, Nat.mod_mod_of_dvd w hd]
  rw [field_eq_mod, hm, ← field_eq_mod]

/-- A write leaves the bytes above it alone. -/
theorem field_setField_above {w off len v off' len' : Nat} (h : off + len ≤ off') :
    field (setField w off len v) off' len' = field w off' len' := by
  have hp : (2 : Nat) ^ (8 * off') = 2 ^ (8 * (off + len)) * 2 ^ (8 * (off' - (off + len))) := by
    rw [← Nat.pow_add, ← Nat.mul_add, Nat.add_sub_cancel' h]
  simp only [field, hp, ← Nat.div_div_eq_div_mul, setField_hi]

/-- Writing back what is there changes nothing. -/
theorem setField_field (w off len : Nat) : setField w off len (field w off len) = w := by
  have h1 : w % 2 ^ (8 * off) + 2 ^ (8 * off) * (w / 2 ^ (8 * off)) = w := Nat.mod_add_div w _
  have h2 : w / 2 ^ (8 * off) % 2 ^ (8 * len) +
      2 ^ (8 * len) * (w / 2 ^ (8 * off) / 2 ^ (8 * len)) = w / 2 ^ (8 * off) :=
    Nat.mod_add_div _ _
  have h3 : w / 2 ^ (8 * off) / 2 ^ (8 * len) = w / (2 ^ (8 * off) * 2 ^ (8 * len)) :=
    Nat.div_div_eq_div_mul _ _ _
  rw [setField_parts, field, Nat.mod_mod, parts_eq, ← h3, Nat.mul_comm _ (2 ^ (8 * len)), h2, h1]

/-- The last write wins. -/
theorem setField_setField (w off len v v' : Nat) :
    setField (setField w off len v) off len v' = setField w off len v' := by
  have hlo : setField w off len v % 2 ^ (8 * off) = w % 2 ^ (8 * off) := setField_low w off len v
  have hhi : setField w off len v / 2 ^ (8 * (off + len)) = w / 2 ^ (8 * (off + len)) :=
    setField_hi w off len v
  rw [setField, hlo, hhi]
  rfl

/-- A write inside the word keeps it a word. -/
theorem setField_lt {w off len : Nat} (v : Nat) (hw : w < 2 ^ 256) (h : off + len ≤ 32) :
    setField w off len v < 2 ^ 256 := by
  have hB : 0 < 2 ^ (8 * off) := Nat.two_pow_pos _
  have hL : 0 < 2 ^ (8 * len) := Nat.two_pow_pos _
  have hK : (2 : Nat) ^ 256 = 2 ^ (8 * (off + len)) * 2 ^ (256 - 8 * (off + len)) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
  have hBL : 0 < 2 ^ (8 * (off + len)) := Nat.two_pow_pos _
  have hlo : w % 2 ^ (8 * off) < 2 ^ (8 * off) := Nat.mod_lt _ hB
  have hv : v % 2 ^ (8 * len) < 2 ^ (8 * len) := Nat.mod_lt _ hL
  have hhi : w / 2 ^ (8 * (off + len)) < 2 ^ (256 - 8 * (off + len)) := by
    apply (Nat.div_lt_iff_lt_mul hBL).mpr
    rw [Nat.mul_comm, ← hK]; exact hw
  -- the low part is below `2^(8·(off+len))`
  have hlow : w % 2 ^ (8 * off) + v % 2 ^ (8 * len) * 2 ^ (8 * off) < 2 ^ (8 * (off + len)) := by
    have h1 : v % 2 ^ (8 * len) * 2 ^ (8 * off) ≤ (2 ^ (8 * len) - 1) * 2 ^ (8 * off) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (2 ^ (8 * len) - 1) * 2 ^ (8 * off) = 2 ^ (8 * len) * 2 ^ (8 * off) - 2 ^ (8 * off) :=
      Nat.sub_one_mul _ _
    have h3 : 2 ^ (8 * off) ≤ 2 ^ (8 * len) * 2 ^ (8 * off) := Nat.le_mul_of_pos_left _ hL
    rw [pow_off_len, Nat.mul_comm (2 ^ (8 * off))]
    omega
  have hhigh : w / 2 ^ (8 * (off + len)) * 2 ^ (8 * (off + len)) + 2 ^ (8 * (off + len)) ≤
      2 ^ 256 := by
    have h4 : (w / 2 ^ (8 * (off + len)) + 1) * 2 ^ (8 * (off + len)) ≤
        2 ^ (256 - 8 * (off + len)) * 2 ^ (8 * (off + len)) := Nat.mul_le_mul_right _ hhi
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ (256 - _)), ← hK] at h4
    exact h4
  unfold setField
  omega

/-! ### Fixed-point values in a slot -/

/-- A storage slot. -/
abbrev Slot := Fin (2 ^ 256)

namespace Fx

variable {t t' : FxTy}

theorem toBits_nonneg (a : Fx t) : 0 ≤ toBits a := by
  have hp : (0 : Int) < 2 ^ t.bits := Int.pow_pos (by decide)
  exact Int.emod_nonneg _ (by omega)

theorem storageBytes_bits (t : FxTy) : 8 * t.storageBytes = t.bits := by
  have h : (decide (8 ≤ t.bits) && decide (t.bits ≤ 256) && t.bits % 8 == 0 &&
      decide (t.digits ≤ 80)) = true := t.valid
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  simp only [FxTy.storageBytes]
  omega

/-- The value of type `t` at byte `off` of a slot: its `M/8` bytes read as
the bit pattern (sign-extended where signed). -/
def load (t : FxTy) (w : Slot) (off : Nat) : Fx t :=
  ofBits t (field w.val off t.storageBytes : Int)

/-- A slot with the value written at byte `off` (inside the slot). -/
def store (w : Slot) (off : Nat) (h : off + t.storageBytes ≤ 32) (a : Fx t) : Slot :=
  ⟨setField w.val off t.storageBytes (toBits a).toNat, setField_lt _ w.isLt h⟩

/-- Read after write. -/
theorem load_store (w : Slot) (off : Nat) (h : off + t.storageBytes ≤ 32) (a : Fx t) :
    load t (store w off h a) off = a := by
  have h0 : 0 ≤ toBits a := toBits_nonneg a
  have hp : (0 : Int) < 2 ^ t.bits := Int.pow_pos (by decide)
  have h1 : toBits a < 2 ^ t.bits := Int.emod_lt_of_pos _ hp
  have hcb : ((2 ^ t.bits : Nat) : Int) = (2 : Int) ^ t.bits := Int.natCast_pow 2 _
  have he : ((toBits a).toNat : Int) = toBits a := Int.toNat_of_nonneg h0
  have hlt : (toBits a).toNat < 2 ^ (8 * t.storageBytes) := by
    rw [storageBytes_bits]; omega
  simp only [load, store, field_setField, Nat.mod_eq_of_lt hlt, he, ofBits_toBits]

/-- A packed value of any type in a disjoint byte range is not disturbed. -/
theorem load_store_disjoint (w : Slot) {off off' : Nat} (h : off + t.storageBytes ≤ 32)
    (a : Fx t) (hd : off' + t'.storageBytes ≤ off ∨ off + t.storageBytes ≤ off') :
    load t' (store w off h a) off' = load t' w off' := by
  simp only [load, store]
  rcases hd with hd | hd
  · rw [field_setField_below hd]
  · rw [field_setField_above hd]

/-- Any byte range disjoint from a write is unchanged: the frame for other
packed state variables, whatever their types. -/
theorem field_store_disjoint (w : Slot) {off off' len : Nat} (h : off + t.storageBytes ≤ 32)
    (a : Fx t) (hd : off' + len ≤ off ∨ off + t.storageBytes ≤ off') :
    field (store w off h a).val off' len = field w.val off' len := by
  simp only [store]
  rcases hd with hd | hd
  · exact field_setField_below hd
  · exact field_setField_above hd

/-- Writing back the value that is there changes nothing. -/
theorem store_load (w : Slot) (off : Nat) (h : off + t.storageBytes ≤ 32) :
    store w off h (load t w off) = w := by
  have hlt : field w.val off t.storageBytes < 2 ^ t.bits := by
    rw [← storageBytes_bits]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hcb : ((2 ^ t.bits : Nat) : Int) = (2 : Int) ^ t.bits := Int.natCast_pow 2 _
  have hb : toBits (load t w off) = (field w.val off t.storageBytes : Int) := by
    simp only [load]
    exact toBits_ofBits (Int.natCast_nonneg _) (by omega)
  apply Fin.ext
  simp only [store, hb, Int.toNat_natCast, setField_field]

/-- The last write wins. -/
theorem store_store (w : Slot) (off : Nat) (h : off + t.storageBytes ≤ 32) (a b : Fx t) :
    store (store w off h a) off h b = store w off h b := by
  apply Fin.ext
  simp only [store, setField_setField]

/-- The zero slot reads as zero: an untouched variable holds its default. -/
theorem load_zero (off : Nat) : load t ⟨0, Nat.two_pow_pos 256⟩ off = zero t := by
  apply Subtype.ext
  have hz : wrapInt t 0 = 0 := wrapInt_of_inRange (zero t).2
  simp only [load, field, Nat.zero_div, Nat.zero_mod, Int.natCast_zero, ofBits, wrap, zero, hz]

/-- A mapping key: the padded ABI word that is hashed (P6). -/
def keyWord (a : Fx t) : Fin (2 ^ 256) := encode a

/-- Distinct keys hash distinct words. -/
theorem keyWord_injective {a b : Fx t} (h : keyWord a = keyWord b) : a = b := by
  have ha : decodeV2 t (encode a) = some a := decodeV2_encode a
  have hb : decodeV2 t (encode b) = some b := decodeV2_encode b
  simp only [keyWord] at h
  rw [h, hb] at ha
  exact (Option.some.inj ha).symm

end Fx

/-! ### Packing a sequence of value types -/

/-- solc's packing: each item (its size in bytes, `1 … 32`) goes at the next
free offset of the current slot, or at offset `0` of the next slot when it
does not fit.  The result lists `(slot, offset, size)`. -/
def place : List Nat → Nat → Nat → List (Nat × Nat × Nat)
  | [], _, _ => []
  | s :: ss, slot, off =>
    if off + s ≤ 32 then (slot, off, s) :: place ss slot (off + s)
    else (slot + 1, 0, s) :: place ss (slot + 1) s

/-- Two placed items do not overlap. -/
def Apart (p q : Nat × Nat × Nat) : Prop :=
  p.1 ≠ q.1 ∨ p.2.1 + p.2.2 ≤ q.2.1 ∨ q.2.1 + q.2.2 ≤ p.2.1

/-- Every item placed from `(slot, off)` on starts there or later. -/
theorem place_after : ∀ (ss : List Nat) (slot off : Nat), ∀ p ∈ place ss slot off,
    slot < p.1 ∨ (slot = p.1 ∧ off ≤ p.2.1)
  | [], _, _, p, hp => by simp only [place, List.not_mem_nil] at hp
  | s :: ss, slot, off, p, hp => by
    unfold place at hp
    split at hp
    · simp only [List.mem_cons] at hp
      rcases hp with hp | hp
      · subst hp; exact Or.inr ⟨rfl, Nat.le_refl _⟩
      · rcases place_after ss slot (off + s) p hp with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by omega⟩
    · simp only [List.mem_cons] at hp
      rcases hp with hp | hp
      · subst hp; exact Or.inl (Nat.lt_succ_self _)
      · rcases place_after ss (slot + 1) s p hp with h | h
        · exact Or.inl (by omega)
        · exact Or.inl (by omega)

/-- Every placed item of size at most `32` lies inside its slot. -/
theorem place_fits : ∀ (ss : List Nat) (slot off : Nat), (∀ s ∈ ss, s ≤ 32) →
    ∀ p ∈ place ss slot off, p.2.1 + p.2.2 ≤ 32
  | [], _, _, _, p, hp => by simp only [place, List.not_mem_nil] at hp
  | s :: ss, slot, off, hs, p, hp => by
    have hs1 : s ≤ 32 := hs s (List.mem_cons_self ..)
    have hss : ∀ s' ∈ ss, s' ≤ 32 := fun s' h => hs s' (List.mem_cons_of_mem _ h)
    unfold place at hp
    split at hp
    · rename_i hfit
      simp only [List.mem_cons] at hp
      rcases hp with hp | hp
      · subst hp; exact hfit
      · exact place_fits ss slot (off + s) hss p hp
    · simp only [List.mem_cons] at hp
      rcases hp with hp | hp
      · subst hp; simp only [Nat.zero_add]; exact hs1
      · exact place_fits ss (slot + 1) s hss p hp

/-- No two placed items overlap. -/
theorem place_pairwise : ∀ (ss : List Nat) (slot off : Nat),
    (place ss slot off).Pairwise Apart
  | [], _, _ => List.Pairwise.nil
  | s :: ss, slot, off => by
    unfold place
    split
    · refine List.Pairwise.cons ?_ (place_pairwise ss slot (off + s))
      intro p hp
      rcases place_after ss slot (off + s) p hp with h | h
      · exact Or.inl (by simp only; omega)
      · exact Or.inr (Or.inl (by simp only; omega))
    · refine List.Pairwise.cons ?_ (place_pairwise ss (slot + 1) s)
      intro p hp
      rcases place_after ss (slot + 1) s p hp with h | h
      · exact Or.inl (by simp only; omega)
      · exact Or.inr (Or.inl (by simp only; omega))

/-! ### Worked values -/

section Examples

open Fx

/-- `fixed8x1 a; ufixed16x2 b; fixed128x18 c; ufixed256x0 d;` packs `a`, `b`
and `c` into slot 0 at offsets 0, 1 and 3, and `d` alone into slot 1. -/
example : place [fixed8x1.storageBytes, ufixed16x2.storageBytes, FxTy.fixed.storageBytes,
    (⟨false, 256, 0, by decide⟩ : FxTy).storageBytes] 0 0 =
    [(0, 0, 1), (0, 1, 2), (0, 3, 16), (1, 0, 32)] := by
  decide

/-- `-0.1 : fixed8x1` is stored as the byte `0xff` (not sign-extended into
the slot) and read back as `-0.1`; the byte above keeps `0xab`. -/
example : (store ⟨0xab00, by decide⟩ 0 (by decide) (⟨-1, by decide⟩ : Fx fixed8x1)).val =
      0xabff ∧
    (load fixed8x1 ⟨0xabff, by decide⟩ 0).1 = -1 := by
  decide +kernel

end Examples

/-! ### Axiom pins -/

/--
info: 'Solidity.Language.FixedPoint.Fx.load_store' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.load_store

/--
info: 'Solidity.Language.FixedPoint.Fx.load_store_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fx.load_store_disjoint

/--
info: 'Solidity.Language.FixedPoint.place_pairwise' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms place_pairwise

end Solidity.Language.FixedPoint
