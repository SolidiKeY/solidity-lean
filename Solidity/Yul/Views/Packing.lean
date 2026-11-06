import Solidity.Source.State
import Solidity.Storage.HashedLayout

/-!
# Packed field arithmetic and typed scalar codec interfaces

Storage offsets count from the least significant byte, unlike memory words.
`Storage.Loc.word` is reused; no hash injectivity is postulated. The existing
G27 layout is word-granular, so packed-field/source layout agreement is an
explicit obligation, not a replacement for that owner's layout.
-/
namespace Solidity.Yul.Views

/-- A Solidity packed scalar occupies 1–32 bytes, inside one slot. -/
structure Field where
  offset : Nat
  width : Nat
  positive : 0 < width
  fits : offset + width ≤ 32

def Field.base (f : Field) : Nat := 256 ^ f.offset
def Field.modulus (f : Field) : Nat := 256 ^ f.width
abbrev Field.Value (f : Field) := Fin f.modulus

def Field.find (f : Field) (w : Nat) : Nat := w / f.base % f.modulus

/-- Preserve both unowned low and high bits. Input value is intrinsically bounded. -/
def Field.save (f : Field) (w : Nat) (v : f.Value) : Nat :=
  w % f.base + f.base * (v.val + f.modulus * (w / f.base / f.modulus))

/-- Codec values retain the actual source type; arbitrary bit patterns may fail
 decoding (for example an invalid enum). No cast from an untyped state occurs. -/
structure ScalarCodec (D : Source.Layout) (τ : Source.STy) (f : Field) where
  encode : Source.Val D τ → f.Value
  decode : f.Value → Option (Source.Val D τ)
  decode_encode : ∀ v, decode (encode v) = some v

/-- Numeric slots are derived through the existing hashed-layout interpretation. -/
def physicalSlot (H : Storage.Pre → Nat) (l : Storage.Loc) : Roadmap.Word :=
  ⟨l.word (2 ^ 256) H, by cases l <;> exact Nat.mod_lt _ (by decide)⟩

/-- Split/recombine identity; no bit is discarded by an unchanged writeback. -/
theorem split_join (w b : Nat) : w % b + b * (w / b) = w := by
  exact Nat.mod_add_div w b

theorem Field.save_unchanged (f : Field) (w : Nat) :
    f.save w ⟨f.find w, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩ = w := by
  unfold Field.save Field.find
  rw [Nat.mod_add_div, Nat.mod_add_div]

/-- Writing a field reads back exactly its bounded value. -/
theorem Field.find_save (f : Field) (w : Nat) (v : f.Value) :
    f.find (f.save w v) = v.val := by
  have hb : 0 < f.base := Nat.pow_pos (by decide)
  unfold Field.find Field.save
  rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt (Nat.mod_lt _ hb)]
  simp only [Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt v.isLt]

/-- Bits below the field survive every update. -/
theorem Field.save_low (f : Field) (w : Nat) (v : f.Value) :
    f.save w v % f.base = w % f.base := by
  simp only [Field.save, Nat.add_mul_mod_self_left, Nat.mod_mod]

/-- Bits above the field survive every update. -/
theorem Field.save_high (f : Field) (w : Nat) (v : f.Value) :
    f.save w v / f.base / f.modulus = w / f.base / f.modulus := by
  have hb : 0 < f.base := Nat.pow_pos (by decide)
  have hm : 0 < f.modulus := Nat.pow_pos (by decide)
  unfold Field.save
  rw [Nat.add_mul_div_left _ _ hb,
    Nat.div_eq_of_lt (Nat.mod_lt _ hb), Nat.zero_add,
    Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt v.isLt,
    Nat.zero_add]

/-- Packed updates stay words: `fits` prevents overflow into bit 256. -/
theorem Field.save_lt (f : Field) (w : Nat) (hw : w < 256 ^ 32) (v : f.Value) :
    f.save w v < 256 ^ 32 := by
  have he : f.base * f.modulus * 256 ^ (32 - (f.offset + f.width)) = 256 ^ 32 := by
    unfold Field.base Field.modulus
    rw [← Nat.pow_add, ← Nat.pow_add, Nat.add_sub_of_le f.fits]
  have hd : f.save w v / 256 ^ 32 = w / 256 ^ 32 := by
    rw [← he, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      Field.save_high, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, he]
    rw [← Nat.mul_assoc, he]
  exact Nat.lt_of_div_eq_zero (Nat.pow_pos (by decide)) (hd.trans (Nat.div_eq_of_lt hw))

/-- The physical packed update is intrinsically word-sized. -/
def Field.saveWord (f : Field) (w : Roadmap.Word) (v : f.Value) : Roadmap.Word :=
  ⟨f.save w.val v, f.save_lt w.val w.isLt v⟩

def Field.findWord (f : Field) (w : Roadmap.Word) : f.Value :=
  ⟨f.find w.val, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩

theorem Field.find_saveWord (f : Field) (w : Roadmap.Word) (v : f.Value) :
    f.findWord (f.saveWord w v) = v := by
  apply Fin.ext
  exact f.find_save w.val v

theorem Field.saveWord_unchanged (f : Field) (w : Roadmap.Word) :
    f.saveWord w (f.findWord w) = w := by
  apply Fin.ext
  exact f.save_unchanged w.val

/-- Another field above the update is unchanged. -/
theorem Field.find_save_above (f g : Field) (w : Nat) (v : f.Value)
    (h : f.offset + f.width ≤ g.offset) : g.find (f.save w v) = g.find w := by
  have factor : f.base * f.modulus * 256 ^ (g.offset - (f.offset + f.width)) = g.base := by
    unfold Field.base Field.modulus
    rw [← Nat.pow_add, ← Nat.pow_add, Nat.add_sub_of_le h]
  have quotient (x : Nat) : x / g.base =
      x / f.base / f.modulus / 256 ^ (g.offset - (f.offset + f.width)) := by
    simp only [Nat.div_div_eq_div_mul, factor]
  unfold Field.find
  rw [quotient (f.save w v), Field.save_high, ← quotient w]

/-- Another field below the update is unchanged. -/
theorem Field.find_save_below (f g : Field) (w : Nat) (v : f.Value)
    (h : g.offset + g.width ≤ f.offset) : g.find (f.save w v) = g.find w := by
  have factor : g.base * g.modulus * 256 ^ (f.offset - (g.offset + g.width)) = f.base := by
    unfold Field.base Field.modulus
    rw [← Nat.pow_add, ← Nat.pow_add, Nat.add_sub_of_le h]
  have observe (x : Nat) : g.find (x % f.base) = g.find x := by
    unfold Field.find
    rw [← factor, Nat.mul_assoc, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]
  calc
    g.find (f.save w v) = g.find (f.save w v % f.base) := (observe _).symm
    _ = g.find (w % f.base) := congrArg g.find (f.save_low w v)
    _ = g.find w := observe w

theorem Field.find_save_disjoint (f g : Field) (w : Nat) (v : f.Value)
    (h : f.offset + f.width ≤ g.offset ∨ g.offset + g.width ≤ f.offset) :
    g.find (f.save w v) = g.find w := by
  rcases h with above | below
  · exact f.find_save_above g w v above
  · exact f.find_save_below g w v below

/-- A concrete codec for the existing intrinsically typed Solidity bool. -/
def boolField : Field := ⟨0, 1, by decide, by decide⟩

def boolCodec (D : Source.Layout) : ScalarCodec D .bool boolField where
  encode v := by
    cases v with
    | bool b => exact ⟨if b then 1 else 0, by cases b <;> decide⟩
    | memRef h _ | storRef h _ | cdRef h _ => cases h
  decode v := if v.val = 0 then some (.bool false)
    else if v.val = 1 then some (.bool true) else none
  decode_encode v := by
    cases v with
    | bool b => cases b <;> rfl
    | memRef h _ | storRef h _ | cdRef h _ => cases h

end Solidity.Yul.Views
