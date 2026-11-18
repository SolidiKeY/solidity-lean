import Solidity.Yul.Layout.Laws
import Solidity.Yul.Layout.ScalarPilot
import Solidity.Examples.YulLayout.PilotScalar.Frame

/-!
# Scalar pilot: the path group of `Yul/Views/ScalarWriteback.lean`

`patchScalarSlot_find`, `encodeScalarPath_view`,
`canonicalPathWriteback_unchanged`, `canonicalPathWriteback_result_view` and
`encodeScalarPath_unchanged`, with their original statements, from the
`write_read` and `frame` laws of `view` and the correspondence `scalarPilot`.
The source-side facts (`canonicalScalarDecode_*`, `preserveScalarWrite_*`) do
not mention a physical view and are used from the original file.
-/
namespace Solidity.Examples.YulLayout.PilotScalar.Path

open Solidity.Goals
open Solidity.Yul.Views
open Solidity.Yul.Layout
open Solidity.Examples.YulLayout.PilotScalar.Frame

/-- Read after write of a field value: the view reads the leaf back. -/
theorem read_written (m out : SlotView) (slot : Roadmap.Word) (f : Field) (v : f.Value)
    (hw : view.geometry.write params (.scalar f.width) (loc slot f) (.leaf v.val) (phys m) =
      some (phys out)) : f.findWord (out slot) = v := by
  have read := view_laws.write_read params _ _ _ _ _
    (by simp only [Shrink.Layout.Fits]; exact ⟨f.positive, by have := f.fits; omega, v.isLt⟩) hw
    (by simp only [Shrink.Geometry.Separated])
  simp only [Shrink.Geometry.read, (pilot.scalar params .storage f slot _ trivial).1, Option.map_some,
    Option.some.injEq, Shrink.Tree.leaf.injEq] at read
  exact Fin.ext read

/-- The path view, read through the view: the path holds the value of the field. -/
theorem path_read {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s : Source.Storage D L) (m : SlotView) :
    scalarPathView p c slot s m ↔ ∃ v, s.read p = some v ∧ c.encode v = f.findWord (m slot) := by
  rw [show m = (phys m).slots .storage from rfl,
    pilot.scalarPathRead params p c slot s .storage (phys m) trivial]
  simp only [Shrink.Geometry.read, (pilot.scalar params .storage f slot _ trivial).1, Option.map_some]
  cases s.read p with
  | none => simp only [Option.map_none, reduceCtorEq, false_and, exists_false]
  | some w =>
    simp only [Option.map_some, Option.some.injEq, Shrink.Tree.leaf.injEq, exists_eq_left']
    exact ⟨Fin.ext, congrArg Fin.val⟩

theorem patchScalarSlot_find (m : SlotView) (slot : Roadmap.Word) (f : Field) (v : f.Value) :
    f.findWord (patchScalarSlot m slot f v slot) = v :=
  read_written m _ slot f v (write_patch m slot f v)

theorem encodeScalarPath_view {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s : Source.Storage D L) (residual out : SlotView) (e : encodeScalarPath p c slot s residual = some out) :
    scalarPathView p c slot s out := by
  have write := pilot.scalarPathWrite params p c slot s .storage (phys residual) trivial
  rw [show (phys residual).slots .storage = residual from rfl, e] at write
  obtain ⟨v, hr, hw⟩ := Option.bind_eq_some_iff.mp write
  exact (path_read p c slot s out).2 ⟨v, hr, (read_written residual out slot f _ hw).symm⟩

theorem canonicalPathWriteback_unchanged {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s : Source.Storage D L) (m : SlotView) (h : scalarPathView p c slot s m) :
    canonicalPathWriteback p c slot m s = some s := by
  obtain ⟨v, hr, hv⟩ := (path_read p c slot s m).1 h
  unfold canonicalPathWriteback
  rw [← hv, canonicalScalarDecode_encode]
  simp only [Option.map_some, preserveScalarWrite_unchanged p c v s hr]

theorem canonicalPathWriteback_result_view {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s s' : Source.Storage D L) (m : SlotView) (e : canonicalPathWriteback p c slot m s = some s') :
    scalarPathView p c slot s' m := by
  obtain ⟨v, hd, he⟩ := Option.map_eq_some_iff.mp e
  subst s'
  exact (path_read p c slot _ m).2
    ⟨v, preserveScalarWrite_read p c v s, (canonicalScalarDecode_sound c _ v hd).2⟩

/-- A base-256 digit below `w` survives reduction modulo `256 ^ w`. -/
theorem digit_mod (y w j : Nat) (h : j < w) : y % 256 ^ w / 256 ^ j % 256 = y / 256 ^ j % 256 := by
  have factor : 256 ^ w = 256 ^ j * (256 * 256 ^ (w - (j + 1))) := by
    rw [← Nat.pow_succ', ← Nat.pow_add]
    congr 1
    omega
  rw [factor, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]

/-- Numbers with the same `k` low base-256 digits agree modulo `256 ^ k`. -/
theorem mod_of_digits (x y k : Nat) (h : ∀ b, b < k → x / 256 ^ b % 256 = y / 256 ^ b % 256) :
    x % 256 ^ k = y % 256 ^ k := by
  induction k with
  | zero => simp only [Nat.pow_zero, Nat.mod_one]
  | succ k ih =>
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, ih (fun b hb => h b (by omega)), h k (Nat.lt_succ_self k)]

/-- Writing the value a field already holds changes no slot: the bytes outside
the field by `frame`, the bytes inside by `write_read`. The laws have no
write-of-the-read-value identity, so this goes through the 32 bytes of a word. -/
theorem write_same (m out : SlotView) (slot : Roadmap.Word) (f : Field)
    (hw : view.geometry.write params (.scalar f.width) (loc slot f) (.leaf (f.findWord (m slot)).val)
      (phys m) = some (phys out)) : out = m := by
  funext t
  have digits : ∀ b, b < 32 → (out t).val / 256 ^ b % 256 = (m t).val / 256 ^ b % 256 := by
    intro b _
    by_cases own : t = slot ∧ f.offset ≤ b ∧ b < f.offset + f.width
    · obtain ⟨rfl, lo, hi⟩ := own
      have same := congrArg (fun x : f.Value => x.val / 256 ^ (b - f.offset) % 256)
        (read_written m out t f _ hw)
      simp only [Field.findWord, Field.find, Field.base, Field.modulus] at same
      rw [digit_mod _ _ _ (by omega), digit_mod _ _ _ (by omega), Nat.div_div_eq_div_mul,
        Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_sub_cancel' lo] at same
      exact same
    · refine write_byte m out slot t f _ b hw ?_
      by_cases ht : t = slot
      · exact Or.inr (Decidable.byContradiction fun hn => own ⟨ht, by omega, by omega⟩)
      · exact Or.inl ht
  have e := mod_of_digits _ _ 32 digits
  rw [Nat.mod_eq_of_lt (out t).isLt, Nat.mod_eq_of_lt (m t).isLt] at e
  exact Fin.ext e

theorem encodeScalarPath_unchanged {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s : Source.Storage D L) (m : SlotView) (h : scalarPathView p c slot s m) :
    encodeScalarPath p c slot s m = some m := by
  obtain ⟨v, hr, hv⟩ := (path_read p c slot s m).1 h
  have write := pilot.scalarPathWrite params p c slot s .storage (phys m) trivial
  rw [hr, Option.bind_some, hv, write_patch] at write
  cases he : encodeScalarPath p c slot s m with
  | none => rw [show (phys m).slots .storage = m from rfl, he] at write; cases write
  | some out =>
    rw [show (phys m).slots .storage = m from rfl, he] at write
    have eq : patchScalarSlot m slot f (f.findWord (m slot)) = out :=
      congrArg Shrink.Phys.storage (Option.some.inj write)
    rw [← eq, write_same m _ slot f (write_patch m slot f _)]

end Solidity.Examples.YulLayout.PilotScalar.Path
