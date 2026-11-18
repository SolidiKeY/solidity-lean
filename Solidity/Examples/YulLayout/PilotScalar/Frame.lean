import Solidity.Yul.Layout.Laws
import Solidity.Yul.Layout.ScalarPilot

/-!
# Scalar pilot: the frame group of `Yul/Views/ScalarWriteback.lean`

`patchScalarSlot_other_field`, `Field.lowByte_other`,
`patchScalarSlot_unowned_byte` and `encodeScalarPath_residual`, with their
original statements, from the `frame` and `local_read` laws of `view` and the
correspondence `scalarPilot`. A slot view is read as the storage of `phys`.
-/
namespace Solidity.Examples.YulLayout.PilotScalar.Frame

open Solidity.Goals
open Solidity.Yul.Views
open Solidity.Yul.Layout

/-- The machine whose storage is `m`. -/
def phys (m : SlotView) : Shrink.Phys := ⟨m, fun _ => 0, fun _ => 0⟩

/-- Parameters to use the laws at; the scalar statements do not depend on them. -/
def params : Shrink.Params := ⟨fun _ => 0, false, .legacy⟩

/-- The Scalar correspondence at `view`. -/
theorem pilot : view.ScalarPilot := scalarPilot alloc

/-- The location of the field `f` of storage slot `slot`. -/
abbrev loc (slot : Roadmap.Word) (f : Field) : Shrink.Loc := ⟨.storage, slot.val, f.offset⟩

/-- `patchScalarSlot` is the view's write of a leaf. -/
theorem write_patch (m : SlotView) (slot : Roadmap.Word) (f : Field) (v : f.Value) :
    view.geometry.write params (.scalar f.width) (loc slot f) (.leaf v.val) (phys m) =
      some (phys (patchScalarSlot m slot f v)) := by
  have hw : 0 < f.width ∧ f.width ≤ 32 ∧ v.val < 256 ^ f.width :=
    ⟨f.positive, by have := f.fits; omega, v.isLt⟩
  simp only [Shrink.Geometry.write, if_pos hw]
  exact (pilot.scalar params .storage f slot (phys m) trivial).2.1 v

/-- Frame: a write to the field `f` of `slot` keeps every other byte of the slots. -/
theorem write_byte (m out : SlotView) (slot t : Roadmap.Word) (f : Field) (x : Shrink.Tree) (b : Nat)
    (hw : view.geometry.write params (.scalar f.width) (loc slot f) x (phys m) = some (phys out))
    (h : t ≠ slot ∨ b < f.offset ∨ f.offset + f.width ≤ b) :
    (out t).val / 256 ^ b % 256 = (m t).val / 256 ^ b % 256 := by
  refine view_laws.frame params _ _ _ _ _ hw (.slot .storage t b) fun hc => ?_
  simp only [Shrink.Geometry.cellsT] at hc
  obtain ⟨b', hb, lo, hi⟩ := ((pilot.scalar params .storage f slot (phys m) trivial).2.2 _).1 hc
  cases hb
  rcases h with h | h
  · exact h rfl
  · omega

/-- Equal low-end bytes are equal `wordByte`s at the reversed index. -/
theorem wordByte_of_byte (x y : Roadmap.Word) (i : Fin 32)
    (h : x.val / 256 ^ i.val % 256 = y.val / 256 ^ i.val % 256) :
    wordByte x (reverseByteIndex 32 i) = wordByte y (reverseByteIndex 32 i) := by
  have hi : 31 - (31 - i.val) = i.val := by have ht := i.isLt; omega
  apply UInt8.toNat_inj.mp
  simp only [wordByte, reverseByteIndex, hi, UInt8.toNat_ofNat']
  exact h

theorem patchScalarSlot_other_field (m : SlotView) (s t : Roadmap.Word) (f g : Field) (v : f.Value)
    (h : s ≠ t ∨ f.offset + f.width ≤ g.offset ∨ g.offset + g.width ≤ f.offset) :
    g.findWord (patchScalarSlot m s f v t) = g.findWord (m t) := by
  have read := view_laws.local_read params (.scalar g.width) (loc t g)
    (phys (patchScalarSlot m s f v)) (phys m) (fun c hc => by
      simp only [Shrink.Geometry.cells] at hc
      obtain ⟨b, hb, lo, hi⟩ := ((pilot.scalar params .storage g t (phys m) trivial).2.2 _).1 hc
      subst hb
      refine write_byte m _ s t f _ b (write_patch m s f v) ?_
      rcases h with h | h
      · exact Or.inl (Ne.symm h)
      · exact Or.inr (by omega))
  simp only [Shrink.Geometry.read, (pilot.scalar params .storage g t _ trivial).1, Option.map_some,
    Option.some.injEq, Shrink.Tree.leaf.injEq] at read
  exact Fin.ext read

theorem Field.lowByte_other (f : Field) (w : Roadmap.Word) (v : f.Value) (i : Fin 32)
    (h : i.val < f.offset ∨ f.offset + f.width ≤ i.val) :
    wordByte (f.saveWord w v) (reverseByteIndex 32 i) = wordByte w (reverseByteIndex 32 i) := by
  have keep := write_byte (fun _ => w) _ 0 0 f _ i.val (write_patch (fun _ => w) 0 f v) (Or.inr h)
  rw [patchScalarSlot, find_saveSlot] at keep
  exact wordByte_of_byte _ _ i keep

theorem patchScalarSlot_unowned_byte (m : SlotView) (slot : Roadmap.Word) (f : Field) (v : f.Value)
    (a : Nat) (bound : a < (2 ^ 256) * 32) (h : scalarByteUnowned slot f a) :
    slotBytes (patchScalarSlot m slot f v) a = slotBytes m a := by
  have hq : a / 32 % 2 ^ 256 = a / 32 := Nat.mod_eq_of_lt (by omega)
  refine wordByte_of_byte _ _ ⟨a % 32, _⟩ (write_byte m _ slot _ f _ (a % 32) (write_patch m slot f v) ?_)
  rcases h with h | h
  · exact Or.inl fun he => h (hq ▸ congrArg Fin.val he)
  · exact Or.inr h

theorem encodeScalarPath_residual {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s : Source.Storage D L) (residual out : SlotView) (e : encodeScalarPath p c slot s residual = some out)
    (a : Nat) (bound : a < (2 ^ 256) * 32) (h : scalarByteUnowned slot f a) :
    slotBytes out a = slotBytes residual a := by
  have write := pilot.scalarPathWrite params p c slot s .storage (phys residual) trivial
  rw [show (phys residual).slots .storage = residual from rfl, e] at write
  obtain ⟨v, _, hw⟩ := Option.bind_eq_some_iff.mp write
  have hq : a / 32 % 2 ^ 256 = a / 32 := Nat.mod_eq_of_lt (by omega)
  refine wordByte_of_byte _ _ ⟨a % 32, _⟩ (write_byte residual out slot _ f _ (a % 32) hw ?_)
  rcases h with h | h
  · exact Or.inl fun he => h (hq ▸ congrArg Fin.val he)
  · exact Or.inr h

end Solidity.Examples.YulLayout.PilotScalar.Frame
