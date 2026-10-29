import Solidity.Evm.Machine
import Solidity.Storage.HashedLayout

/-!
# The hashed layout's slot terms and the EVM model's `Slot`

A read-only correspondence: `Solidity.Evm.Slot` (`Solidity/Evm/Machine.lean`,
not edited here) and `Solidity.Storage.Loc` have the same three shapes, with
a `Slot`'s mapping key a word (`Fin W`) and a `Loc`'s a `Nat`. `ofSlot` is
injective, commutes with adding to the offset, and reaches exactly the terms
whose keys are words (`KeysBelow W`). So the separation theorems of
`HashedLayout.lean` apply to the EVM model's slots read through
`Loc.word W H ∘ ofSlot`, and `lmax` is the EVM model's `Lmax`.
-/

namespace Solidity.Storage

open Solidity.Evm (Slot W Lmax)

/-- The slot term of an EVM slot. -/
def ofSlot : Slot → Loc
  | .root o => .root o
  | .hash k s o => .hash k.val (ofSlot s) o
  | .data s o => .data (ofSlot s) o

theorem ofSlot_injective : ∀ {s t : Slot}, ofSlot s = ofSlot t → s = t
  | .root _, .root _, h => by cases h; rfl
  | .hash k s o, .hash k' t o', h => by
    simp only [ofSlot, Loc.hash.injEq] at h
    obtain ⟨hk, hs, rfl⟩ := h
    rw [Fin.ext hk, ofSlot_injective hs]
  | .data s o, .data t o', h => by
    simp only [ofSlot, Loc.data.injEq] at h
    obtain ⟨hs, rfl⟩ := h
    rw [ofSlot_injective hs]
  | .root _, .hash _ _ _, h => by cases h
  | .root _, .data _ _, h => by cases h
  | .hash _ _ _, .root _, h => by cases h
  | .hash _ _ _, .data _ _, h => by cases h
  | .data _ _, .root _, h => by cases h
  | .data _ _, .hash _ _ _, h => by cases h

theorem ofSlot_add (s : Slot) (i : Nat) : ofSlot (s.add i) = (ofSlot s).add i := by
  cases s <;> rfl

/-- Every mapping key of the term is below `n`. -/
def KeysBelow (n : Nat) : Loc → Prop
  | .root _ => True
  | .hash k s _ => k < n ∧ KeysBelow n s
  | .data s _ => KeysBelow n s

theorem keysBelow_ofSlot : ∀ s : Slot, KeysBelow W (ofSlot s)
  | .root _ => trivial
  | .hash k s _ => ⟨k.isLt, keysBelow_ofSlot s⟩
  | .data s _ => keysBelow_ofSlot s

/-- The terms with word keys are exactly the EVM slots. -/
theorem exists_ofSlot : ∀ {l : Loc}, KeysBelow W l → ∃ s : Slot, ofSlot s = l
  | .root o, _ => ⟨.root o, rfl⟩
  | .hash k l o, h => by
    obtain ⟨s, hs⟩ := exists_ofSlot h.2
    exact ⟨.hash ⟨k, h.1⟩ s o, by simp only [ofSlot, hs]⟩
  | .data l o, h => by
    have hl : KeysBelow W l := h
    obtain ⟨s, hs⟩ := exists_ofSlot hl
    exact ⟨.data s o, by simp only [ofSlot, hs]⟩

theorem lmax_eq_Lmax : lmax = Lmax := rfl

/-- Separation read on EVM slots: under the run's region premise, two bounded
slots whose preimages the run hashed are one word only if they are one slot. -/
theorem slot_word_inj {L R : Nat} {H : Pre → Nat} {P : List Pre} (hH : ∀ p, H p < W)
    (hL : L ≤ W) (hR : R ≤ W) (hRD : Solidity.Hash.RegionsDisjoint W L H (List.range R) P)
    {s t : Slot} (hs : Loc.Bounded L R (ofSlot s)) (ht : Loc.Bounded L R (ofSlot t))
    (hPs : ∀ p ∈ Loc.pres W H (ofSlot s), p ∈ P) (hPt : ∀ p ∈ Loc.pres W H (ofSlot t), p ∈ P)
    (h : Loc.word W H (ofSlot s) = Loc.word W H (ofSlot t)) : s = t :=
  ofSlot_injective (Loc.word_inj hH hL hR hRD _ _ hs ht hPs hPt h)

end Solidity.Storage

/-- info: 'Solidity.Storage.slot_word_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Storage.slot_word_inj
