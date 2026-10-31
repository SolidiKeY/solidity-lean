import Solidity.Backend.Creation.Artifact

/-! Bounded patch regions, using the committed assembler's byte overwrite. -/
namespace Solidity.Backend.Creation

structure Location (total width : Nat) where
  offset : Nat
  bounds : offset + width ≤ total
  deriving DecidableEq

def Location.Disjoint (a : Location total m) (b : Location total n) : Prop :=
  a.offset + m ≤ b.offset ∨ b.offset + n ≤ a.offset

instance (a : Location total m) (b : Location total n) : Decidable (a.Disjoint b) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem patchAt_length (code bytes : List UInt8) (off : Nat)
    (h : off + bytes.length ≤ code.length) :
    (patchAt code off bytes).length = code.length := by
  have ho : off ≤ code.length := by omega
  simp only [patchAt, List.length_append, List.length_take, Nat.min_eq_left ho,
    List.length_drop]
  omega

theorem patchAt_get (code bytes : List UInt8) (off i : Nat)
    (h : off + bytes.length ≤ code.length) :
    (patchAt code off bytes)[i]? =
      if i < off then code[i]? else
      if i < off + bytes.length then bytes[i - off]? else code[i]? := by
  have ho : off ≤ code.length := by omega
  unfold patchAt
  rw [List.append_assoc, List.getElem?_append]
  simp only [List.length_take, Nat.min_eq_left ho]
  split
  · rename_i hi
    exact List.getElem?_take_of_lt hi
  · rename_i hi
    rw [List.getElem?_append]
    by_cases hb : i < off + bytes.length
    · have hb' : i - off < bytes.length := by omega
      simp only [hb, hb', if_true]
    · have hb' : ¬ i - off < bytes.length := by omega
      simp only [hb, hb', if_false, List.getElem?_drop]
      congr 1
      omega

theorem patchAt_frame (code bytes : List UInt8) (off i : Nat)
    (h : off + bytes.length ≤ code.length) (outside : i < off ∨ off + bytes.length ≤ i) :
    (patchAt code off bytes)[i]? = code[i]? := by
  rw [patchAt_get code bytes off i h]
  rcases outside with hi | hi
  · simp only [hi, if_true]
  · have hni : ¬ i < off + bytes.length := by omega
    simp only [hni, if_false, ite_self]

/-- Disjoint assembler overwrites commute, without any byte/address assumptions. -/
theorem patchAt_commute (code a b : List UInt8) (oa ob : Nat)
    (ha : oa + a.length ≤ code.length) (hb : ob + b.length ≤ code.length)
    (disjoint : oa + a.length ≤ ob ∨ ob + b.length ≤ oa) :
    patchAt (patchAt code oa a) ob b = patchAt (patchAt code ob b) oa a := by
  apply List.ext_getElem?
  intro i
  have hab : ob + b.length ≤ (patchAt code oa a).length := by
    rw [patchAt_length _ _ _ ha]; exact hb
  have hba : oa + a.length ≤ (patchAt code ob b).length := by
    rw [patchAt_length _ _ _ hb]; exact ha
  simp only [patchAt_get (patchAt code oa a) b ob i hab,
    patchAt_get (patchAt code ob b) a oa i hba,
    patchAt_get code a oa i ha, patchAt_get code b ob i hb]
  by_cases hia : i < oa <;> by_cases hib : i < ob <;>
    by_cases hia' : i < oa + a.length <;> by_cases hib' : i < ob + b.length <;>
    simp only [hia, hib, hia', hib', if_true, if_false] <;> omega

end Solidity.Backend.Creation
