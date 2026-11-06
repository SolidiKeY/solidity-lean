import Solidity.Evm.TryPanicSourceBody

/-! Six ordered updates for the bounded H8 body. These typed object functions
are proof data, not a replacement evaluator. Source execution remains the
existing Stmt/Prog run. -/
namespace Solidity.Evm.TryPanicSourceBodyImage
open TryByteImage TryPanicProducer TryPanicSourceBody
variable {C : Contract}

/-- Exactly the object in put_run, including the short-buffer branch. -/
def clipped {H : HTy} (o : MObj H bytesR) (i : Fin 96) (b : UInt8) : MObj H bytesR :=
  if i.val < o.1.length then MObj.setElem .dyn o i.val (byteWord b) else o

theorem clipped_length {H : HTy} (o : MObj H bytesR) (i : Fin 96) (b : UInt8) :
    (clipped o i b).1.length = o.1.length := by
  unfold clipped
  split <;> simp only [MObj.setElem_dyn, List.length_set]

theorem clipped_get {H : HTy} (o : MObj H bytesR) (i : Fin 96) (b : UInt8)
    (j : Nat) (hj : j < o.1.length) :
    (clipped o i b).1[j]'(by rw [clipped_length]; exact hj) =
      if j = i.val then byteWord b else o.1[j] := by
  by_cases hit : i.val < o.1.length
  · simp only [clipped, if_pos hit, MObj.setElem_dyn, List.getElem_set]
    simp only [eq_comm]
  · have different : j ≠ i.val := by omega
    simp only [clipped, if_neg hit, if_neg different]

/-- List.set is already identity out of range; this structural cut avoids
unfolding the nested typed-object guards while preserving their exact result. -/
theorem clipped_values {H : HTy} (o : MObj H bytesR) (i : Fin 96) (b : UInt8) :
    (clipped o i b).1 = o.1.set i.val (byteWord b) := by
  by_cases hit : i.val < o.1.length
  · simp only [clipped, if_pos hit, MObj.setElem_dyn]
  · simp only [clipped, if_neg hit]
    exact (List.set_eq_of_length_le (by omega)).symm

/-- Original fixed order, with no commutation of writes or fixed output length. -/
def six {H : HTy} (o : MObj H bytesR) : MObj H bytesR :=
  clipped (clipped (clipped (clipped (clipped (clipped o
    ⟨0, by decide⟩ 0x4e) ⟨1, by decide⟩ 0x48) ⟨2, by decide⟩ 0x7b)
    ⟨3, by decide⟩ 0x71) ⟨35, by decide⟩ 0x43) ⟨95, by decide⟩ 0x80

def imageObj (H : HTy) (n : Nat) (hn : n < 2^256) : MObj H bytesR :=
  six (zerosObj H n hn)

theorem six_values {H : HTy} (o : MObj H bytesR) :
    (six o).1 = (((((o.1.set 0 (byteWord 0x4e)).set 1 (byteWord 0x48)).set 2
      (byteWord 0x7b)).set 3 (byteWord 0x71)).set 35 (byteWord 0x43)).set 95 (byteWord 0x80) := by
  unfold six
  rw [clipped_values, clipped_values, clipped_values, clipped_values, clipped_values, clipped_values]

theorem zeros_length (H : HTy) (n : Nat) (hn : n < 2^256) :
    (zerosObj H n hn).1.length = n := List.length_replicate

theorem image_length (H : HTy) (n : Nat) (hn : n < 2^256) :
    (imageObj H n hn).1.length = n := by
  simp only [imageObj, six, clipped_length, zeros_length]

theorem image_get (H : HTy) (n : Nat) (hn : n < 2^256) (j : Nat) (hj : j < n) :
    (imageObj H n hn).1[j]'(by rw [image_length]; exact hj) =
      byteWord (TryPanicSourceBytes.byteAt j) := by
  simp only [imageObj, six_values, zerosObj, List.getElem_set, List.getElem_replicate]
  simp only [eq_comm]
  by_cases h0 : j = 0
  · subst j; rfl
  by_cases h1 : j = 1
  · subst j; rfl
  by_cases h2 : j = 2
  · subst j; rfl
  by_cases h3 : j = 3
  · subst j; rfl
  by_cases h35 : j = 35
  · subst j; rfl
  by_cases h95 : j = 95
  · subst j; rfl
  simp only [TryPanicSourceBytes.byteAt, if_neg h0, if_neg h1, if_neg h2,
    if_neg h3, if_neg h35, if_neg h95]
  rfl

/-- The concrete updated object is the actual generic image, not a separately
chosen buffer. No padding/serialization/provider law is needed for this core object. -/
theorem image_eq (H : HTy) (n : Nat) (hn : n < 2^256) :
    imageObj H n hn = bytesObj H (TryPanicSourceBytes.bytesAt n)
      (by rw [TryPanicSourceBytes.bytes_length]; exact hn) := by
  apply Subtype.ext
  apply List.ext_getElem
  · rw [image_length]
    simp only [List.length_map, TryPanicSourceBytes.bytes_length]
  · intro j hj hk
    rw [image_get H n hn j (by rw [image_length] at hj; exact hj)]
    simp only [List.getElem_map, TryPanicSourceBytes.bytesAt, List.getElem_ofFn]

-- Keep later sequence checking on the proved field laws, not nested if unfolding.
attribute [irreducible] clipped

end Solidity.Evm.TryPanicSourceBodyImage
