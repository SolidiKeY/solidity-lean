import Solidity.Storage.Representation.Model

/-! Full-word normalization for the committed primitive/key types.
No packed-field layout or new arithmetic interface is introduced. -/
namespace Solidity.Storage.Representation

def keyWord {p : PrimTy} (k : p.Denote) : Nat := (PrimTy.toWord k).val.toNat

theorem keyWord_lt {p : PrimTy} (k : p.Denote) : keyWord k < 2 ^ 256 := by
  have h : PrimTy.inRange .uint (PrimTy.toWord k).val = true := (PrimTy.toWord k).property
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  unfold keyWord
  omega

/-- The approved full-word normalization is idempotent on supported values. -/
theorem word_normalized {p : PrimTy} (v : p.Denote) :
    keyWord v % 2 ^ 256 = keyWord v := Nat.mod_eq_of_lt (keyWord_lt v)

/-- Distinct keys of the same supported type have distinct padded words.
This is a value-encoding fact, not an assumption about hash outputs. -/
theorem keyWord_inj {p : PrimTy} {a b : p.Denote} (h : keyWord a = keyWord b) : a = b := by
  cases p with
  | bool =>
    cases a <;> cases b <;> first | rfl | (simp only [keyWord, PrimTy.toWord, cond_true, cond_false] at h; omega)
  | uint =>
    apply Subtype.ext
    have ha : 0 ≤ a.val := PrimTy.uint_nonneg a
    have hb : 0 ≤ b.val := PrimTy.uint_nonneg b
    change a.val.toNat = b.val.toNat at h
    omega
  | int =>
    apply Subtype.ext
    have ha : PrimTy.inRange .int a.val = true := a.property
    have hb : PrimTy.inRange .int b.val = true := b.property
    simp only [PrimTy.inRange, decide_eq_true_eq] at ha hb
    by_cases hna : 0 ≤ a.val <;> by_cases hnb : 0 ≤ b.val <;>
      simp only [keyWord, PrimTy.toWord, hna, hnb, ↓reduceDIte] at h <;> omega

end Solidity.Storage.Representation
