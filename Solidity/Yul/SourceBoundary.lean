import Solidity.Source.Value
import Solidity.Yul.Words

/-! Exact representation limits of the EXISTING clean Source values.
These theorems do not prohibit dirty Yul values or establish that no state
extension is possible. They rule out lossless encodings into a BARE old bool
value and numeric-key-preserving bare bool/uint8 decoders. A typed raw overlay
or a separate intrinsic dirty-value/state extension can retain the missing bits;
the original Source.Val invariants need not and must not be weakened. -/
namespace Solidity.Yul.SourceBoundary
open Solidity.Source

theorem bool_exhaustive {D : Layout} (value : Val D .bool) :
    value = Val.bool false ∨ value = Val.bool true := by
  cases value with
  | bool flag => cases flag <;> first | exact Or.inl rfl | exact Or.inr rfl
  | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible

theorem bool_key_ne_two {D : Layout} (value : Val D .bool) :
    value.key ≠ some (2 : Int) := by
  rcases bool_exhaustive value with zero | one
  · rw [zero]
    change (some (0 : Int) : Option Int) ≠ some 2
    decide
  · rw [one]
    change (some (1 : Int) : Option Int) ≠ some 2
    decide

/-- This bound is the actual existing constructor range, not a newly imposed
assembly precondition. Dirty uint8 words remain legal in the Yul model. -/
theorem u8_key_bounds {D : Layout} (value : Val D (.int IntTy.u8)) :
    ∃ n : Int, value.key = some n ∧ 0 ≤ n ∧ n ≤ 255 := by
  cases value with
  | int value range =>
    refine ⟨value,rfl,?_⟩
    change 0 ≤ value ∧ value ≤ 255 at range
    exact range
  | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible

theorem u8_key_ne_257 {D : Layout} (value : Val D (.int IntTy.u8)) :
    value.key ≠ some (257 : Int) := by
  obtain ⟨n,key,low,high⟩ := u8_key_bounds value
  intro same
  have equal := Option.some.inj (key.symm.trans same)
  omega

theorem word_two_val : (word 2).val = 2 := by decide
theorem word_257_val : (word 257).val = 257 := by decide

/-- Canonical clean initialization works; the obstruction is retaining all
possible raw words after assembly, not encoding an already clean bool. -/
theorem clean_bool_key (D : Layout) (flag : Bool) :
    (Val.bool flag : Val D .bool).key = some ((truth flag).val : Int) := by
  cases flag <;> rfl

theorem no_bool_key_decoder (D : Layout) :
    ¬ ∃ decode : Word → Val D .bool,
      ∀ raw, (decode raw).key = some (raw.val : Int) := by
  rintro ⟨decode,preserves⟩
  have two := preserves (word 2)
  rw [word_two_val] at two
  exact bool_key_ne_two (decode (word 2)) two

theorem no_u8_key_decoder (D : Layout) :
    ¬ ∃ decode : Word → Val D (.int IntTy.u8),
      ∀ raw, (decode raw).key = some (raw.val : Int) := by
  rintro ⟨decode,preserves⟩
  have large := preserves (word 257)
  rw [word_257_val] at large
  exact u8_key_ne_257 (decode (word 257)) large

/-- Stronger than fixing a particular bool encoding: no encoding whatsoever
can make a bare old bool value retain ALL raw words. Extra typed state remains
a legitimate solution; this theorem makes no claim about such an extension. -/
theorem no_bool_retraction (D : Layout) (encode : Val D .bool → Word)
    (decode : Word → Val D .bool) : ¬ ∀ raw, encode (decode raw) = raw := by
  intro lossless
  have injective : ∀ a b, decode a = decode b → a = b := by
    intro a b same
    exact (lossless a).symm.trans ((congrArg encode same).trans (lossless b))
  rcases bool_exhaustive (decode (word 0)) with zero | zero
  <;> rcases bool_exhaustive (decode (word 1)) with one | one
  <;> rcases bool_exhaustive (decode (word 2)) with two | two
  all_goals first
    | exact (by decide : word 0 ≠ word 1) (injective _ _ (zero.trans one.symm))
    | exact (by decide : word 0 ≠ word 2) (injective _ _ (zero.trans two.symm))
    | exact (by decide : word 1 ≠ word 2) (injective _ _ (one.trans two.symm))

end Solidity.Yul.SourceBoundary
