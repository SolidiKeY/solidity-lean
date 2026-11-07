import Solidity.Frontend.ExpressionUniqueness.MappingIdentity
import Solidity.Frontend.ExpressionUniqueness.TypePrefixControls

/-!
# Unconditional identity controls for arbitrary intrinsic type families

Structural induction discharges every recursive premise for arbitrary array
depths. The result compares against any certified type tree, not merely another
member of the family. Existing exact witnesses establish non-vacuity.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem arrayTypeFamily_word_unique (n : Nat) : WordUnique (arrayTypeFamily n) := by
  induction n with
  | zero => exact elementary_type_word_unique .bool
  | succ n ih => exact array_type_word_unique (arrayTypeFamily n) Syn.none ih none_expr_word_unique

theorem arrayTypeFamily_actual_identity (n : Nat) (other : Syn .typeName)
    (initial final : List Choice) (items : List (List Tok)) (hp : other.prec = true)
    (hy : other.yield initial = some (items, final)) (words : items.flatten = arrayTypeTokens n) :
    other = arrayTypeFamily n := by
  have ownWords : [arrayTypeTokens n].flatten = items.flatten := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using words.symm
  exact (arrayTypeFamily_word_unique n other [] [] initial final [arrayTypeTokens n] items
    (arrayTypeFamily_prec n) hp (arrayTypeFamily_yield n []) hy ownWords).symm

theorem empty_function_type_word_unique (vis : Option Visibility) (mu : Option Mutability) :
    WordUnique (Syn.fnType Syn.nil vis mu Syn.nil) :=
  fn_type_word_unique Syn.nil Syn.nil vis mu (nil_vector_unique .param) (nil_vector_unique .param)

end Solidity.Frontend.ExpressionUniqueness
