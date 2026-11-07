import Solidity.Frontend.ExpressionUniqueness.ContainerIdentity
import Solidity.Frontend.ExpressionUniqueness.PostfixControls

/-!
# Arbitrary optional-hole vector identity and flattened collision control

Full item vectors determine these intrinsic lists against any certified list.
Flattening erases their holes, so list recursion must retain vector boundaries.
This is a list-word collision, not an expression ambiguity.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem optionalHoles_vector_unique (n : Nat) : VectorUnique (optionalHoles n) := by
  induction n with
  | zero => exact nil_vector_unique (.opt .expr)
  | succ n ih => exact cons_vector_unique Syn.none (optionalHoles n) none_expr_word_unique ih

theorem optionalHoles_prec (n : Nat) : (optionalHoles n).prec = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hall : (optionalHoles n).all Syn.precNode = true := (Bool.and_eq_true_iff.mp ih).2
    change (true && (true && true && (optionalHoles n).all Syn.precNode)) = true
    rw [hall]
    rfl

theorem optionalHoles_actual_vector_identity (n : Nat) (other : Syn (.list (.opt .expr)))
    (initial final : List Choice) (hp : other.prec = true)
    (hy : other.yield initial = some (List.replicate n [], final)) : other = optionalHoles n := by
  exact (optionalHoles_vector_unique n other [] [] initial final (List.replicate n [])
    (List.replicate n []) (optionalHoles_prec n) hp (optionalHoles_yield n []) hy rfl).symm

theorem optionalHoles_flatten_collision (n : Nat) : (List.replicate n ([] : List Tok)).flatten = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [List.replicate_succ, List.flatten_cons, List.nil_append] using ih

end Solidity.Frontend.ExpressionUniqueness
