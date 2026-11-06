import Solidity.Frontend.ExpressionUniqueness.TypePrefix
import Solidity.Frontend.ExpressionUniqueness.PostfixControls
import Solidity.Frontend.ExpressionUniqueness.Refusals

/-!
# Type-prefix inhabited families and necessary-boundary countercontrols

The raw new-array/direct-new-index token collision is rejected by the ORIGINAL
certificate. It is not a certified-tree ambiguity. Concrete follower conditions
prevent improper prefix cuts; they are not new exclusions of the original goal.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def arrayTypeFamily : Nat → Syn .typeName
  | 0 => .elem .bool
  | n + 1 => .array (arrayTypeFamily n) .none

def arrayTypeTokens : Nat → List Tok
  | 0 => [.elem .bool]
  | n + 1 => arrayTypeTokens n ++ [.punct .lbrack, .punct .rbrack]

theorem arrayTypeFamily_prec (n : Nat) : (arrayTypeFamily n).prec = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hall : (arrayTypeFamily n).all Syn.precNode = true := (Bool.and_eq_true_iff.mp ih).2
    change (Syn.array (arrayTypeFamily n) .none).prec = true
    simp only [Syn.prec, Syn.all, Syn.precNode, hall, Bool.and_true]

theorem arrayTypeFamily_yield (n : Nat) (rest : List Choice) :
    (arrayTypeFamily n).yield rest = some ([arrayTypeTokens n], rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((arrayTypeFamily n).yield rest).bind (fun r =>
      some ([r.1.flatten ++ pu .lbrack ++ [] ++ pu .rbrack], r.2)) = _
    rw [ih]
    simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil,
      arrayTypeTokens, pu, List.append_assoc, List.singleton_append]

theorem arrayTypeFamily_derives (n : Nat) : (arrayTypeFamily n).Derives (arrayTypeTokens n) := by
  refine ⟨[], ?_⟩
  simp only [Syn.toks, arrayTypeFamily_yield, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem arrayTypeTokens_length (n : Nat) : (arrayTypeTokens n).length = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [arrayTypeTokens, List.length_append, List.length_cons, List.length_nil, ih]
    omega

theorem arrayTypeFamily_tokens_injective (n m : Nat) (h : arrayTypeTokens n = arrayTypeTokens m) : n = m := by
  have lengths := congrArg List.length h
  rw [arrayTypeTokens_length, arrayTypeTokens_length] at lengths
  omega

theorem nil_type_boundary : TypeBoundary [] := ⟨tokenBoundary_nil _, tokenBoundary_nil _⟩

theorem array_follow_boundary_refuted (tail : List Tok) : ¬ TypeBoundary (.punct .lbrack :: tail) := by
  intro h
  have bad : isLeftSquare (.punct .lbrack) = false := h.2 (.punct .lbrack) tail rfl
  cases bad

theorem payable_follow_boundary_refuted (tail : List Tok) : ¬ TypeAtomBoundary (.kw .payable :: tail) := by
  intro h
  have bad : typeAtomForbidden (.kw .payable) = false := h (.kw .payable) tail rfl
  cases bad

theorem view_follow_boundary_refuted (tail : List Tok) : ¬ TypeAtomBoundary (.kw .view :: tail) := by
  intro h
  have bad : typeAtomForbidden (.kw .view) = false := h (.kw .view) tail rfl
  cases bad

theorem raw_new_array_index_collision (base : Syn .typeName) (length : Syn (.opt .expr)) :
    (Syn.new (.array base length)).yield = (Syn.index (.new base) length).yield := by
  simp only [Syn.yield, bind_assoc, pure_bind, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

theorem raw_collision_direct_new_index_refused (base : Syn .typeName) (length : Syn (.opt .expr)) :
    (Syn.index (.new base) length).prec = false := by
  rfl

theorem new_arrayTypeFamily_certified (n : Nat) :
    (Syn.new (arrayTypeFamily n)).Derives (tk .new ++ arrayTypeTokens n) ∧
      (Syn.new (arrayTypeFamily n)).prec = true := by
  have hall : (arrayTypeFamily n).all Syn.precNode = true :=
    (Bool.and_eq_true_iff.mp (arrayTypeFamily_prec n)).2
  constructor
  · refine ⟨[], ?_⟩
    apply (expr_toks_iff _ [] _).mpr
    change ((arrayTypeFamily n).yield []).bind (fun r => some ([tk .new ++ r.1.flatten], r.2)) = _
    rw [arrayTypeFamily_yield]
    simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil]
  · simp only [Syn.prec, Syn.all, Syn.precNode, hall, Bool.true_and]

end Solidity.Frontend.ExpressionUniqueness
