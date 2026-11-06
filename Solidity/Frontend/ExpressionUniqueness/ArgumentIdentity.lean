import Solidity.Frontend.ExpressionUniqueness.ContainerIdentity
import Solidity.Frontend.ExpressionUniqueness.ArgumentSpans
import Solidity.Frontend.ExpressionUniqueness.MemberSpans

/-!
# Intrinsic argument identity induction steps

Actual word-vector and name cuts are derived by the existing span theorems.
Recursive premises are exactly the structural predicates for the existing child
nodes. No parser, global uniqueness or desired split is assumed.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem namedArg_prec_child (name : String) (value : Syn .expr)
    (hp : (Syn.namedArg name value).prec = true) : value.prec = true := by
  have hall : (Syn.namedArg name value).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.namedArg name value).precNode && value.all Syn.precNode) = true at hall
  exact all_prec_implies_prec value (Bool.and_eq_true_iff.mp hall).2

theorem positional_prec_child (args : Syn (.list .expr))
    (hp : (Syn.positional args).prec = true) : args.prec = true := by
  have hall : (Syn.positional args).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.positional args).precNode && args.all Syn.precNode) = true at hall
  exact all_prec_implies_prec args (Bool.and_eq_true_iff.mp hall).2

theorem named_prec_child (args : Syn (.list .namedArg))
    (hp : (Syn.named args).prec = true) : args.prec = true := by
  have hall : (Syn.named args).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.named args).precNode && args.all Syn.precNode) = true at hall
  exact all_prec_implies_prec args (Bool.and_eq_true_iff.mp hall).2

theorem namedArg_word_unique (name : String) (value : Syn .expr) (ih : WordUnique value) :
    WordUnique (Syn.namedArg name value) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  cases other with
  | namedArg name' value' =>
    obtain ⟨names, xs, ys, hx, hyb, childWords⟩ :=
      namedArg_child_spans name name' value value' initial final initial' final' items items' hy hy' words
    have child : value = value' := ih value' initial final initial' final' xs ys
      (namedArg_prec_child name value hp) (namedArg_prec_child name' value' hp') hx hyb childWords
    rw [names, child]

theorem positional_word_unique (args : Syn (.list .expr)) (ih : VectorUnique args) :
    WordUnique (Syn.positional args) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  cases other with
  | positional args' =>
    obtain ⟨xs, ys, hx, hyb, vectors⟩ :=
      positional_argument_spans args args' initial final initial' final' items items' hy hy' words
    have equal : args = args' := ih args' initial final initial' final' xs ys
      (positional_prec_child args hp) (positional_prec_child args' hp') hx hyb vectors
    rw [equal]
  | named args' =>
    exact (positional_named_yields_disjoint args args' initial final initial' final' items items' hy hy' words).elim

theorem named_word_unique (args : Syn (.list .namedArg)) (ih : VectorUnique args) :
    WordUnique (Syn.named args) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  cases other with
  | named args' =>
    obtain ⟨xs, ys, hx, hyb, vectors⟩ :=
      named_argument_spans args args' initial final initial' final' items items' hy hy' words
    have equal : args = args' := ih args' initial final initial' final' xs ys
      (named_prec_child args hp) (named_prec_child args' hp') hx hyb vectors
    rw [equal]
  | positional args' =>
    exact (positional_named_yields_disjoint args' args initial' final' initial final items' items hy' hy words.symm).elim

end Solidity.Frontend.ExpressionUniqueness
