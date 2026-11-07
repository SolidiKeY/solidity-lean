import Solidity.Frontend.ExpressionUniqueness.RecursiveProperty

/-!
# Intrinsic list and optional-expression identity steps

The only recursive premises are the structural induction predicates for actual
children. Lists retain the full item vector, so empty optional components are
never silently erased. None/some separation derives actual expression nonemptiness.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem nil_vector_unique (c : Cat) : VectorUnique (Syn.nil (c := c)) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  cases other with
  | nil => rfl
  | cons head tail =>
    have empty : items = [] := (pure_success_split [] items initial final hy).1
    obtain ⟨xs, ys, middle, hx, ht, shape⟩ := pair_pure_success_split head.yield tail.yield
      (fun xs ys => xs.flatten :: ys) initial' final' items' hy'
    rw [empty, shape] at words
    cases words

theorem cons_vector_unique {c : Cat} (head : Syn c) (tail : Syn (.list c))
    (ihHead : WordUnique head) (ihTail : VectorUnique tail) : VectorUnique (Syn.cons head tail) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  obtain ⟨xs, ys, middle, hx, ht, shape⟩ := pair_pure_success_split head.yield tail.yield
    (fun xs ys => xs.flatten :: ys) initial final items hy
  cases other with
  | nil =>
    have empty : items' = [] := (pure_success_split [] items' initial' final' hy').1
    rw [shape, empty] at words
    cases words
  | cons head' tail' =>
    obtain ⟨xs', ys', middle', hx', ht', shape'⟩ := pair_pure_success_split head'.yield tail'.yield
      (fun xs ys => xs.flatten :: ys) initial' final' items' hy'
    rw [shape, shape'] at words
    obtain ⟨heads, tails⟩ := List.cons.inj words
    obtain ⟨hph, hpt⟩ := list_prec_children head tail hp
    obtain ⟨hph', hpt'⟩ := list_prec_children head' tail' hp'
    have eh : head = head' := ihHead head' initial middle initial' middle' xs xs' hph hph' hx hx' heads
    have et : tail = tail' := ihTail tail' middle final middle' final' ys ys' hpt hpt' ht ht' tails
    rw [eh, et]

theorem none_expr_word_unique : WordUnique (Syn.none (c := .expr)) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have empty : items = [] := (pure_success_split [] items initial final hy).1
  cases other with
  | none => rfl
  | some child =>
    obtain ⟨xs, hx, shape⟩ := one_pure_success_split child.yield (fun xs => [xs.flatten]) initial' final' items' hy'
    have nonempty : xs.flatten ≠ [] := nonemptyItem_flatten (expr_yield_nonempty child initial' xs final' hx)
    rw [empty, shape] at words
    simp only [List.flatten_nil, List.flatten_cons, List.append_nil] at words
    exact (nonempty words.symm).elim

theorem some_expr_word_unique (child : Syn .expr) (ih : WordUnique child) : WordUnique (Syn.some child) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  obtain ⟨xs, hx, shape⟩ := one_pure_success_split child.yield (fun xs => [xs.flatten]) initial final items hy
  cases other with
  | none =>
    have empty : items' = [] := (pure_success_split [] items' initial' final' hy').1
    have nonempty : xs.flatten ≠ [] := nonemptyItem_flatten (expr_yield_nonempty child initial xs final hx)
    rw [shape, empty] at words
    simp only [List.flatten_nil, List.flatten_cons, List.append_nil] at words
    exact (nonempty words).elim
  | some child' =>
    obtain ⟨xs', hx', shape'⟩ := one_pure_success_split child'.yield (fun xs => [xs.flatten]) initial' final' items' hy'
    rw [shape, shape'] at words
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at words
    have equal : child = child' := ih child' initial final initial' final' xs xs'
      (some_prec_child child hp) (some_prec_child child' hp') hx hx' words
    rw [equal]

end Solidity.Frontend.ExpressionUniqueness
