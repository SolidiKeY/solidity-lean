import Solidity.Frontend.C3Exactness.Trace

/-!
# Kernel controls for exact C3 merge

Arbitrary identity and prefix-length families accompany inhabited tests. All
concrete reductions use the kernel (`decide`), never `native_decide`.
-/
namespace Solidity.Frontend.C3Exactness.Controls
open Solidity.Source
variable {α : Type} [DecidableEq α]

/-- The only legal head occurs after an arbitrary number of blocked candidates. -/
def choiceFamily (n : Nat) (a b : α) : List (List α) :=
  List.replicate n [a] ++ [[b, a]]

theorem blocked_prefix (n : Nat) (a b : α) :
    admissible (choiceFamily n a b) a = false := by
  simp only [admissible, choiceFamily, List.drop_one, List.contains_eq_mem, List.all_append,
      List.all_replicate, List.tail_cons, List.not_mem_nil, decide_false, Bool.not_false, ite_self,
      List.all_cons, List.mem_cons, or_false, decide_true, Bool.not_true, List.all_nil, Bool.and_true,
      Bool.and_false]

theorem legal_last (n : Nat) (a b : α) (hne : a ≠ b) :
    admissible (choiceFamily n a b) b = true := by
  simp only [admissible, choiceFamily, List.drop_one, List.contains_eq_mem, List.all_append,
      List.all_replicate, List.tail_cons, List.not_mem_nil, decide_false, Bool.not_false, ite_self,
      List.all_cons, List.mem_cons, Ne.symm hne, or_self, List.all_nil, Bool.and_self]

/-- Every head position is exercised by an arbitrary-length kernel theorem. -/
theorem every_head_position (n : Nat) (a b : α) (hne : a ≠ b) :
    first (choiceFamily n a b) = some b := by
  change (List.replicate n [a] ++ [[b, a]]).findSome?
    (fun l => l.head?.filter (admissible (choiceFamily n a b))) = some b
  simp only [List.findSome?_append, List.head?_cons, Option.isNone_filter, Option.all_some,
      blocked_prefix, Bool.not_false, List.findSome?_replicate_of_isNone, Option.isSome_filter,
      Option.any_some, legal_last n a b hne, List.findSome?_cons_of_isSome, Option.none_or,
      Option.filter_eq_some_iff, and_self]

/-- A two-way precedence cycle obstructs every identity type. -/
theorem cycle_obstruction (a b : α) : Obstruction [[a, b], [b, a]] := by
  simp only [Obstruction, active, ne_eq, decide_not, reduceCtorEq, decide_false, Bool.not_false,
      List.filter_cons_of_pos, List.filter_nil, not_false_eq_true, first, List.head?_cons,
      Option.isNone_filter, admissible, List.drop_one, List.contains_eq_mem, List.all_cons,
      List.tail_cons, List.mem_cons, List.not_mem_nil, or_false, List.all_nil, Bool.and_true,
      Bool.not_and, Bool.not_not, Option.all_some, decide_true, Bool.or_true,
      List.findSome?_cons_of_isNone, Bool.true_or, List.findSome?_nil, and_self]

/-- Repeating an identity within one input list is an obstruction. -/
theorem duplicate_obstruction (a : α) : Obstruction [[a, a]] := by
  simp only [Obstruction, active, ne_eq, decide_not, reduceCtorEq, decide_false, Bool.not_false,
      List.filter_cons_of_pos, List.filter_nil, List.cons_ne_self, not_false_eq_true, first,
      List.head?_cons, Option.isNone_filter, admissible, List.drop_one, List.contains_eq_mem,
      List.all_cons, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false, List.all_nil,
      Bool.and_true, Bool.not_not, Option.all_some, decide_true, List.findSome?_cons_of_isNone,
      List.findSome?_nil, and_self]

/-- The generic relation is inhabited at declaration-position identities. -/
theorem identity_trace : Trace ([[1], [2, 1]] : List (List Nat)) [2, 1] :=
  .step (by decide) (.step (by decide) (.done (by decide)))

/-- A closed witness instantiates the arbitrary blocked-prefix family. -/
theorem last_head_control : first (choiceFamily 8 (1 : Nat) 2) = some 2 :=
  every_head_position 8 1 2 (by decide)

theorem empty_zero_fuel : Env.merge 0 [] = none := rfl
theorem empty_one_fuel : Env.merge 1 [] = some [] := rfl
theorem singleton_insufficient : Env.merge 1 [["a"]] = none := by decide
theorem singleton_sufficient : Env.merge 2 [["a"]] = some ["a"] := by decide

theorem independent_heads : Trace [["a"], ["b"]] ["a", "b"] :=
  (merge_bound_iff _ _).mp (by decide)

/-- Choosing a later legal head is refused by exact deterministic C3. -/
theorem later_head_refused : ¬ Trace [["a"], ["b"]] ["b", "a"] := by
  intro ht
  have he := independent_heads.unique ht
  exact (by decide : ["a", "b"] ≠ ["b", "a"]) he

/-- Shared ancestors are removed globally across all input lists. -/
theorem diamond_merge : Trace [["B", "A"], ["C", "A"], ["B", "C"]] ["B", "C", "A"] :=
  (merge_bound_iff _ _).mp (by decide)

theorem repeated_shared_merge :
    Trace [["C", "A"], ["B", "A"], ["C", "B"], ["A"], []] ["C", "B", "A"] :=
  (merge_bound_iff _ _).mp (by decide)

/-- Genuine obstruction is fuel-independent, unlike the singleton boundary. -/
theorem cycle_refused (n : Nat) : Env.merge n [["a", "b"], ["b", "a"]] = none :=
  (Stuck.here (cycle_obstruction "a" "b")).merge_none n

/-- A fresh legal head may precede a genuine obstruction; both Stuck constructors are inhabited. -/
theorem delayed_obstruction (p a b : α) (hpa : p ≠ a) (hpb : p ≠ b) :
    Stuck [[p], [a, b], [b, a]] := by
  apply Stuck.step (h := p)
  · simp only [first, active, ne_eq, decide_not, List.cons_ne_self, decide_false, Bool.not_false,
      List.filter_cons_of_pos, reduceCtorEq, List.filter_nil, List.head?_cons, Option.isSome_filter,
      Option.any_some, admissible, List.drop_one, List.contains_eq_mem, List.all_cons, List.tail_cons,
      List.not_mem_nil, List.mem_cons, hpb, or_self, hpa, List.all_nil, Bool.and_self,
      List.findSome?_cons_of_isSome, Option.filter_eq_some_iff, and_self]
  · apply Stuck.here
    simp only [Obstruction, active, ne_eq, decide_not, residual, List.cons_ne_self, decide_false,
        Bool.not_false, List.filter_cons_of_pos, reduceCtorEq, List.filter_nil, List.map_cons,
        decide_true, Bool.not_true, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg,
        Ne.symm hpa, Ne.symm hpb, List.map_nil, first, List.head?_cons, Option.isNone_filter,
        admissible, List.drop_one, List.contains_eq_mem, List.all_cons, List.tail_cons, List.mem_cons,
        List.not_mem_nil, or_false, List.all_nil, Bool.and_true, Bool.not_and, Bool.not_not,
        Option.all_some, Bool.or_true, List.findSome?_cons_of_isNone, Bool.true_or,
        List.findSome?_nil, and_self]

/-- A closed delayed-obstruction control fails at every fuel, including after a legal step. -/
theorem delayed_refused (n : Nat) :
    Env.merge n [["p"], ["a", "b"], ["b", "a"]] = none :=
  (delayed_obstruction "p" "a" "b" (by decide) (by decide)).merge_none n

/-- Closed terminal trace witness for the done constructor. -/
theorem empty_trace : Trace ([] : List (List String)) [] := .done rfl

/-- Closed immediate obstruction witness, distinct from delayed propagation. -/
theorem cycle_stuck : Stuck [["a", "b"], ["b", "a"]] := .here (cycle_obstruction "a" "b")

end Solidity.Frontend.C3Exactness.Controls
