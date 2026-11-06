import Solidity.Frontend.ExpressionUniqueness.AllRootLevels

/-!
# Structural induction predicates over existing intrinsic syntax

Word comparison is appropriate for individual expressions/types/arguments.
List comparison retains item boundaries, including empty tuple components.
These predicates organize recursive induction; no public uniqueness instance or
new producer assumption is asserted here.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def WordUnique {c : Cat} (e : Syn c) : Prop :=
  ∀ (other : Syn c) (initial final initial' final' : List Choice) (items items' : List (List Tok)),
    e.prec = true → other.prec = true →
    e.yield initial = some (items, final) → other.yield initial' = some (items', final') →
    items.flatten = items'.flatten → e = other

def VectorUnique {c : Cat} (e : Syn c) : Prop :=
  ∀ (other : Syn c) (initial final initial' final' : List Choice) (items items' : List (List Tok)),
    e.prec = true → other.prec = true →
    e.yield initial = some (items, final) → other.yield initial' = some (items', final') →
    items = items' → e = other

def RecursiveYieldProperty {c : Cat} (e : Syn c) : Prop :=
  match c with
  | .expr | .typeName | .param | .namedArg | .callArgs | .opt .expr => WordUnique e
  | .list .expr | .list .param | .list .namedArg | .list (.opt .expr) => VectorUnique e
  | _ => True

theorem list_prec_children {c : Cat} (head : Syn c) (tail : Syn (.list c))
    (hp : (Syn.cons head tail).prec = true) : head.prec = true ∧ tail.prec = true := by
  have hall : (Syn.cons head tail).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.cons head tail).precNode && head.all Syn.precNode && tail.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec head (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec tail (Bool.and_eq_true_iff.mp hall).2⟩

theorem some_prec_child {c : Cat} (child : Syn c) (hp : (Syn.some child).prec = true) :
    child.prec = true := by
  have hall : (Syn.some child).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.some child).precNode && child.all Syn.precNode) = true at hall
  exact all_prec_implies_prec child (Bool.and_eq_true_iff.mp hall).2

end Solidity.Frontend.ExpressionUniqueness
