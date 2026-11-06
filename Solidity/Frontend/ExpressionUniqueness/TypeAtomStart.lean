import Solidity.Source.Ctor
import Solidity.Frontend.ExpressionUniqueness.TypeSpine

/-!
# Non-array type roots distinguish their first token classes

The classifiers inspect existing intrinsic nodes and tokens only. They recover
a root family from actual prefixes without an assumed split or tree uniqueness.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def typeAtomKind (ty : Syn .typeName) : Nat :=
  match ty.ctor with
  | .elem => 0 | .userType => 1 | .mapping => 2 | .fnType => 3 | _ => 4

def typeTokenClass : Tok → Nat
  | .elem _ => 0 | .ident _ => 1 | .kw .mapping => 2 | .kw .function => 3 | _ => 4

def TypeStart (tag : Nat) (items : List (List Tok)) : Prop :=
  ∃ token rest, items.flatten = token :: rest ∧ typeTokenClass token = tag

theorem typeAtom_yield_start (ty : Syn .typeName) (initial final : List Choice)
    (items : List (List Tok)) (atom : isTypeAtom ty = true)
    (hy : ty.yield initial = some (items, final)) : TypeStart (typeAtomKind ty) items := by
  cases ty with
  | elem e =>
    have shape : items = [e.toks] := (pure_success_split [e.toks] items initial final hy).1
    unfold TypeStart
    rw [shape]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    cases e <;> exact ⟨_, _, rfl, rfl⟩
  | userType path =>
    have shape : items = [path.toks] := (pure_success_split [path.toks] items initial final hy).1
    unfold TypeStart
    rw [shape]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨.ident path.head, _, rfl, rfl⟩
  | mapping key kn value vn =>
    obtain ⟨xs, hx, shape⟩ := mapping_type_yield_parts key kn value vn initial final items hy
    unfold TypeStart
    rw [shape]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, tk, List.singleton_append]
    exact ⟨.kw .mapping, _, rfl, rfl⟩
  | fnType params vis mu returns =>
    obtain ⟨ps, attrs, rs, hp, ha, hr, shape⟩ := fn_type_actual_attribute_run params vis mu returns initial final items hy
    unfold TypeStart
    rw [shape]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, tk,
      List.append_assoc, List.singleton_append]
    exact ⟨.kw .function, _, rfl, rfl⟩
  | array => cases atom

theorem typeAtom_prefix_kinds_equal (a b : Syn .typeName)
    (initial final initial' final' : List Choice) (items items' : List (List Tok)) (tail tail' : List Tok)
    (ha : isTypeAtom a = true) (hb : isTypeAtom b = true)
    (hy : a.yield initial = some (items, final)) (hy' : b.yield initial' = some (items', final'))
    (words : items.flatten ++ tail = items'.flatten ++ tail') : typeAtomKind a = typeAtomKind b := by
  obtain ⟨token, rest, shape, code⟩ := typeAtom_yield_start a initial final items ha hy
  obtain ⟨token', rest', shape', code'⟩ := typeAtom_yield_start b initial' final' items' hb hy'
  rw [shape, shape'] at words
  have tokens : token = token' := (List.cons.inj words).1
  exact code.symm.trans ((congrArg typeTokenClass tokens).trans code')

end Solidity.Frontend.ExpressionUniqueness
