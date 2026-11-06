import Solidity.Frontend.ExpressionUniqueness.Primary

/-!
# Structural facts about successful intrinsic expression yields

A small success-predicate calculus for the existing state printer proves facts
about arbitrary inputs and arbitrary remaining layouts. It is not another syntax
representation and does not assume a root split or expression uniqueness.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def Produces {α : Type} (p : Pr α) (P : α → Prop) : Prop :=
  ∀ initial value rest, p initial = some (value, rest) → P value

theorem produces_pure {α : Type} (value : α) (P : α → Prop) (h : P value) :
    Produces (pure value) P := by
  intro initial result rest hr
  change some (value, initial) = some (result, rest) at hr
  cases hr
  exact h

theorem produces_bind_all {α β : Type} (p : Pr α) (k : α → Pr β) (Q : β → Prop)
    (h : ∀ value, Produces (k value) Q) : Produces (p >>= k) Q := by
  intro initial result rest hr
  change (p initial).bind (fun r => k r.1 r.2) = some (result, rest) at hr
  cases hp : p initial with
  | none => rw [hp] at hr; cases hr
  | some value =>
    rw [hp] at hr
    exact h value.1 value.2 result rest hr

theorem produces_bind {α β : Type} (p : Pr α) (k : α → Pr β)
    (P : α → Prop) (Q : β → Prop) (hp : Produces p P)
    (hk : ∀ value, P value → Produces (k value) Q) : Produces (p >>= k) Q := by
  intro initial result rest hr
  change (p initial).bind (fun r => k r.1 r.2) = some (result, rest) at hr
  cases he : p initial with
  | none => rw [he] at hr; cases hr
  | some value =>
    rw [he] at hr
    exact hk value.1 (hp initial value.1 value.2 he) value.2 result rest hr

def SingleItem (items : List (List Tok)) : Prop := ∃ ts, items = [ts]

def NonemptyItem (items : List (List Tok)) : Prop := ∃ ts, items = [ts] ∧ ts ≠ []

/-- All 29 expression constructors produce one item, for arbitrary subtrees,
including successful partial-layout executions. No precedence premise is needed. -/
theorem expr_yield_single (e : Syn .expr) : Produces e.yield SingleItem := by
  cases e with
  | index e i =>
    apply produces_bind_all (e.yield) _ SingleItem
    intro value0
    apply produces_bind_all (i.yield) _ SingleItem
    intro value1
    exact produces_pure _ _ ⟨_, rfl⟩
  | slice e i j =>
    apply produces_bind_all (e.yield) _ SingleItem
    intro value0
    apply produces_bind_all (i.yield) _ SingleItem
    intro value1
    apply produces_bind_all (j.yield) _ SingleItem
    intro value2
    exact produces_pure _ _ ⟨_, rfl⟩
  | member e name =>
    apply produces_bind_all (e.yield) _ SingleItem
    intro value0
    exact produces_pure _ _ ⟨_, rfl⟩
  | callOptions e first rest =>
    apply produces_bind_all (e.yield) _ SingleItem
    intro value0
    apply produces_bind_all (first.yield) _ SingleItem
    intro value1
    apply produces_bind_all (rest.yield) _ SingleItem
    intro value2
    exact produces_pure _ _ ⟨_, rfl⟩
  | call e args =>
    apply produces_bind_all (e.yield) _ SingleItem
    intro value0
    apply produces_bind_all (args.yield) _ SingleItem
    intro value1
    exact produces_pure _ _ ⟨_, rfl⟩
  | payableConv args =>
    apply produces_bind_all (args.yield) _ SingleItem
    intro value0
    exact produces_pure _ _ ⟨_, rfl⟩
  | metaType ty =>
    apply produces_bind_all (ty.yield) _ SingleItem
    intro value0
    exact produces_pure _ _ ⟨_, rfl⟩
  | unaryPrefix op e =>
    apply produces_bind_all (e.yield) _ SingleItem
    intro value0
    exact produces_pure _ _ ⟨_, rfl⟩
  | unarySuffix op e =>
    apply produces_bind_all (e.yield) _ SingleItem
    intro value0
    exact produces_pure _ _ ⟨_, rfl⟩
  | exp a b =>
    apply produces_bind_all (a.yield) _ SingleItem
    intro value0
    apply produces_bind_all (b.yield) _ SingleItem
    intro value1
    exact produces_pure _ _ ⟨_, rfl⟩
  | mulDivMod op a b =>
    apply produces_bind_all (a.yield) _ SingleItem
    intro value0
    apply produces_bind_all (b.yield) _ SingleItem
    intro value1
    exact produces_pure _ _ ⟨_, rfl⟩
  | addSub op a b =>
    apply produces_bind_all (a.yield) _ SingleItem
    intro value0
    apply produces_bind_all (b.yield) _ SingleItem
    intro value1
    exact produces_pure _ _ ⟨_, rfl⟩
  | shift op a b =>
    apply produces_bind_all (a.yield) _ SingleItem
    intro value0
    apply produces_bind_all (b.yield) _ SingleItem
    intro value1
    exact produces_pure _ _ ⟨_, rfl⟩
  | bitAnd a b =>
    apply produces_bind_all (a.yield) _ SingleItem
    intro value0
    apply produces_bind_all (b.yield) _ SingleItem
    intro value1
    exact produces_pure _ _ ⟨_, rfl⟩
  | bitXor a b =>
    apply produces_bind_all (a.yield) _ SingleItem
    intro value0
    apply produces_bind_all (b.yield) _ SingleItem
    intro value1
    exact produces_pure _ _ ⟨_, rfl⟩
  | bitOr a b =>
    apply produces_bind_all (a.yield) _ SingleItem
    intro value0
    apply produces_bind_all (b.yield) _ SingleItem
    intro value1
    exact produces_pure _ _ ⟨_, rfl⟩
  | order op a b =>
    apply produces_bind_all (a.yield) _ SingleItem
    intro value0
    apply produces_bind_all (b.yield) _ SingleItem
    intro value1
    exact produces_pure _ _ ⟨_, rfl⟩
  | equality op a b =>
    apply produces_bind_all (a.yield) _ SingleItem
    intro value0
    apply produces_bind_all (b.yield) _ SingleItem
    intro value1
    exact produces_pure _ _ ⟨_, rfl⟩
  | and a b =>
    apply produces_bind_all (a.yield) _ SingleItem
    intro value0
    apply produces_bind_all (b.yield) _ SingleItem
    intro value1
    exact produces_pure _ _ ⟨_, rfl⟩
  | or a b =>
    apply produces_bind_all (a.yield) _ SingleItem
    intro value0
    apply produces_bind_all (b.yield) _ SingleItem
    intro value1
    exact produces_pure _ _ ⟨_, rfl⟩
  | cond c a b =>
    apply produces_bind_all (c.yield) _ SingleItem
    intro value0
    apply produces_bind_all (a.yield) _ SingleItem
    intro value1
    apply produces_bind_all (b.yield) _ SingleItem
    intro value2
    exact produces_pure _ _ ⟨_, rfl⟩
  | assign op a b =>
    apply produces_bind_all (a.yield) _ SingleItem
    intro value0
    apply produces_bind_all (b.yield) _ SingleItem
    intro value1
    exact produces_pure _ _ ⟨_, rfl⟩
  | new ty =>
    apply produces_bind_all (ty.yield) _ SingleItem
    intro value0
    exact produces_pure _ _ ⟨_, rfl⟩
  | tuple first rest =>
    apply produces_bind_all (first.yield) _ SingleItem
    intro value0
    apply produces_bind_all (rest.yield) _ SingleItem
    intro value1
    exact produces_pure _ _ ⟨_, rfl⟩
  | inlineArray first rest =>
    apply produces_bind_all (first.yield) _ SingleItem
    intro value0
    apply produces_bind_all (rest.yield) _ SingleItem
    intro value1
    exact produces_pure _ _ ⟨_, rfl⟩
  | ident name =>
    exact produces_pure _ _ ⟨_, rfl⟩
  | lit l =>
    apply produces_bind_all (litP l) _ SingleItem
    intro value0
    exact produces_pure _ _ ⟨_, rfl⟩
  | litUnit n u =>
    exact produces_pure _ _ ⟨_, rfl⟩
  | elemType ty ht =>
    exact produces_pure _ _ ⟨_, rfl⟩

theorem litP_nonempty (l : Lit) : Produces (litP l) (fun ts => ts ≠ []) := by
  cases l with
  | bool b => exact produces_pure _ _ (by intro h; cases h)
  | num n => exact produces_pure _ _ (by intro h; cases h)
  | str bs =>
    intro initial ts rest h
    obtain ⟨cs, _, ht, hne⟩ := fragsP_spec Tok.str bs initial rest ts h
    rw [ht]
    intro empty
    exact hne (List.map_eq_nil_iff.mp empty)
  | hexStr bs =>
    intro initial ts rest h
    obtain ⟨cs, _, ht, hne⟩ := fragsP_spec Tok.hexStr bs initial rest ts h
    rw [ht]
    intro empty
    exact hne (List.map_eq_nil_iff.mp empty)
  | unicodeStr bs =>
    intro initial ts rest h
    obtain ⟨cs, _, ht, hne⟩ := fragsP_spec Tok.unicodeStr bs initial rest ts h
    rw [ht]
    intro empty
    exact hne (List.map_eq_nil_iff.mp empty)

theorem callArgs_yield_nonempty (args : Syn .callArgs) : Produces args.yield NonemptyItem := by
  cases args with
  | positional es =>
    apply produces_bind_all es.yield _ NonemptyItem
    intro items
    exact produces_pure _ _ ⟨_, rfl, by intro h; cases h⟩
  | named args =>
    apply produces_bind_all args.yield _ NonemptyItem
    intro items
    exact produces_pure _ _ ⟨_, rfl, by intro h; cases h⟩

theorem nonemptyItem_flatten {items : List (List Tok)} (h : NonemptyItem items) :
    items.flatten ≠ [] := by
  obtain ⟨ts, rfl, ht⟩ := h
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using ht

theorem append_nonempty_left {α : Type} (xs ys : List α) (h : xs ≠ []) : xs ++ ys ≠ [] :=
  fun empty => h (List.append_eq_nil_iff.mp empty).1

theorem append_nonempty_right {α : Type} (xs ys : List α) (h : ys ≠ []) : xs ++ ys ≠ [] :=
  fun empty => h (List.append_eq_nil_iff.mp empty).2

/-- Every successful expression yield has nonempty tokens, even before the
layout suffix is consumed. The argument is exhaustive over the intrinsic roots. -/
theorem expr_yield_nonempty (e : Syn .expr) : Produces e.yield NonemptyItem := by
  cases e with
  | index e i =>
    apply produces_bind_all e.yield _ NonemptyItem
    intro value0
    apply produces_bind_all i.yield _ NonemptyItem
    intro value1
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | slice e i j =>
    apply produces_bind_all e.yield _ NonemptyItem
    intro value0
    apply produces_bind_all i.yield _ NonemptyItem
    intro value1
    apply produces_bind_all j.yield _ NonemptyItem
    intro value2
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | member e name =>
    apply produces_bind_all e.yield _ NonemptyItem
    intro value0
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | callOptions e first rest =>
    apply produces_bind_all e.yield _ NonemptyItem
    intro value0
    apply produces_bind_all first.yield _ NonemptyItem
    intro value1
    apply produces_bind_all rest.yield _ NonemptyItem
    intro value2
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | call e args =>
    apply produces_bind_all e.yield _ NonemptyItem
    intro value0
    apply produces_bind args.yield _ NonemptyItem NonemptyItem (callArgs_yield_nonempty args)
    intro items hitems
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    exact append_nonempty_right _ _ (nonemptyItem_flatten hitems)
  | payableConv args =>
    apply produces_bind_all args.yield _ NonemptyItem
    intro value0
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | metaType ty =>
    apply produces_bind_all ty.yield _ NonemptyItem
    intro value0
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | unaryPrefix op e =>
    apply produces_bind_all e.yield _ NonemptyItem
    intro value0
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    cases op <;> exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
  | unarySuffix op e =>
    apply produces_bind_all e.yield _ NonemptyItem
    intro value0
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | exp a b =>
    apply produces_bind_all a.yield _ NonemptyItem
    intro value0
    apply produces_bind_all b.yield _ NonemptyItem
    intro value1
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | mulDivMod op a b =>
    apply produces_bind_all a.yield _ NonemptyItem
    intro value0
    apply produces_bind_all b.yield _ NonemptyItem
    intro value1
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | addSub op a b =>
    apply produces_bind_all a.yield _ NonemptyItem
    intro value0
    apply produces_bind_all b.yield _ NonemptyItem
    intro value1
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | shift op a b =>
    apply produces_bind_all a.yield _ NonemptyItem
    intro value0
    apply produces_bind_all b.yield _ NonemptyItem
    intro value1
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | bitAnd a b =>
    apply produces_bind_all a.yield _ NonemptyItem
    intro value0
    apply produces_bind_all b.yield _ NonemptyItem
    intro value1
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | bitXor a b =>
    apply produces_bind_all a.yield _ NonemptyItem
    intro value0
    apply produces_bind_all b.yield _ NonemptyItem
    intro value1
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | bitOr a b =>
    apply produces_bind_all a.yield _ NonemptyItem
    intro value0
    apply produces_bind_all b.yield _ NonemptyItem
    intro value1
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | order op a b =>
    apply produces_bind_all a.yield _ NonemptyItem
    intro value0
    apply produces_bind_all b.yield _ NonemptyItem
    intro value1
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | equality op a b =>
    apply produces_bind_all a.yield _ NonemptyItem
    intro value0
    apply produces_bind_all b.yield _ NonemptyItem
    intro value1
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | and a b =>
    apply produces_bind_all a.yield _ NonemptyItem
    intro value0
    apply produces_bind_all b.yield _ NonemptyItem
    intro value1
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | or a b =>
    apply produces_bind_all a.yield _ NonemptyItem
    intro value0
    apply produces_bind_all b.yield _ NonemptyItem
    intro value1
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | cond c a b =>
    apply produces_bind_all c.yield _ NonemptyItem
    intro value0
    apply produces_bind_all a.yield _ NonemptyItem
    intro value1
    apply produces_bind_all b.yield _ NonemptyItem
    intro value2
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | assign op a b =>
    apply produces_bind_all a.yield _ NonemptyItem
    intro value0
    apply produces_bind_all b.yield _ NonemptyItem
    intro value1
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | new ty =>
    apply produces_bind_all ty.yield _ NonemptyItem
    intro value0
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | tuple first rest =>
    apply produces_bind_all first.yield _ NonemptyItem
    intro value0
    apply produces_bind_all rest.yield _ NonemptyItem
    intro value1
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | inlineArray first rest =>
    apply produces_bind_all first.yield _ NonemptyItem
    intro value0
    apply produces_bind_all rest.yield _ NonemptyItem
    intro value1
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | ident name =>
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | lit l =>
    apply produces_bind (litP l) _ (fun ts => ts ≠ []) NonemptyItem (litP_nonempty l)
    intro tokens htokens
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    exact htokens
  | litUnit n u =>
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))
  | elemType ty ht =>
    apply produces_pure
    refine ⟨_, rfl, ?_⟩
    first
      | exact List.cons_ne_nil _ _
      | exact append_nonempty_left _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_right _ _ (List.cons_ne_nil _ _)
      | exact append_nonempty_left _ _ (append_nonempty_right _ _ (List.cons_ne_nil _ _))

/-- Connect the public fully-consumed token certificate to the actual one-item
yield equation; no layout equality premise is introduced. -/
theorem expr_toks_iff (e : Syn .expr) (L : List Choice) (ts : List Tok) :
    e.toks L = some ts ↔ e.yield L = some ([ts], []) := by
  constructor
  · intro ht
    cases hy : e.yield L with
    | none => simp only [Syn.toks, hy] at ht; cases ht
    | some result =>
      rcases result with ⟨items, rest⟩
      cases rest with
      | cons choice rest => simp only [Syn.toks, hy] at ht; cases ht
      | nil =>
        obtain ⟨tokens, he⟩ := expr_yield_single e L items [] hy
        subst items
        have heq : tokens = ts := by
          simpa only [Syn.toks, hy, List.flatten_cons, List.flatten_nil, List.append_nil,
            Option.some.injEq] using ht
        cases heq
        rfl
  · intro hy
    simp only [Syn.toks, hy, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem derives_nonempty_of_produces {c : Cat} (e : Syn c)
    (hp : Produces e.yield NonemptyItem) (ts : List Tok) (h : e.Derives ts) : ts ≠ [] := by
  obtain ⟨L, ht⟩ := h
  cases hy : e.yield L with
  | none => simp only [Syn.toks, hy] at ht; cases ht
  | some result =>
    rcases result with ⟨items, rest⟩
    cases rest with
    | cons choice rest => simp only [Syn.toks, hy] at ht; cases ht
    | nil =>
      have hne := nonemptyItem_flatten (hp L items [] hy)
      have heq : items.flatten = ts := by
        simpa only [Syn.toks, hy, Option.some.injEq] using ht
      exact heq ▸ hne

theorem expr_derives_nonempty (e : Syn .expr) (ts : List Tok) (h : e.Derives ts) : ts ≠ [] :=
  derives_nonempty_of_produces e (expr_yield_nonempty e) ts h

theorem some_expr_yield_nonempty (e : Syn .expr) : Produces (Syn.some e).yield NonemptyItem := by
  apply produces_bind e.yield _ NonemptyItem NonemptyItem (expr_yield_nonempty e)
  intro items hi
  exact produces_pure _ _ ⟨_, rfl, nonemptyItem_flatten hi⟩

/-- Empty optional-expression tokens uniquely identify absence, for arbitrary
expression contents and layouts. This discharges the tuple-hole ambiguity case. -/
theorem optional_expr_empty_iff (e : Syn (.opt .expr)) : e.Derives [] ↔ e = .none := by
  cases e with
  | none =>
    constructor
    · intro _; rfl
    · intro _; exact ⟨[], rfl⟩
  | some e =>
    constructor
    · intro h
      exact False.elim (derives_nonempty_of_produces (.some e)
        (some_expr_yield_nonempty e) [] h rfl)
    · intro h; cases h

/-- A present expression option preserves the expression's one-item state
printer exactly, including the untouched remainder of the layout. -/
theorem some_expr_yield_eq (e : Syn .expr) : (Syn.some e).yield = e.yield := by
  funext L
  change ((e.yield L).bind fun r => some ([r.1.flatten], r.2)) = e.yield L
  cases he : e.yield L with
  | none => rfl
  | some result =>
    rcases result with ⟨items, rest⟩
    obtain ⟨ts, rfl⟩ := expr_yield_single e L items rest he
    simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil]

/-- This partial-layout version is what the tuple/index/slice parent uses. -/
theorem optional_expr_yield_empty_iff (e : Syn (.opt .expr)) (L rest : List Choice)
    (items : List (List Tok)) (h : e.yield L = some (items, rest)) :
    items.flatten = [] ↔ e = .none := by
  cases e with
  | none =>
    change some ([], L) = some (items, rest) at h
    cases h
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some e =>
    constructor
    · intro empty
      exact False.elim (nonemptyItem_flatten (some_expr_yield_nonempty e L items rest h) empty)
    · intro impossible; cases impossible

theorem optional_presence_reconstructed (a b : Syn (.opt .expr))
    (La Lb ra rb : List Choice) (xs ys : List (List Tok))
    (ha : a.yield La = some (xs, ra)) (hb : b.yield Lb = some (ys, rb))
    (heq : xs.flatten = ys.flatten) : a = .none ↔ b = .none := by
  constructor
  · intro absent
    apply (optional_expr_yield_empty_iff b Lb rb ys hb).mp
    rw [← heq]
    exact (optional_expr_yield_empty_iff a La ra xs ha).mpr absent
  · intro absent
    apply (optional_expr_yield_empty_iff a La ra xs ha).mp
    rw [heq]
    exact (optional_expr_yield_empty_iff b Lb rb ys hb).mpr absent

end Solidity.Frontend.ExpressionUniqueness
