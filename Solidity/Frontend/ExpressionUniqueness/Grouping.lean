import Solidity.Frontend.ExpressionUniqueness.DelimiterReconstruction
import Solidity.Frontend.ExpressionUniqueness.Families

/-!
# Grouping yield inversion and arbitrary-depth certified controls

Parentheses remain the existing one-component tuple. This module reconstructs
the actual child token certificate and the end of a grouping span. Equality of
arbitrary child trees still belongs to the open global uniqueness obligation.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem group_yield_map (e : Syn .expr) (L : List Choice) :
    (group e).yield L = (e.yield L).map (fun r => ([parens r.1.flatten], r.2)) := by
  change (((Syn.some e).yield L).bind
    (fun r => some ([parens (r.1.flatten ++ [])], r.2))) = _
  rw [some_expr_yield_eq]
  cases he : e.yield L with
  | none => rfl
  | some result =>
    rcases result with ⟨items, rest⟩
    simp only [Option.bind_some, Option.map_some, List.append_nil]

theorem group_toks_iff (e : Syn .expr) (L : List Choice) (ts : List Tok) :
    (group e).toks L = some ts ↔ ∃ inner, e.toks L = some inner ∧ ts = parens inner := by
  constructor
  · intro h
    have hg := (expr_toks_iff (group e) L ts).mp h
    rw [group_yield_map] at hg
    cases he : e.yield L with
    | none => rw [he] at hg; cases hg
    | some result =>
      rcases result with ⟨items, rest⟩
      rw [he] at hg
      have hpair := Prod.mk.inj (Option.some.inj hg)
      have hrest : rest = [] := hpair.2
      subst rest
      obtain ⟨inner, hi⟩ := expr_yield_single e L items [] he
      subst items
      refine ⟨inner, (expr_toks_iff e L inner).mpr he, ?_⟩
      have ht := (List.cons.inj hpair.1).1
      simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using ht.symm
  · intro ⟨inner, hi, ht⟩
    subst ts
    apply (expr_toks_iff (group e) L (parens inner)).mpr
    rw [group_yield_map, (expr_toks_iff e L inner).mp hi]
    simp only [Option.map_some, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem group_derives_iff (e : Syn .expr) (ts : List Tok) :
    (group e).Derives ts ↔ ∃ inner, e.Derives inner ∧ ts = parens inner := by
  constructor
  · intro ⟨L, h⟩
    obtain ⟨inner, hi, ht⟩ := (group_toks_iff e L ts).mp h
    exact ⟨inner, ⟨L, hi⟩, ht⟩
  · intro ⟨inner, ⟨L, hi⟩, ht⟩
    exact ⟨L, (group_toks_iff e L ts).mpr ⟨inner, hi, ht⟩⟩

/-- The group and continuation spans are recovered from the original two
certificates; no caller-supplied balance or split premise is used. -/
theorem group_prefix_unique (a b : Syn .expr) (xs ys tail tail' : List Tok)
    (ha : (group a).Derives xs) (hb : (group b).Derives ys)
    (heq : xs ++ tail = ys ++ tail') : xs = ys ∧ tail = tail' := by
  obtain ⟨ia, hia, hxa⟩ := (group_derives_iff a xs).mp ha
  obtain ⟨ib, hib, hyb⟩ := (group_derives_iff b ys).mp hb
  subst xs
  subst ys
  obtain ⟨payload, suffix⟩ := expression_parens_prefix_unique a b ia ib tail tail' hia hib heq
  exact ⟨congrArg parens payload, suffix⟩

def parenTokens : Nat → List Tok → List Tok
  | 0, ts => ts
  | n + 1, ts => parens (parenTokens n ts)

theorem groupFamily_toks (n : Nat) (e : Syn .expr) (L : List Choice) (ts : List Tok)
    (h : e.toks L = some ts) : (groupFamily n e).toks L = some (parenTokens n ts) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    exact (group_toks_iff (groupFamily n e) L (parenTokens (n + 1) ts)).mpr
      ⟨parenTokens n ts, ih, rfl⟩

theorem groupFamily_certified (n : Nat) (e : Syn .expr) (ts : List Tok)
    (hd : e.Derives ts) (hp : e.prec = true) :
    (groupFamily n e).Derives (parenTokens n ts) ∧ (groupFamily n e).prec = true := by
  obtain ⟨L, hL⟩ := hd
  exact ⟨⟨L, groupFamily_toks n e L ts hL⟩, groupFamily_prec n hp⟩

theorem parenTokens_length (n : Nat) (ts : List Tok) :
    (parenTokens n ts).length = ts.length + 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [parenTokens, parens, pu, List.length_append, List.length_cons, List.length_nil, ih]
    omega

theorem parenTokens_depth_injective (ts : List Tok) {n m : Nat}
    (h : parenTokens n ts = parenTokens m ts) : n = m := by
  have hl := congrArg List.length h
  rw [parenTokens_length, parenTokens_length] at hl
  omega

theorem groupFamily_inhabited (n : Nat) (name : String) :
    (groupFamily n (.ident name)).Derives (parenTokens n [.ident name]) ∧
      (groupFamily n (.ident name)).prec = true :=
  groupFamily_certified n (.ident name) [.ident name] ⟨[], rfl⟩ rfl

/-- For a fixed printable intrinsic expression, grouping depth is also
injective at the tree level. No converse yield-uniqueness premise is used. -/
theorem groupFamily_certified_depth_injective (e : Syn .expr) (ts : List Tok)
    (hd : e.Derives ts) {n m : Nat} (h : groupFamily n e = groupFamily m e) : n = m := by
  obtain ⟨L, hL⟩ := hd
  have ht := congrArg (fun tree : Syn .expr => tree.toks L) h
  change (groupFamily n e).toks L = (groupFamily m e).toks L at ht
  rw [groupFamily_toks n e L ts hL, groupFamily_toks m e L ts hL] at ht
  exact parenTokens_depth_injective ts (Option.some.inj ht)

end Solidity.Frontend.ExpressionUniqueness
