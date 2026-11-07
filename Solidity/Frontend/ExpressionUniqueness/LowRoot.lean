import Solidity.Frontend.ExpressionUniqueness.ExpressionLowFree

/-!
# Recover assignment and conditional root marker classes from certificates

The first joint loose-root marker is derived from existing recursive precedence
and printer certificates. Assignments in conditional middle branches are allowed:
the conditional's question mark occurs first. These results reconstruct root
classes and assignment operators, not complete child trees or the colon cut.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def FirstLowIs (marker : Tok) (items : List (List Tok)) : Prop :=
  ∃ n, firstTop lowMarker [] items.flatten = some (n, marker)

theorem assignment_yield_firstLow (op : AssignOp) (a b : Syn .expr)
    (hp : (Syn.assign op a b).prec = true) :
    Produces (Syn.assign op a b).yield (FirstLowIs (.punct op.punct)) := by
  have hpreca : a.prec = true := by
    apply all_prec_implies_prec a
    have hall : (Syn.assign op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.1.2
  have hlevela : 2 ≤ a.level := by
    have hr : (Syn.assign op a b).precNode = true := Syn.prec_root hp
    exact of_decide_eq_true hr
  apply produces_bind a.yield _ LowFreeItems (FirstLowIs (.punct op.punct))
    (high_expr_yield_lowFree a hpreca hlevela)
  intro xs hx
  apply produces_bind_all b.yield _ (FirstLowIs (.punct op.punct))
  intro ys
  apply produces_pure
  refine ⟨xs.flatten.length, ?_⟩
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] using
    firstTop_marker lowMarker xs.flatten ys.flatten (.punct op.punct)
      (lowFreeItems_flatten hx) (assignment_lowMarker op)

theorem conditional_yield_firstLow (c a b : Syn .expr)
    (hp : (Syn.cond c a b).prec = true) :
    Produces (Syn.cond c a b).yield (FirstLowIs (.punct .question)) := by
  have hprecc : c.prec = true := by
    apply all_prec_implies_prec c
    have hall : (Syn.cond c a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.1.1.2
  have hlevelc : 2 ≤ c.level := by
    have hr : (Syn.cond c a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact hr.1
  apply produces_bind c.yield _ LowFreeItems (FirstLowIs (.punct .question))
    (high_expr_yield_lowFree c hprecc hlevelc)
  intro xs hx
  apply produces_bind_all a.yield _ (FirstLowIs (.punct .question))
  intro ys
  apply produces_bind_all b.yield _ (FirstLowIs (.punct .question))
  intro zs
  apply produces_pure
  refine ⟨xs.flatten.length, ?_⟩
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] using
    firstTop_marker lowMarker xs.flatten (ys.flatten ++ pu .colon ++ zs.flatten)
      (.punct .question) (lowFreeItems_flatten hx) rfl

theorem derives_firstLow (e : Syn .expr) (ts : List Tok) (marker : Tok)
    (hy : Produces e.yield (FirstLowIs marker)) (hd : e.Derives ts) :
    ∃ n, firstTop lowMarker [] ts = some (n, marker) := by
  obtain ⟨L, ht⟩ := hd
  have h : FirstLowIs marker [ts] := hy L [ts] [] ((expr_toks_iff e L ts).mp ht)
  simpa only [FirstLowIs, List.flatten_cons, List.flatten_nil, List.append_nil] using h

theorem assignment_derives_firstLow (op : AssignOp) (a b : Syn .expr) (ts : List Tok)
    (hp : (Syn.assign op a b).prec = true) (hd : (Syn.assign op a b).Derives ts) :
    ∃ n, firstTop lowMarker [] ts = some (n, .punct op.punct) :=
  derives_firstLow _ ts _ (assignment_yield_firstLow op a b hp) hd

theorem conditional_derives_firstLow (c a b : Syn .expr) (ts : List Tok)
    (hp : (Syn.cond c a b).prec = true) (hd : (Syn.cond c a b).Derives ts) :
    ∃ n, firstTop lowMarker [] ts = some (n, .punct .question) :=
  derives_firstLow _ ts _ (conditional_yield_firstLow c a b hp) hd

theorem assignment_conditional_disjoint (op : AssignOp) (a b c d e : Syn .expr)
    (ts : List Tok) (ha : (Syn.assign op a b).prec = true)
    (hc : (Syn.cond c d e).prec = true) (da : (Syn.assign op a b).Derives ts)
    (dc : (Syn.cond c d e).Derives ts) : False := by
  obtain ⟨n, hn⟩ := assignment_derives_firstLow op a b ts ha da
  obtain ⟨m, hm⟩ := conditional_derives_firstLow c d e ts hc dc
  have he : Tok.punct op.punct = Tok.punct .question :=
    (Prod.mk.inj (Option.some.inj (hn.symm.trans hm))).2
  cases op <;> cases he

theorem assignment_punct_injective (op op' : AssignOp) (h : op.punct = op'.punct) : op = op' := by
  cases op <;> cases op' <;> cases h <;> rfl

theorem assignment_operator_reconstructed (op op' : AssignOp) (a b c d : Syn .expr)
    (ts : List Tok) (ha : (Syn.assign op a b).prec = true)
    (hc : (Syn.assign op' c d).prec = true) (da : (Syn.assign op a b).Derives ts)
    (dc : (Syn.assign op' c d).Derives ts) : op = op' := by
  obtain ⟨n, hn⟩ := assignment_derives_firstLow op a b ts ha da
  obtain ⟨m, hm⟩ := assignment_derives_firstLow op' c d ts hc dc
  have he : Tok.punct op.punct = Tok.punct op'.punct :=
    (Prod.mk.inj (Option.some.inj (hn.symm.trans hm))).2
  apply assignment_punct_injective op op'
  exact Tok.punct.inj he

theorem expr_level_below_two_cases (e : Syn .expr) (h : e.level < 2) :
    (∃ op a b, e = Syn.assign op a b) ∨ (∃ c a b, e = Syn.cond c a b) := by
  cases e with
  | assign op a b => exact Or.inl ⟨op, a, b, rfl⟩
  | cond c a b => exact Or.inr ⟨c, a, b, rfl⟩
  | index => exact ((by decide : ¬ 15 < 2) h).elim
  | slice => exact ((by decide : ¬ 15 < 2) h).elim
  | member => exact ((by decide : ¬ 15 < 2) h).elim
  | callOptions => exact ((by decide : ¬ 15 < 2) h).elim
  | call => exact ((by decide : ¬ 15 < 2) h).elim
  | payableConv => exact ((by decide : ¬ 16 < 2) h).elim
  | metaType => exact ((by decide : ¬ 16 < 2) h).elim
  | unaryPrefix => exact ((by decide : ¬ 13 < 2) h).elim
  | unarySuffix => exact ((by decide : ¬ 14 < 2) h).elim
  | exp => exact ((by decide : ¬ 12 < 2) h).elim
  | mulDivMod => exact ((by decide : ¬ 11 < 2) h).elim
  | addSub => exact ((by decide : ¬ 10 < 2) h).elim
  | shift => exact ((by decide : ¬ 9 < 2) h).elim
  | bitAnd => exact ((by decide : ¬ 8 < 2) h).elim
  | bitXor => exact ((by decide : ¬ 7 < 2) h).elim
  | bitOr => exact ((by decide : ¬ 6 < 2) h).elim
  | order => exact ((by decide : ¬ 5 < 2) h).elim
  | equality => exact ((by decide : ¬ 4 < 2) h).elim
  | and => exact ((by decide : ¬ 3 < 2) h).elim
  | or => exact ((by decide : ¬ 2 < 2) h).elim
  | new => exact ((by decide : ¬ 16 < 2) h).elim
  | tuple => exact ((by decide : ¬ 16 < 2) h).elim
  | inlineArray => exact ((by decide : ¬ 16 < 2) h).elim
  | ident => exact ((by decide : ¬ 16 < 2) h).elim
  | lit => exact ((by decide : ¬ 16 < 2) h).elim
  | litUnit => exact ((by decide : ¬ 16 < 2) h).elim
  | elemType => exact ((by decide : ¬ 16 < 2) h).elim

/-- The token scanner exactly detects whether a certified expression root is
above the assignment/conditional pair. No root-class premise is provided. -/
theorem certified_firstLow_none_iff (e : Syn .expr) (ts : List Tok)
    (hp : e.prec = true) (hd : e.Derives ts) :
    firstTop lowMarker [] ts = none ↔ 2 ≤ e.level := by
  constructor
  · intro hnone
    by_cases hlevel : 2 ≤ e.level
    · exact hlevel
    have hlt : e.level < 2 := Nat.lt_of_not_ge hlevel
    rcases expr_level_below_two_cases e hlt with ⟨op, a, b, he⟩ | ⟨c, a, b, he⟩
    · subst e
      obtain ⟨n, hn⟩ := assignment_derives_firstLow op a b ts hp hd
      rw [hn] at hnone
      cases hnone
    · subst e
      obtain ⟨n, hn⟩ := conditional_derives_firstLow c a b ts hp hd
      rw [hn] at hnone
      cases hnone
  · intro hl
    exact firstTop_none_of_skip lowMarker ts (high_expr_derives_lowFree e ts hp hl hd)

end Solidity.Frontend.ExpressionUniqueness
