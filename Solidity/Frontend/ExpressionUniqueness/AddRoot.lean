import Solidity.Frontend.ExpressionUniqueness.ExpressionAddFree
import Solidity.Frontend.ExpressionUniqueness.ExpressionMode
import Solidity.Frontend.ExpressionUniqueness.BinaryRank

/-!
# Certified additive roots use operand-sensitive last markers

This closes the raw-rank-ten marker gap without excluding prefix minus.
All ordinary binary root ranks can now be separated from higher certified roots.
Complete child spans and recursive tree uniqueness remain separate obligations.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def LastAddIs (marker : Tok) (items : List (List Tok)) : Prop :=
  ∃ position, lastAdd items.flatten = some (position, marker)

theorem add_yield_lastAdd (op : AddOp) (a b : Syn .expr)
    (hp : (Syn.addSub op a b).prec = true) :
    Produces (Syn.addSub op a b).yield (LastAddIs (.punct op.punct)) := by
  have hprecb : b.prec = true := by
    apply all_prec_implies_prec b
    have hall : (Syn.addSub op a b).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
    simp only [Syn.all, Bool.and_eq_true] at hall
    exact hall.2
  have hlevelb : 10 < b.level := by
    have hr : (Syn.addSub op a b).precNode = true := Syn.prec_root hp
    simp only [Syn.precNode, binOk, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact Nat.lt_of_lt_of_le (by decide : 10 < 11) hr.2
  have hm : modeStep ([], true) (.punct op.punct) = some ([], false) := by cases op <;> rfl
  have hit : addHit ([], true) (.punct op.punct) = true := by cases op <;> rfl
  apply produces_bind a.yield _ ModeDoneItems (LastAddIs (.punct op.punct)) (expr_yield_modeDone a)
  intro xs hx
  apply produces_bind b.yield _ AddFreeItems (LastAddIs (.punct op.punct))
    (high_expr_yield_addFree b hprecb hlevelb)
  intro ys hy
  apply produces_pure
  refine ⟨xs.flatten.length, ?_⟩
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, pu,
    List.append_assoc, List.singleton_append] using
    lastAdd_marker xs.flatten ys.flatten (.punct op.punct) hx hy hm hit

theorem derives_lastAdd (e : Syn .expr) (ts : List Tok) (marker : Tok)
    (hy : Produces e.yield (LastAddIs marker)) (hd : e.Derives ts) :
    ∃ position, lastAdd ts = some (position, marker) := by
  obtain ⟨L, ht⟩ := hd
  have h : LastAddIs marker [ts] := hy L [ts] [] ((expr_toks_iff e L ts).mp ht)
  simpa only [LastAddIs, List.flatten_cons, List.flatten_nil, List.append_nil] using h

theorem add_derives_lastAdd (op : AddOp) (a b : Syn .expr) (ts : List Tok)
    (hp : (Syn.addSub op a b).prec = true) (hd : (Syn.addSub op a b).Derives ts) :
    ∃ position, lastAdd ts = some (position, .punct op.punct) :=
  derives_lastAdd _ ts _ (add_yield_lastAdd op a b hp) hd

theorem add_punct_injective (op op' : AddOp) (h : op.punct = op'.punct) : op = op' := by
  cases op <;> cases op' <;> cases h <;> rfl

theorem add_operator_reconstructed (op op' : AddOp) (a b c d : Syn .expr) (ts : List Tok)
    (ha : (Syn.addSub op a b).prec = true) (hb : (Syn.addSub op' c d).prec = true)
    (da : (Syn.addSub op a b).Derives ts) (db : (Syn.addSub op' c d).Derives ts) : op = op' := by
  obtain ⟨n, hn⟩ := add_derives_lastAdd op a b ts ha da
  obtain ⟨m, hm⟩ := add_derives_lastAdd op' c d ts hb db
  have ht : Tok.punct op.punct = Tok.punct op'.punct :=
    (Prod.mk.inj (Option.some.inj (hn.symm.trans hm))).2
  exact add_punct_injective op op' (Tok.punct.inj ht)

theorem expr_level_ten_cases (e : Syn .expr) (hl : e.level = 10) :
    ∃ op a b, e = Syn.addSub op a b := by
  cases e with
  | addSub op a b => exact ⟨op, a, b, rfl⟩
  | index => exact ((by decide : 15 ≠ 10) hl).elim
  | slice => exact ((by decide : 15 ≠ 10) hl).elim
  | member => exact ((by decide : 15 ≠ 10) hl).elim
  | callOptions => exact ((by decide : 15 ≠ 10) hl).elim
  | call => exact ((by decide : 15 ≠ 10) hl).elim
  | payableConv => exact ((by decide : 16 ≠ 10) hl).elim
  | metaType => exact ((by decide : 16 ≠ 10) hl).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 10) hl).elim
  | unarySuffix => exact ((by decide : 14 ≠ 10) hl).elim
  | exp => exact ((by decide : 12 ≠ 10) hl).elim
  | mulDivMod => exact ((by decide : 11 ≠ 10) hl).elim
  | shift => exact ((by decide : 9 ≠ 10) hl).elim
  | bitAnd => exact ((by decide : 8 ≠ 10) hl).elim
  | bitXor => exact ((by decide : 7 ≠ 10) hl).elim
  | bitOr => exact ((by decide : 6 ≠ 10) hl).elim
  | order => exact ((by decide : 5 ≠ 10) hl).elim
  | equality => exact ((by decide : 4 ≠ 10) hl).elim
  | and => exact ((by decide : 3 ≠ 10) hl).elim
  | or => exact ((by decide : 2 ≠ 10) hl).elim
  | cond => exact ((by decide : 1 ≠ 10) hl).elim
  | assign => exact ((by decide : 0 ≠ 10) hl).elim
  | new => exact ((by decide : 16 ≠ 10) hl).elim
  | tuple => exact ((by decide : 16 ≠ 10) hl).elim
  | inlineArray => exact ((by decide : 16 ≠ 10) hl).elim
  | ident => exact ((by decide : 16 ≠ 10) hl).elim
  | lit => exact ((by decide : 16 ≠ 10) hl).elim
  | litUnit => exact ((by decide : 16 ≠ 10) hl).elim
  | elemType => exact ((by decide : 16 ≠ 10) hl).elim

theorem add_higher_root_disjoint (a b : Syn .expr) (ts : List Tok)
    (hal : a.level = 10) (higher : 10 < b.level) (ha : a.prec = true) (hb : b.prec = true)
    (da : a.Derives ts) (db : b.Derives ts) : False := by
  obtain ⟨op, left, right, he⟩ := expr_level_ten_cases a hal
  subst a
  obtain ⟨position, scan⟩ := add_derives_lastAdd op left right ts ha da
  have absent : lastAdd ts = none := lastAdd_none_of_skip ts ([], true)
    (high_expr_derives_addFree b ts hb higher db)
  rw [scan] at absent
  cases absent

/-- Every ordinary binary rank 2 through 12, including addition/subtraction,
is disjoint from every higher certified expression root at the same yield. -/
theorem binary_higher_root_disjoint (a b : Syn .expr) (ts : List Tok)
    (hmin : 2 ≤ a.level) (hmax : a.level ≤ 12) (higher : a.level < b.level)
    (ha : a.prec = true) (hb : b.prec = true) (da : a.Derives ts) (db : b.Derives ts) : False := by
  by_cases ten : a.level = 10
  · exact add_higher_root_disjoint a b ts ten (ten ▸ higher) ha hb da db
  by_cases twelve : a.level = 12
  · exact exp_higher_root_disjoint a b ts twelve (twelve ▸ higher) ha hb da db
  have below : a.level ≤ 11 := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hmax twelve)
  exact left_binary_higher_root_disjoint a b ts hmin below ten higher ha hb da db

theorem certified_binary_root_levels_equal (a b : Syn .expr) (ts : List Tok)
    (amin : 2 ≤ a.level) (amax : a.level ≤ 12) (bmin : 2 ≤ b.level) (bmax : b.level ≤ 12)
    (ha : a.prec = true) (hb : b.prec = true) (da : a.Derives ts) (db : b.Derives ts) :
    a.level = b.level := by
  rcases Nat.lt_trichotomy a.level b.level with less | equal | greater
  · exact False.elim (binary_higher_root_disjoint a b ts amin amax less ha hb da db)
  · exact equal
  · exact False.elim (binary_higher_root_disjoint b a ts bmin bmax greater hb ha db da)

end Solidity.Frontend.ExpressionUniqueness
