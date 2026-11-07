import Solidity.Frontend.ExpressionUniqueness.BinaryRoot

/-!
# Certified binary marker classes distinguish lower roots from higher roots

The existing root level is classified by exhaustive intrinsic constructors.
Every token marker used below is derived from the original tree certificates.
Rank-ten operand state and complete child-span/tree reconstruction remain open.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem certified_left_binary_marker (e : Syn .expr) (ts : List Tok)
    (hmin : 2 ≤ e.level) (hmax : e.level ≤ 11) (hskip : e.level ≠ 10)
    (hp : e.prec = true) (hd : e.Derives ts) :
    ∃ position marker, lastTop (binaryMarker e.level) ts = some (position, marker) ∧
      binaryMarker e.level marker = true := by
  cases e with
  | index => exact ((by decide : ¬ 15 ≤ 11) hmax).elim
  | slice => exact ((by decide : ¬ 15 ≤ 11) hmax).elim
  | member => exact ((by decide : ¬ 15 ≤ 11) hmax).elim
  | callOptions => exact ((by decide : ¬ 15 ≤ 11) hmax).elim
  | call => exact ((by decide : ¬ 15 ≤ 11) hmax).elim
  | payableConv => exact ((by decide : ¬ 16 ≤ 11) hmax).elim
  | metaType => exact ((by decide : ¬ 16 ≤ 11) hmax).elim
  | unaryPrefix => exact ((by decide : ¬ 13 ≤ 11) hmax).elim
  | unarySuffix => exact ((by decide : ¬ 14 ≤ 11) hmax).elim
  | exp => exact ((by decide : ¬ 12 ≤ 11) hmax).elim
  | mulDivMod op a b =>
    obtain ⟨position, scan⟩ := mul_derives_lastBinary op a b ts hp hd
    refine ⟨position, .punct op.punct, scan, ?_⟩
    cases op <;> rfl
  | addSub => exact (hskip rfl).elim
  | shift op a b =>
    obtain ⟨position, scan⟩ := shift_derives_lastBinary op a b ts hp hd
    refine ⟨position, .punct op.punct, scan, ?_⟩
    cases op <;> rfl
  | bitAnd a b =>
    obtain ⟨position, scan⟩ := bitAnd_derives_lastBinary a b ts hp hd
    refine ⟨position, .punct .bitAnd, scan, ?_⟩
    rfl
  | bitXor a b =>
    obtain ⟨position, scan⟩ := bitXor_derives_lastBinary a b ts hp hd
    refine ⟨position, .punct .bitXor, scan, ?_⟩
    rfl
  | bitOr a b =>
    obtain ⟨position, scan⟩ := bitOr_derives_lastBinary a b ts hp hd
    refine ⟨position, .punct .bitOr, scan, ?_⟩
    rfl
  | order op a b =>
    obtain ⟨position, scan⟩ := order_derives_lastBinary op a b ts hp hd
    refine ⟨position, .punct op.punct, scan, ?_⟩
    cases op <;> rfl
  | equality op a b =>
    obtain ⟨position, scan⟩ := equality_derives_lastBinary op a b ts hp hd
    refine ⟨position, .punct op.punct, scan, ?_⟩
    cases op <;> rfl
  | and a b =>
    obtain ⟨position, scan⟩ := and_derives_lastBinary a b ts hp hd
    refine ⟨position, .punct .and, scan, ?_⟩
    rfl
  | or a b =>
    obtain ⟨position, scan⟩ := or_derives_lastBinary a b ts hp hd
    refine ⟨position, .punct .or, scan, ?_⟩
    rfl
  | cond => exact ((by decide : ¬ 2 ≤ 1) hmin).elim
  | assign => exact ((by decide : ¬ 2 ≤ 0) hmin).elim
  | new => exact ((by decide : ¬ 16 ≤ 11) hmax).elim
  | tuple => exact ((by decide : ¬ 16 ≤ 11) hmax).elim
  | inlineArray => exact ((by decide : ¬ 16 ≤ 11) hmax).elim
  | ident => exact ((by decide : ¬ 16 ≤ 11) hmax).elim
  | lit => exact ((by decide : ¬ 16 ≤ 11) hmax).elim
  | litUnit => exact ((by decide : ¬ 16 ≤ 11) hmax).elim
  | elemType => exact ((by decide : ¬ 16 ≤ 11) hmax).elim

theorem expr_level_twelve_cases (e : Syn .expr) (hl : e.level = 12) :
    ∃ a b, e = Syn.exp a b := by
  cases e with
  | exp a b => exact ⟨a, b, rfl⟩
  | index => exact ((by decide : 15 ≠ 12) hl).elim
  | slice => exact ((by decide : 15 ≠ 12) hl).elim
  | member => exact ((by decide : 15 ≠ 12) hl).elim
  | callOptions => exact ((by decide : 15 ≠ 12) hl).elim
  | call => exact ((by decide : 15 ≠ 12) hl).elim
  | payableConv => exact ((by decide : 16 ≠ 12) hl).elim
  | metaType => exact ((by decide : 16 ≠ 12) hl).elim
  | unaryPrefix => exact ((by decide : 13 ≠ 12) hl).elim
  | unarySuffix => exact ((by decide : 14 ≠ 12) hl).elim
  | mulDivMod => exact ((by decide : 11 ≠ 12) hl).elim
  | addSub => exact ((by decide : 10 ≠ 12) hl).elim
  | shift => exact ((by decide : 9 ≠ 12) hl).elim
  | bitAnd => exact ((by decide : 8 ≠ 12) hl).elim
  | bitXor => exact ((by decide : 7 ≠ 12) hl).elim
  | bitOr => exact ((by decide : 6 ≠ 12) hl).elim
  | order => exact ((by decide : 5 ≠ 12) hl).elim
  | equality => exact ((by decide : 4 ≠ 12) hl).elim
  | and => exact ((by decide : 3 ≠ 12) hl).elim
  | or => exact ((by decide : 2 ≠ 12) hl).elim
  | cond => exact ((by decide : 1 ≠ 12) hl).elim
  | assign => exact ((by decide : 0 ≠ 12) hl).elim
  | new => exact ((by decide : 16 ≠ 12) hl).elim
  | tuple => exact ((by decide : 16 ≠ 12) hl).elim
  | inlineArray => exact ((by decide : 16 ≠ 12) hl).elim
  | ident => exact ((by decide : 16 ≠ 12) hl).elim
  | lit => exact ((by decide : 16 ≠ 12) hl).elim
  | litUnit => exact ((by decide : 16 ≠ 12) hl).elim
  | elemType => exact ((by decide : 16 ≠ 12) hl).elim

theorem certified_exp_marker (e : Syn .expr) (ts : List Tok) (hl : e.level = 12)
    (hp : e.prec = true) (hd : e.Derives ts) :
    ∃ position, firstTop (binaryMarker 12) [] ts = some (position, .punct .exp) := by
  obtain ⟨a, b, he⟩ := expr_level_twelve_cases e hl
  subst e
  exact exp_derives_firstBinary a b ts hp hd

/-- A certified lower left-associative binary root cannot share its yield with
any certified higher root; every scanner hypothesis is derived internally. -/
theorem left_binary_higher_root_disjoint (a b : Syn .expr) (ts : List Tok)
    (hmin : 2 ≤ a.level) (hmax : a.level ≤ 11) (hskip : a.level ≠ 10)
    (higher : a.level < b.level) (ha : a.prec = true) (hb : b.prec = true)
    (da : a.Derives ts) (db : b.Derives ts) : False := by
  obtain ⟨position, marker, scan, _⟩ := certified_left_binary_marker a ts hmin hmax hskip ha da
  have absent : lastTop (binaryMarker a.level) ts = none :=
    lastTop_none_of_binaryFree a.level ts
      (high_expr_derives_binaryFree a.level hmin hskip b ts hb higher db)
  rw [scan] at absent
  cases absent

theorem exp_higher_root_disjoint (a b : Syn .expr) (ts : List Tok)
    (hal : a.level = 12) (higher : 12 < b.level)
    (ha : a.prec = true) (hb : b.prec = true) (da : a.Derives ts) (db : b.Derives ts) : False := by
  obtain ⟨position, scan⟩ := certified_exp_marker a ts hal ha da
  have absent : firstTop (binaryMarker 12) [] ts = none :=
    firstTop_none_of_skip (binaryMarker 12) ts
      (high_expr_derives_binaryFree 12 (by decide) (by decide) b ts hb higher db)
  rw [scan] at absent
  cases absent

theorem mul_punct_injective (op op' : MulOp) (h : op.punct = op'.punct) : op = op' := by
  cases op <;> cases op' <;> cases h <;> rfl

theorem mul_operator_reconstructed (op op' : MulOp) (a b c d : Syn .expr) (ts : List Tok)
    (ha : (Syn.mulDivMod op a b).prec = true) (hb : (Syn.mulDivMod op' c d).prec = true)
    (da : (Syn.mulDivMod op a b).Derives ts) (db : (Syn.mulDivMod op' c d).Derives ts) : op = op' := by
  obtain ⟨n, hn⟩ := mul_derives_lastBinary op a b ts ha da
  obtain ⟨m, hm⟩ := mul_derives_lastBinary op' c d ts hb db
  have ht : Tok.punct op.punct = Tok.punct op'.punct :=
    (Prod.mk.inj (Option.some.inj (hn.symm.trans hm))).2
  exact mul_punct_injective op op' (Tok.punct.inj ht)

theorem shift_punct_injective (op op' : ShiftOp) (h : op.punct = op'.punct) : op = op' := by
  cases op <;> cases op' <;> cases h <;> rfl

theorem shift_operator_reconstructed (op op' : ShiftOp) (a b c d : Syn .expr) (ts : List Tok)
    (ha : (Syn.shift op a b).prec = true) (hb : (Syn.shift op' c d).prec = true)
    (da : (Syn.shift op a b).Derives ts) (db : (Syn.shift op' c d).Derives ts) : op = op' := by
  obtain ⟨n, hn⟩ := shift_derives_lastBinary op a b ts ha da
  obtain ⟨m, hm⟩ := shift_derives_lastBinary op' c d ts hb db
  have ht : Tok.punct op.punct = Tok.punct op'.punct :=
    (Prod.mk.inj (Option.some.inj (hn.symm.trans hm))).2
  exact shift_punct_injective op op' (Tok.punct.inj ht)

theorem order_punct_injective (op op' : OrderOp) (h : op.punct = op'.punct) : op = op' := by
  cases op <;> cases op' <;> cases h <;> rfl

theorem order_operator_reconstructed (op op' : OrderOp) (a b c d : Syn .expr) (ts : List Tok)
    (ha : (Syn.order op a b).prec = true) (hb : (Syn.order op' c d).prec = true)
    (da : (Syn.order op a b).Derives ts) (db : (Syn.order op' c d).Derives ts) : op = op' := by
  obtain ⟨n, hn⟩ := order_derives_lastBinary op a b ts ha da
  obtain ⟨m, hm⟩ := order_derives_lastBinary op' c d ts hb db
  have ht : Tok.punct op.punct = Tok.punct op'.punct :=
    (Prod.mk.inj (Option.some.inj (hn.symm.trans hm))).2
  exact order_punct_injective op op' (Tok.punct.inj ht)

theorem equality_punct_injective (op op' : EqOp) (h : op.punct = op'.punct) : op = op' := by
  cases op <;> cases op' <;> cases h <;> rfl

theorem equality_operator_reconstructed (op op' : EqOp) (a b c d : Syn .expr) (ts : List Tok)
    (ha : (Syn.equality op a b).prec = true) (hb : (Syn.equality op' c d).prec = true)
    (da : (Syn.equality op a b).Derives ts) (db : (Syn.equality op' c d).Derives ts) : op = op' := by
  obtain ⟨n, hn⟩ := equality_derives_lastBinary op a b ts ha da
  obtain ⟨m, hm⟩ := equality_derives_lastBinary op' c d ts hb db
  have ht : Tok.punct op.punct = Tok.punct op'.punct :=
    (Prod.mk.inj (Option.some.inj (hn.symm.trans hm))).2
  exact equality_punct_injective op op' (Tok.punct.inj ht)

end Solidity.Frontend.ExpressionUniqueness
