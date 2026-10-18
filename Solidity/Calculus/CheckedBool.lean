import Solidity.Calculus.CheckedScalar

/-!
# Partial Boolean expressions and numeric comparisons

A Boolean expression has two success predicates, one for each result.
Failure satisfies neither. This representation preserves short circuit
evaluation without pretending that a comparison's Boolean code is affine.
-/

namespace Solidity.Linear

def Affine.compare (op : BinOp) (a b : Affine) : AFml :=
  match op with
  | .lt => .not (b.le a)
  | .gt => .not (a.le b)
  | .le => a.le b
  | .ge => b.le a
  | .eqB => a.eq b
  | .neB => .not (a.eq b)
  | _ => .ff

theorem Affine.holds_compare (op : BinOp) (a b : Affine) (x : Nat → Nat) :
    (a.compare op b).holds x ↔ op.cmpZ (a.eval x) (b.eval x) = true := by
  cases op <;> simp only [compare, AFml.holds, holds_eq, holds_le, BinOp.cmpZ,
    decide_eq_true_eq, Bool.not_eq_true', Bool.eq_false_iff, Bool.false_eq_true]
  all_goals first | omega | simp only [ne_eq, decide_eq_true_eq]

structure CheckedBool where
  yes : AFml
  no : AFml

namespace CheckedBool

def Correct (a : CheckedBool) (x : Nat → Nat) (v : Option Bool) : Prop :=
  (a.yes.holds x ↔ v = some true) ∧ (a.no.holds x ↔ v = some false)

def disj (a b : AFml) : AFml := .imp (.not a) b

theorem disj_holds (a b : AFml) (x : Nat → Nat) :
    (disj a b).holds x ↔ a.holds x ∨ b.holds x := by
  simp only [disj, AFml.holds]
  grind

def ofScalar (a : CheckedScalar .bool) : CheckedBool :=
  ⟨.and a.defined (a.code.eq (.literal 1)), .and a.defined (a.code.eq (.literal 0))⟩

theorem ofScalar_correct (a : CheckedScalar .bool) (x : Nat → Nat) (v : Option Bool)
    (h : a.Correct x v) : (ofScalar a).Correct x v := by
  cases v with
  | none =>
    simp_all only [Correct, CheckedScalar.Correct, ofScalar, AFml.holds, false_and,
      reduceCtorEq, and_self]
  | some b =>
    cases b <;> simp_all only [Correct, CheckedScalar.Correct, ofScalar, AFml.holds,
      Affine.holds_eq, Affine.eval_literal, ScalarCode.encode,
      ↓reduceIte, true_and, reduceCtorEq]
    all_goals decide

def not (a : CheckedBool) : CheckedBool := ⟨a.no, a.yes⟩

theorem not_correct (a : CheckedBool) (x : Nat → Nat) (v : Option Bool)
    (h : a.Correct x v) : a.not.Correct x (v.map (! ·)) := by
  cases v with
  | none =>
    simp only [Correct, not, Option.map_none, reduceCtorEq] at *
    exact ⟨h.2, h.1⟩
  | some b =>
    cases b <;> simp only [Correct, not, Option.map_some, Bool.not_false, Bool.not_true,
      Option.some.injEq, Bool.false_eq_true, Bool.true_eq_false] at * <;> exact ⟨h.2, h.1⟩

def and (a b : CheckedBool) : CheckedBool :=
  ⟨.and a.yes b.yes, disj a.no (.and a.yes b.no)⟩

def or (a b : CheckedBool) : CheckedBool :=
  ⟨disj a.yes (.and a.no b.yes), .and a.no b.no⟩

def andResult (a b : Option Bool) : Option Bool := a.bind fun v => if v then b else some false
def orResult (a b : Option Bool) : Option Bool := a.bind fun v => if v then some true else b

theorem and_correct (a b : CheckedBool) (x : Nat → Nat) (va vb : Option Bool)
    (ha : a.Correct x va) (hb : b.Correct x vb) :
    (a.and b).Correct x (andResult va vb) := by
  simp only [Correct, and, AFml.holds, disj_holds, ha.1, ha.2, hb.1, hb.2]
  cases va with
  | none => simp only [andResult, Option.bind_none, reduceCtorEq, false_and, false_or, iff_self, and_self]
  | some v =>
    cases v <;> cases vb with
    | none => decide
    | some w => cases w <;> decide

theorem or_correct (a b : CheckedBool) (x : Nat → Nat) (va vb : Option Bool)
    (ha : a.Correct x va) (hb : b.Correct x vb) :
    (a.or b).Correct x (orResult va vb) := by
  simp only [Correct, or, AFml.holds, disj_holds, ha.1, ha.2, hb.1, hb.2]
  cases va with
  | none => simp only [orResult, Option.bind_none, reduceCtorEq, false_and, false_or, iff_self, and_self]
  | some v =>
    cases v <;> cases vb with
    | none => decide
    | some w => cases w <;> decide

/-- Boolean equality is strict in both operands, unlike conjunction. -/
def eq (a b : CheckedBool) : CheckedBool :=
  ⟨disj (.and a.yes b.yes) (.and a.no b.no),
    disj (.and a.yes b.no) (.and a.no b.yes)⟩

theorem eq_correct (a b : CheckedBool) (x : Nat → Nat) (va vb : Option Bool)
    (ha : a.Correct x va) (hb : b.Correct x vb) :
    (a.eq b).Correct x (va.bind fun v => vb.map fun w => decide (v = w)) := by
  simp only [Correct, eq, disj_holds, AFml.holds, ha.1, ha.2, hb.1, hb.2]
  cases va with
  | none => simp only [Option.bind_none, reduceCtorEq, false_and, false_or, iff_self, and_self]
  | some v =>
    cases v <;> cases vb with
    | none => decide
    | some w => cases w <;> decide

def comparison {p : PrimTy} (op : BinOp) (a b : CheckedScalar p) : CheckedBool :=
  let predicate := (a.code.offset (-ScalarCode.offset p)).compare op (b.code.offset (-ScalarCode.offset p))
  ⟨.and (.and a.defined b.defined) predicate, .and (.and a.defined b.defined) (.not predicate)⟩

theorem comparison_correct {p : PrimTy} (op : BinOp) (a b : CheckedScalar p) (x : Nat → Nat)
    (va vb : Option p.Denote) (ha : a.Correct x va) (hb : b.Correct x vb) :
    (comparison op a b).Correct x (va.bind fun v => vb.map fun w =>
      op.cmpZ (ScalarCode.integer p v) (ScalarCode.integer p w)) := by
  cases va with
  | none =>
    simp_all only [CheckedScalar.Correct, Correct, comparison, AFml.holds, false_and,
      Option.bind_none, reduceCtorEq, iff_self, and_self]
  | some v =>
    cases vb with
    | none =>
      simp_all only [CheckedScalar.Correct, Correct, comparison, AFml.holds, true_and,
        false_and, Option.bind_some, Option.map_none, reduceCtorEq, iff_self, and_self]
    | some w =>
      have hav : (a.code.offset (-ScalarCode.offset p)).eval x = ScalarCode.integer p v := by
        rw [Affine.eval_offset, ha.2, ScalarCode.encode_integer]
        omega
      have hbv : (b.code.offset (-ScalarCode.offset p)).eval x = ScalarCode.integer p w := by
        rw [Affine.eval_offset, hb.2, ScalarCode.encode_integer]
        omega
      simp only [Correct, comparison, AFml.holds, ha.1, hb.1, true_and,
        Affine.holds_compare, hav, hbv, Option.bind_some, Option.map_some,
        Option.some.injEq, Bool.eq_false_iff, iff_self, and_self]

end CheckedBool

end Solidity.Linear
