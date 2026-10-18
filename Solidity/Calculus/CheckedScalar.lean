import Solidity.Calculus.LinearForms
import Solidity.Calculus.QueryReduction

/-!
# Definedness guards for checked scalar arithmetic

Affine expressions denote scalar codes, with the signed offset explicit.
Their guards describe successful evaluation, including both operands and
the result's bounds. Failed computations are preserved as failure; equal
out-of-range expressions do not become a true defined equality.
-/

namespace Solidity.Linear

namespace ScalarCode

def offset : PrimTy → Int
  | .int => ((2 ^ 255 : Nat) : Int)
  | .bool | .uint => 0

def integer : (p : PrimTy) → p.Denote → Int
  | .bool, v => if v = true then 1 else 0
  | .uint, v | .int, v => v.val

theorem encode_integer (p : PrimTy) (v : p.Denote) :
    ((encode p v).val : Int) = integer p v + offset p := by
  cases p with
  | bool => cases v <;> rfl
  | uint =>
    have h : PrimTy.uint.inRange v.val = true := v.property
    simp only [PrimTy.inRange, decide_eq_true_eq] at h
    change (v.val.toNat : Int) = v.val + 0
    omega
  | int =>
    have h : PrimTy.int.inRange v.val = true := v.property
    simp only [PrimTy.inRange, decide_eq_true_eq] at h
    change ((v.val + ((2 ^ 255 : Nat) : Int)).toNat : Int) = v.val + ((2 ^ 255 : Nat) : Int)
    omega

/-- The shifted range test is exactly Solidity's signed/unsigned range. -/
theorem inRange_iff (p : PrimTy) (hp : p.isNumeric = true) (n : Int) :
    p.inRange n = true ↔ 0 ≤ n + offset p ∧ n + offset p < (bound p : Int) := by
  cases p with
  | bool => cases hp
  | uint => simp only [PrimTy.inRange, decide_eq_true_eq, offset, bound, Int.add_zero]
  | int =>
    simp only [PrimTy.inRange, decide_eq_true_eq, offset, bound]
    have hb : ((2 ^ 256 : Nat) : Int) = 2 * ((2 ^ 255 : Nat) : Int) := by decide +kernel
    omega

end ScalarCode

/-- A partial primitive computation, as a code and its definedness guard. -/
structure CheckedScalar (p : PrimTy) where
  code : Affine
  defined : AFml

namespace CheckedScalar

open ScalarCode

/-- Exact relation to the interpreter's optional result. A successful result
has its exact code; a failed result has a false guard. -/
def Correct {p : PrimTy} (a : CheckedScalar p) (x : Nat → Nat) : Option p.Denote → Prop
  | none => ¬ a.defined.holds x
  | some v => a.defined.holds x ∧ a.code.eval x = ((encode p v).val : Int)

def range (p : PrimTy) (a : Affine) : AFml :=
  .and ((Affine.literal 0).le a) (a.le (.literal ((ScalarCode.bound p : Int) - 1)))

theorem range_iff (p : PrimTy) (a : Affine) (x : Nat → Nat) :
    (range p a).holds x ↔ 0 ≤ a.eval x ∧ a.eval x < (ScalarCode.bound p : Int) := by
  simp only [range, AFml.holds, Affine.holds_le, Affine.eval_literal]
  omega

def ofInt (p : PrimTy) (a : Affine) : CheckedScalar p := ⟨a, range p a⟩

theorem ofInt_correct (p : PrimTy) (hp : p.isNumeric = true) (a : Affine) (n : Int)
    (x : Nat → Nat) (ha : a.eval x = n + offset p) :
    (ofInt p a).Correct x (p.ofInt? n) := by
  have hd : (range p a).holds x ↔ p.inRange n = true := by
    rw [range_iff, ha]
    exact (ScalarCode.inRange_iff p hp n).symm
  cases p with
  | bool => cases hp
  | uint | int =>
    simp only [PrimTy.ofInt?]
    split
    · rename_i hr
      change (range _ a).holds x ∧ a.eval x = _
      refine ⟨hd.2 hr, ?_⟩
      rw [encode_integer]
      exact ha
    · rename_i hr
      exact fun hg => hr (hd.1 hg)

/-- Requiring an operand to return preserves failed evaluation exactly. -/
def guard {p : PrimTy} (g : AFml) (a : CheckedScalar p) : CheckedScalar p :=
  ⟨a.code, .and g a.defined⟩

theorem guard_correct {p : PrimTy} (g : AFml) (a : CheckedScalar p) (x : Nat → Nat)
    (v : Option p.Denote) (h : a.Correct x v) (hg : g.holds x) :
    (a.guard g).Correct x v := by
  cases v <;> simp_all only [Correct, guard, AFml.holds, true_and, not_false_eq_true]

/-- Result code of checked addition/subtraction. The signed offset occurs
once in the result, even though both operands already contain it. -/
def arithCode (p : PrimTy) (subtract : Bool) (a b : Affine) : Affine :=
  if subtract then (a.sub b).offset (offset p) else (a.add b).offset (-offset p)

def arith {p : PrimTy} (subtract : Bool) (a b : CheckedScalar p) : CheckedScalar p :=
  (ofInt p (arithCode p subtract a.code b.code)).guard (.and a.defined b.defined)

/-- Exact optional arithmetic: both operands and the checked result must
return. In particular, failure of both sides is still failure. -/
theorem arith_correct {p : PrimTy} (hp : p.isNumeric = true) (subtract : Bool)
    (a b : CheckedScalar p) (x : Nat → Nat) (va vb : Option p.Denote)
    (ha : a.Correct x va) (hb : b.Correct x vb) :
    (arith subtract a b).Correct x (va.bind fun v => vb.bind fun w =>
      p.ofInt? (if subtract then integer p v - integer p w else integer p v + integer p w)) := by
  cases va with
  | none =>
    exact fun hg => ha hg.1.1
  | some v =>
    cases vb with
    | none => exact fun hg => hb hg.1.2
    | some w =>
      apply guard_correct (.and a.defined b.defined) _ x _ _ ⟨ha.1, hb.1⟩
      apply ofInt_correct p hp
      cases subtract <;>
        simp only [arithCode, Bool.false_eq_true, ↓reduceIte, Affine.eval_add,
          Affine.eval_sub, Affine.eval_offset, ha.2, hb.2, encode_integer]
      all_goals omega

/-- Defined equality includes both guards. Two failed expressions are not
equal, even when their unchecked affine values happen to coincide. -/
def eq {p : PrimTy} (a b : CheckedScalar p) : AFml :=
  .and a.defined (.and b.defined (a.code.eq b.code))

theorem eq_correct {p : PrimTy} (a b : CheckedScalar p) (x : Nat → Nat)
    (va vb : Option p.Denote) (ha : a.Correct x va) (hb : b.Correct x vb) :
    (a.eq b).holds x ↔ Decide.ReadFormula.equal va vb = true := by
  cases va <;> cases vb <;>
    simp_all only [Correct, eq, AFml.holds, Affine.holds_eq, Decide.ReadFormula.equal,
      Bool.false_eq_true, decide_eq_true_eq, false_and, true_and, iff_self]
  constructor
  · intro hc
    apply (ScalarCode.encode_val_eq_iff p _ _).1
    omega
  · rintro rfl; rfl

end CheckedScalar

end Solidity.Linear
