import Solidity.Calculus.ScalarCode

/-!
# Affine forms for typed arithmetic translation

Constants and numbered scalar codes share a single affine representation.
The comparison constructors below are exact translations to the existing
arithmetic intermediate language, not extra decision procedures.
-/

namespace Solidity.Linear

def Lin.sub : Lin → Lin → Lin
  | [], bs => bs.map (- ·)
  | as, [] => as
  | a :: as, b :: bs => (a - b) :: Lin.sub as bs

theorem Lin.eval_neg (as : Lin) (x : Nat → Nat) :
    Lin.eval (as.map (- ·)) x = -as.eval x := by
  induction as generalizing x with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, eval, ih]
    grind

theorem Lin.eval_sub (as bs : Lin) (x : Nat → Nat) :
    (as.sub bs).eval x = as.eval x - bs.eval x := by
  induction as generalizing bs x with
  | nil => simp only [sub, eval, eval_neg, Int.zero_sub]
  | cons a as ih =>
    cases bs with
    | nil => simp only [sub, eval, Int.sub_zero]
    | cons b bs =>
      simp only [sub, eval, ih]
      grind

def Lin.add (as bs : Lin) : Lin := as.sub (bs.map (- ·))

theorem Lin.eval_add (as bs : Lin) (x : Nat → Nat) :
    (as.add bs).eval x = as.eval x + bs.eval x := by
  simp only [add, eval_sub, eval_neg, Int.sub_neg]

structure Affine where
  coeff : Lin
  constant : Int

def Affine.eval (a : Affine) (x : Nat → Nat) : Int := a.coeff.eval x + a.constant

def Affine.literal (n : Int) : Affine := ⟨[], n⟩
def Affine.variable (k : Nat) : Affine := ⟨Lin.basis k, 0⟩

def Affine.add (a b : Affine) : Affine := ⟨a.coeff.add b.coeff, a.constant + b.constant⟩
def Affine.sub (a b : Affine) : Affine := ⟨a.coeff.sub b.coeff, a.constant - b.constant⟩
def Affine.offset (a : Affine) (n : Int) : Affine := ⟨a.coeff, a.constant + n⟩

theorem Affine.eval_add (a b : Affine) (x : Nat → Nat) :
    (a.add b).eval x = a.eval x + b.eval x := by
  simp only [add, eval, Lin.eval_add]
  omega

theorem Affine.eval_sub (a b : Affine) (x : Nat → Nat) :
    (a.sub b).eval x = a.eval x - b.eval x := by
  simp only [sub, eval, Lin.eval_sub]
  omega

theorem Affine.eval_offset (a : Affine) (n : Int) (x : Nat → Nat) :
    (a.offset n).eval x = a.eval x + n := by
  simp only [offset, eval]
  omega

theorem Affine.eval_literal (n : Int) (x : Nat → Nat) : (literal n).eval x = n := by
  exact Int.zero_add n

theorem Affine.eval_variable (k : Nat) (x : Nat → Nat) : (Affine.variable k).eval x = (x k : Int) := by
  simp only [Affine.variable, eval, Lin.eval_basis, Int.add_zero]

def Affine.eq (a b : Affine) : AFml := .eq (a.coeff.sub b.coeff) (b.constant - a.constant)
def Affine.le (a b : Affine) : AFml := .le (a.coeff.sub b.coeff) (b.constant - a.constant)

theorem Affine.holds_eq (a b : Affine) (x : Nat → Nat) :
    (a.eq b).holds x ↔ a.eval x = b.eval x := by
  simp only [eq, AFml.holds, Lin.eval_sub, eval]
  omega

theorem Affine.holds_le (a b : Affine) (x : Nat → Nat) :
    (a.le b).holds x ↔ a.eval x ≤ b.eval x := by
  simp only [le, AFml.holds, Lin.eval_sub, eval]
  omega

end Solidity.Linear
