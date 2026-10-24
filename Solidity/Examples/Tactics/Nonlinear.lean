import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Close

/-!
# Nonlinear arithmetic beyond literal bounds

The first-order examples pin each new instance family. The final theorem
uses the public scoped strategy on actual checked Solidity multiplications.
-/
namespace Solidity.Examples.Tactics.Nonlinear

open Solidity.Close

/-- A symbolic comparison scales by a nonnegative, unbounded factor. -/
theorem positiveScale (x y z : Int) (hxy : x ≤ y) (hz : 0 ≤ z) : x*z ≤ y*z := by
  sol_close_nonlin
  grind

/-- A nonpositive factor reverses the symbolic comparison, including zero. -/
theorem negativeScale (x y z : Int) (hxy : x ≤ y) (hz : z ≤ 0) : y*z ≤ x*z := by
  sol_close_nonlin
  grind

/-- Strict comparisons are converted to the integer successor form. -/
theorem strictScale (x y z : Int) (hxy : x < y) (hz : 0 < z) : x*z < y*z := by
  sol_close_nonlin
  grind

/-- A literal coefficient does not make a symbolic bound nonlinear. -/
theorem coefficientScale (x y z : Int) (hxy : 2*x ≤ y) (hz : 0 ≤ z) :
    (2*x)*z ≤ y*z := by
  sol_close_nonlin
  grind

/-- Coefficient bounds also scale in the reversed direction. -/
theorem coefficientNegative (x y z : Int) (hxy : 3*x ≤ y) (hz : z ≤ 0) :
    y*z ≤ (3*x)*z := by
  sol_close_nonlin
  grind

/-- Both intervals have symbolic endpoints; no literal upper bound is supplied. -/
theorem orderedProduct (a b c d : Int) (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : 0 ≤ c) (hcd : c ≤ d) : a*c ≤ b*d := by
  sol_close_nonlin
  grind

/-- A compound factor's square needs no bound on its atom. -/
theorem compoundSquare (x : Int) : 0 ≤ (x+1)*(x+1) := by
  sol_close_nonlin
  grind

/-- The selected square of a difference supplies this cross-product inequality. -/
theorem crossProduct (x y : Int) : 2*x*y ≤ x*x+y*y := by
  sol_close_nonlin
  grind

/-- Sixteen irrelevant products cannot consume the target's factor budget. -/
example (x u v : Int) (_noise : (u+0)*(v+0) = (u+0)*(v+0) ∧
      (u+1)*(v+1) = (u+1)*(v+1) ∧
      (u+2)*(v+2) = (u+2)*(v+2) ∧
      (u+3)*(v+3) = (u+3)*(v+3) ∧
      (u+4)*(v+4) = (u+4)*(v+4) ∧
      (u+5)*(v+5) = (u+5)*(v+5) ∧
      (u+6)*(v+6) = (u+6)*(v+6) ∧
      (u+7)*(v+7) = (u+7)*(v+7) ∧
      (u+8)*(v+8) = (u+8)*(v+8) ∧
      (u+9)*(v+9) = (u+9)*(v+9) ∧
      (u+10)*(v+10) = (u+10)*(v+10) ∧
      (u+11)*(v+11) = (u+11)*(v+11) ∧
      (u+12)*(v+12) = (u+12)*(v+12) ∧
      (u+13)*(v+13) = (u+13)*(v+13) ∧
      (u+14)*(v+14) = (u+14)*(v+14) ∧
      (u+15)*(v+15) = (u+15)*(v+15)) :
    0 ≤ (x+1)*(x+1) := by
  sol_close_nonlin
  assumption

/-- The atom budget is enforced and leaves the original context usable. -/
example (a b c d e : Int) (_h : 0 ≤ (a+b+c+d+e)*(a+b+c+d+e)) : True := by
  fail_if_success sol_close_nonlin
  trivial

local instance : InContract := ⟨StandardExample⟩
open scoped Solidity.Scoped

/-- Checked source multiplications preserve a symbolic input order. -/
theorem checkedProducts : ⊨ᶠ dl!{ ∀ uint x; ∀ uint y; ∀ uint z;
    (x <= y ∧ y <= 1000 ∧ z <= 1000) →
    [ uint a = x*z; uint b = y*z; ] a <= b } := by
  sol_prove
  all_goals sol_leaf
  all_goals sol_close

end Solidity.Examples.Tactics.Nonlinear
