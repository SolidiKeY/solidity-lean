import Solidity.Calculus.LinearCountermodel
import Solidity.Calculus.LinearSyntax

/-!
# Complete arithmetic decisions and extracted assignments

These exercise the arithmetic intermediate language, not yet a complete
Solidity verifier. Counterassignments come from reachable derivative nodes,
including a value outside a small candidate pool.
-/

namespace Solidity.Examples.LinearDecision

open Solidity.Linear

/-- Direct conjunction projections normalize before the bit-search graph. -/
def projectLeft : AFml := linear!{ ([1] = 2 ∧ [0, 1] = 3) → [1] = 2 }
def projectRight : AFml := linear!{ ([1] = 2 ∧ [0, 1] = 3) → [0, 1] = 3 }
example : projectLeft.norm = .tt := by decide +kernel
example : projectRight.norm = .tt := by decide +kernel

/-- Matching only a coefficient or reversing the implication is insufficient. -/
def wrongProjection : AFml := linear!{ ([1] = 2 ∧ [0, 1] = 3) → [0, 1] = 4 }
def reverseProjection : AFml := linear!{ [1] = 2 → ([1] = 2 ∧ [0, 1] = 3) }
example : wrongProjection.norm != .tt := by decide +kernel
example : reverseProjection.norm != .tt := by decide +kernel
example : wrongProjection.check (fun i => if i = 0 then 2 else 3) = false := by decide +kernel
example : reverseProjection.check (fun _ => 2) = false := by decide +kernel

/-- info: [true, true, false, false] -/
#guard_msgs in #eval [projectLeft.decide, projectRight.decide,
  wrongProjection.decide, reverseProjection.decide]

/-- info: 'Solidity.Linear.AFml.holds_nImp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AFml.holds_nImp

def evenNotOdd : AFml := linear!{ ¬([2, -2] = 1) }

/-- The quotation is notation only; the kernel sees the same arithmetic. -/
example : evenNotOdd = AFml.not (.eq [2, -2] 1) := rfl
example : linear!{ true } = AFml.tt := rfl
example : linear!{ false } = AFml.ff := rfl
example : linear!{ true ∧ false → ¬true } = AFml.imp (.and .tt .ff) (.not .tt) := rfl
example : (true : Bool) = Bool.true := rfl

/-- info: "¬((2)*x0 + (-2)*x1 = 1)" -/
#guard_msgs in #eval evenNotOdd.pp

example : evenNotOdd.decide = true := by decide +kernel
theorem evenNotOdd_valid : evenNotOdd.Valid := (AFml.decide_iff _).1 (by decide +kernel)

def missesSeventeen : AFml := linear!{ ¬([1] = 17) }
def seventeenModel := missesSeventeen.countermodel (by decide +kernel)

example : seventeenModel.val 0 = 17 := by decide +kernel
example : missesSeventeen.check seventeenModel.val = false := by decide +kernel
example : missesSeventeen.countermodelValues (by decide +kernel) = [17] := by decide +kernel

def negativeCoefficients : AFml := linear!{ ¬([-1] = (-17)) }
def negativeModel := negativeCoefficients.countermodel (by decide +kernel)
example : negativeModel.val 0 = 17 := by decide +kernel
example : negativeCoefficients.check negativeModel.val = false := by decide +kernel

def twoVariables : AFml := linear!{ ¬([1, 2] = 25) }
def twoVariablesModel := twoVariables.countermodel (by decide +kernel)

example : twoVariables.check twoVariablesModel.val = false := by decide +kernel
example : twoVariablesModel.val 0 + 2 * twoVariablesModel.val 1 = 25 := by decide +kernel

/-- Simplification can decide a constant formula without any bit search. -/
example : (AFml.eq [0, 0] 0).decide = true := by decide +kernel
example : (AFml.eq [] 1).decide = false := by decide +kernel
example : (AFml.eq [] 1).check ((AFml.eq [] 1).countermodel (by decide +kernel)).val = false := by
  decide +kernel

def implication : AFml := linear!{ [1] = 3 → [1] = 4 }
example : implication.check (implication.countermodel (by decide +kernel)).val = false := by
  decide +kernel

def differentWidths : AFml := linear!{ [1] = 3 → [1, 1] = 4 }
example : differentWidths.check (differentWidths.countermodel (by decide +kernel)).val = false := by
  decide +kernel

example : evenNotOdd.verify.isLeft = true := by decide +kernel
example : missesSeventeen.verify.isRight = true := by decide +kernel

def bounded : AFml := linear!{ [1] ≤ 17 → [2] ≤ 34 }
example : bounded.decide = true := by decide +kernel

def upperBoundary : AFml := linear!{ [1] ≤ 255 → [1] ≤ 254 }
example : upperBoundary.countermodelValues (by decide +kernel) = [255] := by decide +kernel

def oddBoundary : AFml := linear!{ [2] ≤ 17 }
example : oddBoundary.check (oddBoundary.countermodel (by decide +kernel)).val = false := by
  decide +kernel

example : (linear!{ ¬([2] ≤ (-1)) }).decide = true := by decide +kernel
example : (linear!{ [-1] ≤ 0 }).decide = true := by decide +kernel
example : (linear!{ [] ≤ (-1) }).decide = false := by decide +kernel
example : (linear!{ [] ≤ 0 }).decide = true := by decide +kernel

/-- info: "((1)*x0 ≤ 17)" -/
#guard_msgs in #eval (linear!{ [1] ≤ 17 }).pp

/-- info: 'Solidity.Linear.AFml.decide_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AFml.decide_iff

/-- info: 'Solidity.Linear.AFml.countermodel_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AFml.countermodel_check

/-- info: 'Solidity.Linear.AFml.countermodelValues_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AFml.countermodelValues_check

end Solidity.Examples.LinearDecision
