import Solidity.Calculus.Decision
import Solidity.Examples.ReadRealization

/-!
# The closer's decision (M7): products by a literal, nested quantifiers

`decideLeaf` (`Calculus/Decision.lean`) answers on `Fml.Covered`.  Two
features M7 added to it, each refused before (`dependentReduction?` gave
`none`): a checked product by a literal on either side (`2 * x`, `x * 3`,
also over a storage read), and a universal quantifier in the consequent of
an implication (a postcondition's `\forall`), moved to the prefix.  The
verdicts are the compiled ones: the kernel's arithmetic decision over
256-bit codes is too deep for the language server (as in
`Examples/AutoComplete.lean`); the theorems' fragment checks are the
kernel's, the `#eval` pins the compiled ones.

`Fml.inTarget` is the fragment the user named, on program-free leaves: a
negative-position quantifier over a mapping is in it exactly when it is in
the array property fragment, and `decideLeaf` still answers `unknown` on
it (`docs/automation.md`, M7).
-/

namespace Solidity.Examples.Decision

open Solidity.Decide

def Bank : Contract := contract!{ mapping(uint => uint) balances; }

section

local instance : InContract := ⟨Bank⟩

/-- Doubling by a literal on the left, below the overflow. -/
def double : Fml Bank [] := dl!{ ∀ uint x; x < 100 → [ uint y = 2 * x; ] y == x + x }

/-- On the right. -/
def triple : Fml Bank [] := dl!{ ∀ uint x; x < 100 → [ uint y = x * 3; ] y == x + x + x }

/-- Under the diamond the doubling must return: it overflows at `2^255`. -/
def doubleReturns : Fml Bank [] := dl!{ ∀ uint x; ⟨ uint y = 2 * x; ⟩ y == x + x }

/-- A storage read doubled. -/
def doubleBalance : Fml Bank [] :=
  dl!{ ∀ uint k; balances[k] < 7 → [ balances[k] = 2 * balances[k]; ] balances[k] < 14 }

/-- A quantifier in a consequent, moved to the prefix (`LFml.prenex`). -/
def nested : Fml Bank [] := dl!{ ∀ uint x; x < 10 → ∀ uint y; y < 10 → x + y < 20 }

/-- A postcondition's `\forall` past a write, and its refutation. -/
def written : Fml Bank [] :=
  dl!{ ∀ uint k; [ balances[k] = 1; ] (∀ uint j; j == k → balances[j] == 1) }
def writtenBad : Fml Bank [] := dl!{ ∀ uint k; [ balances[k] = 1; ] (∀ uint j; balances[j] == 1) }

/-- Leaves of the named fragment: an array-property hypothesis, and one
outside it (the index read as a value). -/
def apf : Fml Bank [] := dl!{ (∀ uint k; k < 10 → balances[k] == 0) → balances[5] == 0 }
def notApf : Fml Bank [] := dl!{ (∀ uint k; balances[k] == k) → balances[5] == 5 }

/-- Guards outside the fragment: a disequality, arithmetic on the index. -/
def guardNe : Fml Bank [] := dl!{ (∀ uint k; k != 3 → balances[k] == 0) → balances[5] == 0 }
def guardArith : Fml Bank [] := dl!{ (∀ uint k; k + 1 < 10 → balances[k] == 0) → balances[5] == 0 }

end

def verdict {C : Contract} (φ : Fml C []) : String :=
  match decideGoal φ with
  | .proved => "proved"
  | .refuted _ => "refuted"
  | .unknown => "unknown"

theorem double_covered : double.Covered = true := by decide +kernel

/-- `decideGoal_complete`, applied: no hash, so no premise. -/
theorem double_answers : decideGoal double ≠ .unknown :=
  decideGoal_complete double_covered rfl

theorem nested_covered : nested.Covered = true := by decide +kernel

/-- `decideLeaf_proved_iff`, applied: the verdict is exact. -/
theorem double_iff : decideLeaf double = .proved ↔ Fml.Valid double :=
  decideLeaf_proved_iff double_covered

/-- info: ["proved", "proved", "refuted", "proved"] -/
#guard_msgs in #eval [double, triple, doubleReturns, doubleBalance].map verdict

/-- info: [true, true, true, true] -/
#guard_msgs in #eval [double, triple, doubleReturns, doubleBalance].map Fml.Covered

/-- info: ["proved", "proved", "refuted"] -/
#guard_msgs in #eval [nested, written, writtenBad].map verdict

/-- info: [true, false, false, false] -/
#guard_msgs in #eval [apf, notApf, guardNe, guardArith].map (Fml.inTarget {})

/-- A program-free leaf both covered and in the named fragment. -/
theorem nested_inTarget : nested.inTarget {} = true := by decide +kernel

/-- `DecisionTheorem` is not yet true: `apf` is in the fragment, and
answered `unknown`. -/
theorem apf_inTarget : apf.inTarget {} = true := by decide +kernel

/-- info: ["unknown", "unknown"] -/
#guard_msgs in #eval [apf, notApf].map verdict

end Solidity.Examples.Decision
