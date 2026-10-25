import Solidity.Calculus.Decision
import Solidity.Examples.ReadRealization

/-!
# The closer's decision (M7), on products with a literal factor

`decideLeaf` (`Calculus/Decision.lean`) answers on `Fml.Covered`: a
checked product by a literal on either side (`2 * x`, `x * 3`, also over a
storage read) is now in it, and was refused before M7 (the arithmetic
compiler read only `+` and `-`).  The verdicts are the compiled ones: the
kernel's arithmetic decision over 256-bit codes is too deep for the
language server (as in `Examples/AutoComplete.lean`).

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

/-- Leaves of the named fragment: an array-property hypothesis, and one
outside it (the index read as a value). -/
def apf : Fml Bank [] := dl!{ (∀ uint k; k < 10 → balances[k] == 0) → balances[5] == 0 }
def notApf : Fml Bank [] := dl!{ (∀ uint k; balances[k] == k) → balances[5] == 5 }

end

def verdict {C : Contract} (φ : Fml C []) : String :=
  match decideLeaf φ with
  | .proved => "proved"
  | .refuted _ => "refuted"
  | .unknown => "unknown"

theorem double_covered : double.Covered = true := by decide +kernel

/-- `decideLeaf_proved_iff`, applied: the verdict is exact. -/
theorem double_iff : decideLeaf double = .proved ↔ Fml.Valid double :=
  decideLeaf_proved_iff double_covered

/-- info: ["proved", "proved", "refuted", "proved"] -/
#guard_msgs in #eval [double, triple, doubleReturns, doubleBalance].map verdict

/-- info: [true, true, true, true] -/
#guard_msgs in #eval [double, triple, doubleReturns, doubleBalance].map Fml.Covered

/-- info: [true, false] -/
#guard_msgs in #eval [apf, notApf].map (Fml.inTarget {})

/-- info: ["unknown", "unknown"] -/
#guard_msgs in #eval [apf, notApf].map verdict

end Solidity.Examples.Decision
