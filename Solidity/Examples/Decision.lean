import Solidity.Calculus.Decision
import Solidity.Examples.ReadRealization

/-!
# The closer's decision (M7): the features added to its fragment

`decideLeaf` (`Calculus/Decision.lean`) answers on `Fml.Covered`.  The
features M7 added to it, each refused before (`dependentReduction?` gave
`none`): a checked product by a literal on either side (`2 * x`, `x * 3`,
also over a storage read); a universal quantifier in the consequent of
an implication (a postcondition's `\forall`), moved to the prefix; unary
`-` and `~`, compiled as affine codes; and the operators cut into fresh
atoms (`Calculus/QuotientCut.lean`): `int(·)`, `uint(·)`, `/`, `%`, `>>`,
`<<` and a low mask `& (2^k - 1)` by a literal, `+%`, `-%`.  Each has a
proved and a refuted verdict pinned and a kernel-checked covered leaf.  The
verdicts are the compiled ones: the kernel's arithmetic decision over
256-bit codes is too deep for the language server (as in
`Examples/AutoComplete.lean`); the theorems' fragment checks are the
kernel's, the `#eval` pins the compiled ones.

Presburger quantifiers past the prefix (M7, step 4) are decided by the
quantified pipeline (`quantReduction?`, `QFml.decide_iff`): an `∃` or a
`∀` in a hypothesis, an alternation `∀∃`, beside a storage write; a
quantifier whose body reads storage is still outside (`evenRead`).

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

/-- Presburger quantifiers (M7, step 4): an `∃` in a hypothesis, a `∀` in
one, an alternation `∀∃`, and false variants; one beside a storage write. -/
def evenHyp : Fml Bank [] := dl!{ ∀ uint x; (∃ uint y; y < 5 ∧ x == y + y) → x != 3 }
def evenHypBad : Fml Bank [] := dl!{ ∀ uint x; (∃ uint y; y < 5 ∧ x == y + y) → x != 4 }
def leastHyp : Fml Bank [] := dl!{ ∀ uint x; (∀ uint y; x <= y) → x == 0 }
def above : Fml Bank [] := dl!{ ∀ uint x; x < 10 → (∃ uint y; x < y) }
def below : Fml Bank [] := dl!{ ∀ uint x; (∃ uint y; y < x) }
def evenWrite : Fml Bank [] :=
  dl!{ ∀ uint k; (∃ uint y; y + y == k) → [ balances[k] = k; ] balances[k] != 1 }
def oddWrite : Fml Bank [] :=
  dl!{ ∀ uint k; (∃ uint y; y + y + 1 == k) → [ balances[k] = k; ] balances[k] != 1 }

/-- A quantifier whose body reads storage is outside (step 4's remainder). -/
def evenRead : Fml Bank [] := dl!{ ∀ uint k; (∃ uint y; balances[k] == y + y) → balances[k] != 7 }

/-! ### Unary minus, the complement and the conversions (M7, plan step 1) -/

def negOk : Fml Bank [] := dl!{ ∀ int x; x > 0 → [ int y = -x; ] y + x == 0 }
/-- `-x` overflows at `-2^255`, so under the diamond it must return. -/
def negBad : Fml Bank [] := dl!{ ∀ int x; ⟨ int y = -x; ⟩ y + x == 0 }
def bnotOk : Fml Bank [] := dl!{ ∀ uint x; [ uint y = ~x; uint z = ~0; ] y + x == z }
def bnotBad : Fml Bank [] := dl!{ ∀ uint x; [ uint y = ~x; ] y < x }
def toIntOk : Fml Bank [] := dl!{ ∀ uint x; x < 100 → [ int y = int(x); ] y >= 0 }
/-- A word past `2^255` reads negative. -/
def toIntBad : Fml Bank [] := dl!{ ∀ uint x; [ int y = int(x); ] y >= 0 }
def toUintOk : Fml Bank [] := dl!{ ∀ int x; x >= 0 → [ uint y = uint(x); ] y <
  57896044618658097711785492504343953926634992332820282019728792003956564819968 }
def toUintBad : Fml Bank [] := dl!{ ∀ int x; [ uint y = uint(x); ] y <
  57896044618658097711785492504343953926634992332820282019728792003956564819968 }

/-! ### Quotients, shifts, masks and wrapping arithmetic (M7, plan step 2) -/

def divOk : Fml Bank [] := dl!{ ∀ uint x; [ uint y = x / 3; ] y * 3 <= x }
def divBad : Fml Bank [] := dl!{ ∀ uint x; [ uint y = x / 3; uint z = y * 3; ] z == x }
def modOk : Fml Bank [] := dl!{ ∀ uint x; [ uint y = x % 8; ] y < 8 }
def modBad : Fml Bank [] := dl!{ ∀ uint x; [ uint y = x % 8; ] y < 7 }
def shrOk : Fml Bank [] := dl!{ ∀ uint x; [ uint y = x >> 4; ] y <= x }
/-- `>>` on `int` rounds toward `-∞`. -/
def shrInt : Fml Bank [] := dl!{ ∀ int x; x < 0 → [ int y = x >> 1; ] y < 0 }
def shrIntBad : Fml Bank [] := dl!{ ∀ int x; [ int y = x >> 1; ] y < x }
/-- A left shift by `4`: in the fragment (`shl_covered`), its verdict past the
decision's reach in practice (`docs/automation.md`, M7). -/
def shlOk : Fml Bank [] := dl!{ ∀ uint x; x < 16 → [ uint y = x << 4; uint z = x * 16; ] y == z }
def shlZero : Fml Bank [] := dl!{ ∀ uint x; [ uint y = x << 0; ] y == x }
def shlFar : Fml Bank [] := dl!{ ∀ uint x; [ uint y = x << 300; ] y == x }
def maskOk : Fml Bank [] := dl!{ ∀ uint x; [ uint y = x & 7; ] y < 8 }
def maskBad : Fml Bank [] := dl!{ ∀ uint x; [ uint y = 7 & x; ] y < 7 }
def addWOk : Fml Bank [] := dl!{ ∀ uint x; ∀ uint z; [ uint y = x +% z; uint w = y -% z; ] w == x }
/-- `x +% 1` wraps to `0` at `2^256 - 1`. -/
def addWBad : Fml Bank [] := dl!{ ∀ uint x; [ uint y = x +% 1; ] y > x }
def subWOk : Fml Bank [] := dl!{ ∀ uint x; [ uint y = x -% 1; uint w = y +% 1; ] w == x }
def subWBad : Fml Bank [] := dl!{ ∀ uint x; [ uint y = x -% 1; ] y < x }

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

-- `decideLeaf` on Presburger quantifiers: each verdict exact
-- (`QFml.decide_iff`), each refutation a certified state.
/-- info: ["proved", "refuted", "proved", "proved", "refuted", "proved", "refuted", "unknown"] -/
#guard_msgs in
#eval [evenHyp, evenHypBad, leastHyp, above, below, evenWrite, oddWrite, evenRead].map verdict

/-- info: [true, true, true, true, true, true, true, false] -/
#guard_msgs in
#eval [evenHyp, evenHypBad, leastHyp, above, below, evenWrite, oddWrite, evenRead].map Fml.Covered

theorem evenHyp_covered : evenHyp.Covered = true := by decide +kernel

/-- `decideLeaf_complete`, applied to an `∃` in a hypothesis. -/
theorem evenHyp_answers : decideLeaf evenHyp ≠ .unknown := decideLeaf_complete evenHyp_covered

/-- info: ["proved", "refuted", "proved", "refuted", "proved", "refuted", "proved", "refuted"] -/
#guard_msgs in #eval [negOk, negBad, bnotOk, bnotBad, toIntOk, toIntBad, toUintOk, toUintBad].map verdict

/-- info: ["proved", "refuted", "proved", "refuted", "proved", "proved", "refuted"] -/
#guard_msgs in #eval [divOk, divBad, modOk, modBad, shrOk, shrInt, shrIntBad].map verdict

/-- info: ["proved", "refuted", "proved", "refuted", "proved", "refuted", "proved", "refuted"] -/
#guard_msgs in #eval [shlZero, shlFar, maskOk, maskBad, addWOk, addWBad, subWOk, subWBad].map verdict

/-- info: true -/
#guard_msgs in #eval [negOk, negBad, bnotOk, bnotBad, toIntOk, toIntBad, toUintOk, toUintBad, divOk,
  divBad, modOk, modBad, shrOk, shrInt, shrIntBad, shlOk, shlZero, shlFar, maskOk, maskBad, addWOk,
  addWBad, subWOk, subWBad].all Fml.Covered

/-! Kernel-checked coverage, one leaf a feature. -/

theorem neg_covered : negOk.Covered = true := by decide +kernel
theorem bnot_covered : bnotOk.Covered = true := by decide +kernel
theorem toInt_covered : toIntOk.Covered = true := by decide +kernel
theorem toUint_covered : toUintOk.Covered = true := by decide +kernel
theorem div_covered : divOk.Covered = true := by decide +kernel
theorem mod_covered : modOk.Covered = true := by decide +kernel
theorem shr_covered : shrInt.Covered = true := by decide +kernel
theorem shl_covered : shlOk.Covered = true := by decide +kernel
theorem mask_covered : maskOk.Covered = true := by decide +kernel
theorem addW_covered : addWOk.Covered = true := by decide +kernel
theorem subW_covered : subWOk.Covered = true := by decide +kernel

/-- `decideLeaf_proved_iff`, applied to a cut leaf. -/
theorem div_iff : decideLeaf divOk = .proved ↔ Fml.Valid divOk :=
  decideLeaf_proved_iff div_covered

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
