import Solidity.Calculus.Decision
import Solidity.Examples.ReadRealization
import Solidity.Examples.DecisionHashes

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
`∀` in a hypothesis, an alternation `∀∃`, beside a storage write, and one
whose body reads storage at no variable it binds (`evenRead`: the read
hoisted out, `hoistPrep`).

`Fml.inTarget` is the fragment the user named, on program-free leaves: a
negative-position quantifier over a mapping is in it only when it is in
the array property fragment (a conservative reading).  `decideLeaf` decides such a block over a
mapping at a root (M7, step 5: `apf`, instantiated at the index set,
`apfPrep`), and a block over an inner mapping whose bound index is the
last (`rowApf`).  Two bound indices on one
path (`gridApf`) and a strict comparison of two bound variables
(`strictSorted`) are outside the named fragment (`docs/automation.md`, M7).
-/

namespace Solidity.Examples.Decision

open Solidity.Decide

-- The verdicts run one after another: run in parallel, their evaluations
-- together overflow a command-line `lean`'s stack (exit 135).
set_option Elab.async false

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

/-- A quantifier whose body reads storage at no variable it binds: the read
hoisted out (step 4's remainder), and a false variant. -/
def evenRead : Fml Bank [] := dl!{ ∀ uint k; (∃ uint y; balances[k] == y + y) → balances[k] != 7 }
def evenReadBad : Fml Bank [] := dl!{ ∀ uint k; (∃ uint y; balances[k] == y + y) → balances[k] != 8 }

/-! ### The array property fragment (M7, plan step 5) -/

/-- Instantiated at `0`, `5`, `10`, `11`; false variants, a key past the
guard, a two-sided guard and its strict variant. -/
def apfBad : Fml Bank [] := dl!{ (∀ uint k; k < 10 → balances[k] == 0) → balances[5] == 1 }
def apfOut : Fml Bank [] := dl!{ (∀ uint k; k < 10 → balances[k] == 0) → balances[12] == 0 }
def apfTwo : Fml Bank [] :=
  dl!{ (∀ uint k; 3 <= k && k < 10 → balances[k] == 7) → balances[4] + balances[9] == 14 }
def apfTwoBad : Fml Bank [] := dl!{ (∀ uint k; 3 < k && k < 10 → balances[k] == 7) → balances[3] == 7 }

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
/-- A left shift by `4`: in the fragment (`shl_covered`), `x` related to `y`
through `2^256`; decided by the walk (`AFml.fastVerify`, `docs/automation.md`,
M7). -/
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

/-! ### KeY `int` (M7, plan step 3)

`toInt(x)` widens a `uint` to KeY's unbounded `int` (`Srt.kint`): `+`, `-`
and products by a literal never overflow there, and the comparisons are
exact (`KIntValue`, `CheckedInt`). -/

def kintOk : Fml Bank [] := dl!{ ∀ uint x; toInt(x) + 1 > toInt(x) }
def kintBad : Fml Bank [] := dl!{ ∀ uint x; ∀ uint y; toInt(x) - toInt(y) < 5 }
/-- A sum past `2^256` is no overflow. -/
def kintWide : Fml Bank [] := dl!{ ∀ uint x; ∀ uint y; toInt(x) + toInt(y) >= toInt(x) }
/-- The difference of two words is negative where the second is larger. -/
def kintNeg : Fml Bank [] := dl!{ ∀ uint x; ∀ uint y; x < y → toInt(x) - toInt(y) < 0 }
def kintScale : Fml Bank [] := dl!{ ∀ uint x; 3 * toInt(x) - toInt(x) = toInt(x) * 2 }
def kintScaleBad : Fml Bank [] := dl!{ ∀ uint x; 3 * toInt(x) <= toInt(x) * 2 }
/-- A transaction field widened. -/
def kintValue : Fml Bank [] := dl!{ toInt(msg.value) + toInt(msg.value) >= toInt(msg.value) }
/-- A storage read widened, past a write. -/
def kintRead : Fml Bank [] :=
  dl!{ ∀ uint k; [ balances[k] = 7; ] toInt(balances[k]) - 7 = 0 }

/-! ### Ledger reads (M7, plan step 3)

`net(a)` reads the ledger of the starting state, a KeY `int` per address:
each read is cut to a read at a fresh constant, consistent with the others
at equal addresses (`LFml.ledgerCut`), its entry two natural codes of the
arithmetic (`LeafArithmeticZ`). -/

def netOk : Fml Bank [] := dl!{ ∀ uint a; net(a) = 7 → net(a) + 1 = 8 }
/-- Reads at equal addresses read equal entries. -/
def netSame : Fml Bank [] := dl!{ ∀ uint a; ∀ uint b; a == b → net(a) = net(b) }
/-- An entry may be negative. -/
def netNeg : Fml Bank [] := dl!{ ∀ uint a; net(a) >= 0 }
def netOther : Fml Bank [] := dl!{ ∀ uint a; ∀ uint b; net(a) = 7 → net(b) = 7 }
/-- A ledger entry against a storage read. -/
def netStore : Fml Bank [] := dl!{ ∀ uint a; net(a) = toInt(balances[a]) → net(a) >= 0 }
/-- Past a write to storage. -/
def netWrite : Fml Bank [] :=
  dl!{ ∀ uint a; [ balances[a] = 3; ] net(a) - toInt(balances[a]) < net(a) }
def netDistinct : Fml Bank [] := dl!{ ∀ uint a; ∀ uint b; net(a) < net(b) → a != b }
/-- Four reads: in the fragment (`netSwap_covered`), each read two codes and
each pair of reads a consistency premise; decided by the walk, the slowest
pin here (`docs/automation.md`, M7). -/
def netSwap : Fml Bank [] := dl!{ ∀ uint a; ∀ uint b; net(a) + net(b) = net(b) + net(a) }

/-- Guards outside the fragment: a disequality, arithmetic on the index. -/
def guardNe : Fml Bank [] := dl!{ (∀ uint k; k != 3 → balances[k] == 0) → balances[5] == 0 }
def guardArith : Fml Bank [] := dl!{ (∀ uint k; k + 1 < 10 → balances[k] == 0) → balances[5] == 0 }

end

/-- Nested mappings. -/
def Allow : Contract := contract!{ mapping(uint => mapping(uint => uint)) allow; mapping(uint => uint) balances; }

section

local instance : InContract := ⟨Allow⟩

/-- A block over an inner mapping, its bound index the last (`apfPrep`,
`MShape`): decided, and false variants (another row, a key past the guard);
the row a parameter. -/
def rowApf : Fml Allow [] := dl!{ (∀ uint k; k < 10 → allow[3][k] == 0) → allow[3][5] == 0 }
def rowBad : Fml Allow [] := dl!{ (∀ uint k; k < 10 → allow[3][k] == 0) → allow[4][5] == 0 }
def rowOut : Fml Allow [] := dl!{ (∀ uint k; k < 10 → allow[3][k] == 0) → allow[3][12] == 0 }
def rowVar : Fml Allow [] := dl!{ ∀ uint x; (∀ uint k; k < 10 → allow[x][k] == 0) → allow[x][5] == 0 }
/-- A key the solver places past `2^200`: refuted by a rebuilt mapping of a
dozen entries, the keys between the guard's bound and the key read at the
key (`lastIn`, `lastBound`), not `2^200` entries. -/
def rowFar : Fml Allow [] :=
  dl!{ ∀ uint x; (∀ uint k; k < 10 → allow[3][k] == 0) →
    x > 1606938044258990275541962092341162602522202993782792835301376 → allow[3][x] == 0 }
/-- Outside the named fragment: two bound indices on one path, and a
strict comparison of two bound variables. -/
def gridApf : Fml Allow [] := dl!{ (∀ uint i; ∀ uint j; allow[i][j] == 0) → allow[1][2] == 0 }
def strictSorted : Fml Allow [] :=
  dl!{ (∀ uint i; ∀ uint j; i < j → balances[i] < balances[j]) → balances[1] < balances[2] }
/-- Inside: the non-strict comparison of two bound variables, and one bound
index on a nested path. -/
def sortedLe : Fml Allow [] :=
  dl!{ (∀ uint i; ∀ uint j; i <= j → balances[i] <= balances[j]) → balances[2] <= balances[5] }
def columnApf : Fml Allow [] := dl!{ (∀ uint i; i < 10 → allow[i][3] == 0) → allow[1][3] == 0 }

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
/-- info: ["proved", "refuted", "proved", "proved", "refuted", "proved", "refuted", "proved", "refuted"] -/
#guard_msgs in
#eval [evenHyp, evenHypBad, leastHyp, above, below, evenWrite, oddWrite, evenRead, evenReadBad].map verdict

/-- info: [true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval [evenHyp, evenHypBad, leastHyp, above, below, evenWrite, oddWrite, evenRead, evenReadBad].map Fml.Covered

/-- A read in a quantifier, hoisted: kernel-checked coverage. -/
theorem evenRead_covered : evenRead.Covered = true := by decide +kernel

theorem evenHyp_covered : evenHyp.Covered = true := by decide +kernel

/-- `decideLeaf_complete`, applied to an `∃` in a hypothesis. -/
theorem evenHyp_answers : decideLeaf evenHyp ≠ .unknown := decideLeaf_complete evenHyp_covered

/-- info: ["proved", "refuted", "proved", "refuted", "proved", "refuted", "proved", "refuted"] -/
#guard_msgs in #eval [negOk, negBad, bnotOk, bnotBad, toIntOk, toIntBad, toUintOk, toUintBad].map verdict

/-- info: ["proved", "refuted", "proved", "refuted", "proved", "proved", "refuted"] -/
#guard_msgs in #eval [divOk, divBad, modOk, modBad, shrOk, shrInt, shrIntBad].map verdict

/-- info: ["proved", "refuted", "proved", "refuted", "proved", "refuted", "proved", "refuted"] -/
#guard_msgs in #eval [shlZero, shlFar, maskOk, maskBad, addWOk, addWBad, subWOk, subWBad].map verdict

-- `x << 4` against `x * 16`: decided by the walk (M7, the running time).
/-- info: "proved" -/
#guard_msgs in #eval verdict shlOk

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

/-- info: ["proved", "refuted", "proved", "proved", "proved", "refuted", "proved", "proved"] -/
#guard_msgs in #eval [kintOk, kintBad, kintWide, kintNeg, kintScale, kintScaleBad, kintValue,
  kintRead].map verdict

/-- info: true -/
#guard_msgs in #eval [kintOk, kintBad, kintWide, kintNeg, kintScale, kintScaleBad, kintValue,
  kintRead].all Fml.Covered

theorem kint_covered : kintOk.Covered = true := by decide +kernel
theorem kintScale_covered : kintScale.Covered = true := by decide +kernel

/-- `decideLeaf_proved_iff`, applied to a KeY `int` leaf. -/
theorem kint_iff : decideLeaf kintOk = .proved ↔ Fml.Valid kintOk :=
  decideLeaf_proved_iff kint_covered

/-- info: ["proved", "proved", "refuted", "refuted", "proved", "proved", "proved"] -/
#guard_msgs in #eval [netOk, netSame, netNeg, netOther, netStore, netWrite, netDistinct].map verdict

/-- info: true -/
#guard_msgs in #eval [netOk, netSame, netNeg, netOther, netStore, netWrite, netDistinct].all Fml.Covered

-- Four ledger reads: decided by the walk (M7, the running time).
/-- info: "proved" -/
#guard_msgs in #eval verdict netSwap

theorem net_covered : netOk.Covered = true := by decide +kernel
theorem netSame_covered : netSame.Covered = true := by decide +kernel
theorem netSwap_covered : netSwap.Covered = true := by decide +kernel

/-- `decideLeaf_proved_iff`, applied to a leaf that reads the ledger. -/
theorem net_iff : decideLeaf netOk = .proved ↔ Fml.Valid netOk :=
  decideLeaf_proved_iff net_covered

/-- `decideLeaf_proved_iff`, applied to a cut leaf. -/
theorem div_iff : decideLeaf divOk = .proved ↔ Fml.Valid divOk :=
  decideLeaf_proved_iff div_covered

/-- info: [true, false, false, false] -/
#guard_msgs in #eval [apf, notApf, guardNe, guardArith].map (Fml.inTarget {})

/-- A program-free leaf both covered and in the named fragment. -/
theorem nested_inTarget : nested.inTarget {} = true := by decide +kernel

/-- `apf` is in the named fragment, and decided (below). -/
theorem apf_inTarget : apf.inTarget {} = true := by decide +kernel

/-- info: ["proved", "unknown"] -/
#guard_msgs in #eval [apf, notApf].map verdict

/-! Array property blocks (M7, step 5): each verdict exact, each refutation
a state whose mapping holds, at each key, what the key's floor in the
index set held (`MRoot.surgery`). -/

/-- info: ["proved", "refuted", "refuted", "proved", "refuted"] -/
#guard_msgs in #eval [apf, apfBad, apfOut, apfTwo, apfTwoBad].map verdict

/-- info: [true, true, true, true, true] -/
#guard_msgs in #eval [apf, apfBad, apfOut, apfTwo, apfTwoBad].map Fml.Covered

theorem apf_covered : apf.Covered = true := by decide +kernel
theorem apfBad_covered : apfBad.Covered = true := by decide +kernel

/-- `decideGoal_complete`, applied to an array property block. -/
theorem apf_answers : decideGoal apf ≠ .unknown := decideGoal_complete apf_covered rfl

/-- `decideLeaf_proved_iff`, applied: the false variant is not valid. -/
theorem apfBad_iff : decideLeaf apfBad = .proved ↔ Fml.Valid apfBad :=
  decideLeaf_proved_iff apfBad_covered

/-! A block over an inner mapping (`allow[3][k]`): the floor construction
under every outer key (`MShape.rebuild`). -/

theorem rowApf_inTarget : rowApf.inTarget {} = true := by decide +kernel

/-- info: ["proved", "refuted", "refuted", "proved"] -/
#guard_msgs in #eval [rowApf, rowBad, rowOut, rowVar].map verdict

/-- info: [true, true, true, true] -/
#guard_msgs in #eval [rowApf, rowBad, rowOut, rowVar].map Fml.Covered

theorem rowApf_covered : rowApf.Covered = true := by decide +kernel
theorem rowBad_covered : rowBad.Covered = true := by decide +kernel

/-- The entries of `allow`'s rows in a state: the outer keys', each row's. -/
def allowRows (σ : State Allow []) : List Nat :=
  match σ.storage.get (f := "allow") (T := .ref (.mapping .uint (.ref (.mapping .uint (.prim .uint))))) rfl with
  | .map m d => (m.toList.map fun e => match e.2 with | .map m' _ => m'.toList.length) ++
      [match d with | .map m' _ => m'.toList.length]

/-- info: ("refuted", true, true) -/
#guard_msgs in #eval (verdict rowFar, rowFar.Covered, rowFar.inTarget {})

/-! The refutation's `allow`: the row it reads (`3`) and the default row,
twelve entries each (keys `0` to `11`: the guard's bound and its successor;
past them the default, the far key's word), where the floor construction
listed `2^200` keys. -/

/-- info: some [12, 12] -/
#guard_msgs in #eval match decideGoal rowFar with | .refuted σ => some (allowRows σ) | _ => none

/-- The far key's leaf, by the kernel. -/
theorem rowFar_covered : rowFar.Covered = true := by decide +kernel

/-- `decideGoal_complete`, applied to a block over an inner mapping. -/
theorem rowApf_answers : decideGoal rowApf ≠ .unknown := decideGoal_complete rowApf_covered rfl

/-- `decideLeaf_proved_iff`, applied: the verdict is exact. -/
theorem rowApf_iff : decideLeaf rowApf = .proved ↔ Fml.Valid rowApf :=
  decideLeaf_proved_iff rowApf_covered

/-- info: [false, false, true, true] -/
#guard_msgs in #eval [gridApf, strictSorted, sortedLe, columnApf].map (Fml.inTarget {})

/-- A two-variable block over a root: covered (nine instances, nineteen
reads), decided by the walk (`docs/automation.md`, M7). -/
theorem sortedLe_covered : sortedLe.Covered = true := by decide +kernel

/-- info: "proved" -/
#guard_msgs in #eval verdict sortedLe

/-! ## Counterexamples to `DecisionTheorem`

`DecisionTheorem` is not yet true.  One leaf per shape of `Fml.inTarget`
that `decideGoal` still answers `unknown` on: each in the fragment, by the
kernel, and answered `unknown` (the compiled verdicts below).  The list is
`docs/automation.md`'s (M7, "What is not proved"). -/

/-- The roots the shapes read. -/
def Gaps : Contract := contract!{
  struct Acc { uint v; bool live; }
  mapping(uint => mapping(uint => uint)) allow;
  mapping(uint => uint) balances;
  mapping(int => uint) ibal;
  mapping(bool => uint) flags;
  mapping(uint => Acc) accs;
  uint[] arr;
  uint[3] fixedArr;
}

section Gaps

local instance : InContract := ⟨Gaps⟩

/-! ### Quantifiers over contents outside `apfPrep`'s shapes -/

/-- A block whose bound index is not the last of its path (`m[i][3]`). -/
def gapColumn : Fml Gaps [] := dl!{ (∀ uint i; i < 10 → allow[i][3] == 0) → allow[1][3] == 0 }
/-- A root read at a bound index at two depths. -/
def gapTwoPaths : Fml Gaps [] :=
  dl!{ (∀ uint k; k < 10 → allow[3][k] == 0 && allow[k][3] == 0) → allow[3][5] == 0 }
/-- A block over a mapping keyed by `int`, and by `bool`. -/
def gapIntKeyed : Fml Gaps [] := dl!{ (∀ int k; k < 10 → ibal[k] == 0) → ibal[5] == 0 }
def gapBoolKeyed : Fml Gaps [] := dl!{ (∀ bool b; flags[b] == 0) → flags[true] == 0 }
/-- A block reading a struct's member past the bound index. -/
def gapStructValue : Fml Gaps [] := dl!{ (∀ uint k; k < 10 → accs[k].v == 0) → accs[5].v == 0 }
/-- A block over an array. -/
def gapArrayBlock : Fml Gaps [] :=
  dl!{ (∀ uint i; i < 3 → arr[i] == 0) → arr.length > 5 → arr[1] == 0 }
/-- A block over the ledger. -/
def gapLedgerBlock : Fml Gaps [] := dl!{ (∀ uint a; net(a) >= 0) → net(5) >= 0 }
/-- A guard with a partial ground operand (`x - 1` reverts at `0`). -/
def gapPartialGuard : Fml Gaps [] :=
  dl!{ ∀ uint x; (∀ uint k; k < x - 1 → balances[k] == 0) → x > 3 → balances[1] == 0 }
/-- A positive quantifier the prefix does not reach, reading at its variable. -/
def gapPositiveForall : Fml Gaps [] :=
  dl!{ ∀ uint x; balances[x] == 0 → (balances[x] == 0 && (∀ uint k; balances[k] == balances[k])) }

/-- Counterexamples once, decided by the arrays' pipeline (feature 10,
below): a dynamic array's element at a checked index, and a fixed array's
at a literal one. -/
def arrayRead : Fml Gaps [] := dl!{ ∀ uint i; i < arr.length → arr[i] == arr[i] }
def fixedRead : Fml Gaps [] := dl!{ fixedArr[1] == fixedArr[1] }

end Gaps

section GapTerms

/-! ### Memory, the ledger and KeY's `int` without quantifiers -/

/-- Leaves written with the constructors: `dl!` has no notation for them. -/
def litU {Γ : Ctx} (n : Nat) : Tm Gaps Γ (.val .uint) := .app0 (.lit (uintOfNat n))
def litI {Γ : Ctx} (n : Int) (h : PrimTy.int.inRange n = true := by decide) : Tm Gaps Γ (.val .int) :=
  .app0 (.lit (p := .int) ⟨n, h⟩)
def isT {Γ : Ctx} (b : Tm Gaps Γ (.val .bool)) : Fml Gaps Γ := .eq b (.app0 (.lit (p := .bool) true))
def xU : Tm Gaps [.val .uint] (.val .uint) := .pvV .here
def xI : Tm Gaps [.val .int] (.val .int) := .pvV .here
def allU (φ : Fml Gaps [.val .uint]) : Fml Gaps [] := .all (.user "x") .uint φ
def allI (φ : Fml Gaps [.val .int]) : Fml Gaps [] := .all (.user "x") .int φ

/-- A memory read: `∀ fresh s. len(s) > 0 → s[0] == 0`.  A counterexample
once, decided by the fresh arrays' lane (below). -/
def gapMemory : Fml Gaps [] := .allocAll (.user "s") (.array (.prim .uint))
  (.imp (isT (.app2 (.binop .gt rfl) (.app2 .mlen (.app0 .memory) (.pvI .here)) (litU 0)))
    (.eq (.app2 .read (.app0 .memory) (.app2 (.mat .dyn) (.pvI .here) (litU 0))) (litU 0)))
/-- A binder of KeY's unbounded `int`: `∀ int z. z + 1 > z`. -/
def gapKIntBinder : Fml Gaps [] := .bind .box (.user "z") .kint
  (isT (.app2 (.zcmp .gt rfl) (.app2 (.zbin .add rfl) (.pvZ .here) (.app0 (.zlit 1))) (.pvZ .here)))
/-- The ledger read past a payment: `{pay(x, 1)} net(x) >= 0`. -/
def gapLedgerWrite : Fml Gaps [] := allU (.upd .box (.snoc .nil (.pay xU (litU 1)))
  (isT (.app2 (.zcmp .ge rfl) (.app1 .net (.pvV .here)) (.app0 (.zlit 0)))))
/-- Fifty storage reads: past `Fml.exactBounded`'s bounds. -/
def gapManyReads : Fml Gaps [] :=
  let bal (n : Nat) : Tm Gaps [.val .uint] (.val .uint) :=
    .app2 .find (.app0 .storage) (.app2 (.at .map) (.app0 (.root "balances" rfl)) (litU n))
  allU (.imp (Fml.conjL ((List.range 50).map fun n => .eq (bal n) xU)) (.eq (bal 0) (bal 49)))

/-! ### Operators with a literal operand, not carried through the stages -/

/-- `/`, `%` at `int` by a literal. -/
def gapIntDiv : Fml Gaps [] := allI (.imp (isT (.app2 (.binop .ge rfl) xI (litI 0)))
  (isT (.app2 (.binop .le rfl) (.app2 (.binop .mul rfl) (.app2 (.binop .div rfl) xI (litI 3)) (litI 3)) xI)))
def gapIntMod : Fml Gaps [] := allI (isT (.app2 (.binop .lt rfl) (.app2 (.binop .mod rfl) xI (litI 3)) (litI 3)))
/-- `|`, `^` with a literal, `&` with one that is not a low mask. -/
def gapOr : Fml Gaps [] := allU (isT (.app2 (.binop .ge rfl) (.app2 (.binop .bor rfl) xU (litU 1)) xU))
def gapXor : Fml Gaps [] := allU (isT (.app2 (.binop .neB rfl) (.app2 (.binop .bxor rfl) xU (litU 1)) xU))
def gapAnd : Fml Gaps [] := allU (isT (.app2 (.binop .le rfl) (.app2 (.binop .band rfl) xU (litU 6)) (litU 6)))
/-- `**` by a literal (`x ** 1`), `*%` by a literal. -/
def gapPow : Fml Gaps [] := allU (.eq (.app2 (.binop .pow rfl) xU (litU 1)) xU)
def gapMulW : Fml Gaps [] := allU (isT (.app2 (.binop .ge rfl) (.app2 (.binop .mulW rfl) xU (litU 3)) (litU 0)))

end GapTerms

/-! ### Hashes outside `Fml.hashCovered` -/

section GapHashes

open Solidity.Examples.DecisionHashes
open Solidity.Examples.Tactics.Hashing (Names)

/-- Three kinds of hash of one string. -/
def gapThreeKinds : Fml Names [] :=
  strings (.imp (.eq hS hT) (.imp (.eq shaS shaT)
    (.eq (.app2 (.hash .ripemd160) (.app0 .memory) (.pvI (.there .here)))
      (.app2 (.hash .ripemd160) (.app0 .memory) (.pvI .here)))))
/-- Two kinds, no string hashed by both: no kind to read the other's words
against. -/
def gapMixedKinds : Fml Names2 [] :=
  strings2 (.imp (.eq (rd2 "ids" rfl kS) (n2 1)) (.eq (rd2 "shas" rfl sT) (n2 1)))
/-- A hash of written memory: `∀ s t. [ s[0] = 1; ] keccak256(s) ==
keccak256(t)`.  The verdict turns on the strings' bytes past the write,
which no stage reads (memory, plan step 6). -/
def gapWrittenMemory : Fml Names [] :=
  strings (.upd .box (.snoc .nil (.memory (.app3 .write (.app0 .memory)
    (.app2 (.mat .dyn) (.pvI (.there .here)) (num 0)) (.app1 .mval (num 1))))) (.eq hS hT))
/-- A hash under a negative value quantifier whose nodes the top premise
does not read: `∀ s t. (∀ x. keccak256(s) != keccak256(t)) → !(∀ y.
keccak256(s) == keccak256(t))`.  Valid as `holds` reads it, and false
under the premise exactly at two strings with different bytes and one
hash, where both inner premises fail: the only refutation is a
collision, which cannot be exhibited.  Not decidable without narrowing
`Fml.inTarget` (`docs/automation.md`, M7). -/
def gapHashNegForall : Fml Names [] :=
  let hs : Tm Names (.val .uint :: Γst) (.val .uint) := Tm.wk (.drop .refl) hS
  let ht : Tm Names (.val .uint :: Γst) (.val .uint) := Tm.wk (.drop .refl) hT
  strings (.imp (.all (.user "x") .uint (.not (.eq hs ht))) (.not (.all (.user "y") .uint (.eq hs ht))))

end GapHashes

theorem gapColumn_inTarget : gapColumn.inTarget {} = true := by decide +kernel
theorem gapTwoPaths_inTarget : gapTwoPaths.inTarget {} = true := by decide +kernel
theorem gapIntKeyed_inTarget : gapIntKeyed.inTarget {} = true := by decide +kernel
theorem gapBoolKeyed_inTarget : gapBoolKeyed.inTarget {} = true := by decide +kernel
theorem gapStructValue_inTarget : gapStructValue.inTarget {} = true := by decide +kernel
theorem gapArrayBlock_inTarget : gapArrayBlock.inTarget {} = true := by decide +kernel
theorem gapLedgerBlock_inTarget : gapLedgerBlock.inTarget {} = true := by decide +kernel
theorem gapPartialGuard_inTarget : gapPartialGuard.inTarget {} = true := by decide +kernel
theorem gapPositiveForall_inTarget : gapPositiveForall.inTarget {} = true := by decide +kernel
theorem gapMemory_inTarget : gapMemory.inTarget {} = true := by decide +kernel
theorem gapKIntBinder_inTarget : gapKIntBinder.inTarget {} = true := by decide +kernel
theorem gapLedgerWrite_inTarget : gapLedgerWrite.inTarget {} = true := by decide +kernel
theorem gapManyReads_inTarget : gapManyReads.inTarget {} = true := by decide +kernel
theorem gapIntDiv_inTarget : gapIntDiv.inTarget {} = true := by decide +kernel
theorem gapIntMod_inTarget : gapIntMod.inTarget {} = true := by decide +kernel
theorem gapOr_inTarget : gapOr.inTarget {} = true := by decide +kernel
theorem gapXor_inTarget : gapXor.inTarget {} = true := by decide +kernel
theorem gapAnd_inTarget : gapAnd.inTarget {} = true := by decide +kernel
theorem gapPow_inTarget : gapPow.inTarget {} = true := by decide +kernel
theorem gapMulW_inTarget : gapMulW.inTarget {} = true := by decide +kernel
theorem gapThreeKinds_inTarget : gapThreeKinds.inTarget {} = true := by decide +kernel
theorem gapMixedKinds_inTarget : gapMixedKinds.inTarget {} = true := by decide +kernel
theorem gapWrittenMemory_inTarget : gapWrittenMemory.inTarget {} = true := by decide +kernel
theorem gapHashNegForall_inTarget : gapHashNegForall.inTarget {} = true := by decide +kernel

/-- info: true -/
#guard_msgs in
#eval ([gapColumn, gapTwoPaths, gapIntKeyed, gapBoolKeyed, gapStructValue, gapArrayBlock, gapLedgerBlock,
  gapPartialGuard, gapPositiveForall, gapKIntBinder, gapLedgerWrite,
  gapManyReads, gapIntDiv, gapIntMod, gapOr, gapXor, gapAnd, gapPow, gapMulW].map verdict).all (· == "unknown")

/-- info: ["unknown", "unknown", "unknown", "unknown"] -/
#guard_msgs in
#eval [verdict gapThreeKinds, verdict gapMixedKinds, verdict gapWrittenMemory, verdict gapHashNegForall]

/-! ### Storage arrays at symbolic indices (M7, plan step 6)

A checked read `xs[i]` halts past the live length; the Theory reads a
formula's `xs[i]` at any slot, the default past every slot.  Update pushing
takes the Theory's reads exactly (`Tm.toLT`), and `arrayReduction?` cuts the
array reads to atoms with what actual arrays make of them
(`Calculus/ArrayCut.lean`), the slot tests a length check settles folded
(`LTm.hasFold`).  A refutation's arrays are rebuilt from the atoms, the
counterassignment first shrunk. -/


def Arrays : Contract := contract!{ uint[] xs; uint[4] row; mapping(uint => uint) owed; }

section

local instance : InContract := ⟨Arrays⟩

/-- An in-range read, its element read again in the postcondition (the
Theory's read), and a false variant. -/
def inRange : Fml Arrays [] := dl!{ ∀ uint i; i < xs.length → [ uint x = xs[i]; ] x == xs[i] }
def inRangeBad : Fml Arrays [] := dl!{ ∀ uint i; i < xs.length → [ uint x = xs[i]; ] x == 0 }
/-- Under the diamond the read must return: past the length it halts. -/
def pastEnd : Fml Arrays [] := dl!{ ∀ uint i; ⟨ uint x = xs[i]; ⟩ true }
def inRangeReturns : Fml Arrays [] := dl!{ ∀ uint i; i < xs.length → ⟨ uint x = xs[i]; ⟩ true }
/-- A write then a read at equal symbolic indices, at different ones (the
read keeps the old word), and at any (refuted). -/
def writeSame : Fml Arrays [] :=
  dl!{ ∀ uint i; ∀ uint j; i == j → [ xs[i] = 5; uint x = xs[j]; ] x == 5 }
def writeKeep : Fml Arrays [] :=
  dl!{ ∀ uint i; ∀ uint j; i != j → j < xs.length → xs[j] == 7 → [ xs[i] = 5; ] xs[j] == 7 }
def writeOther : Fml Arrays [] :=
  dl!{ ∀ uint i; ∀ uint j; [ xs[i] = 5; uint x = xs[j]; ] x == 5 }
def writeRead : Fml Arrays [] := dl!{ ∀ uint i; [ xs[i] = 5; ] xs[i] == 5 }
/-- A fixed array: a write below its length read back, and one past it. -/
def rowWrite : Fml Arrays [] := dl!{ ∀ uint i; i < 4 → [ row[i] = 5; ] row[i] == 5 }
def rowPast : Fml Arrays [] := dl!{ ∀ uint i; ⟨ row[i] = 5; ⟩ true }
/-- Past the live length the Theory reads the slots there, not the default;
past a fixed array's length, the default. -/
def shadowRead : Fml Arrays [] := dl!{ ∀ uint i; i >= xs.length → xs[i] == 0 }
def rowPastRead : Fml Arrays [] := dl!{ ∀ uint i; i >= 4 → row[i] == 0 }
/-- An array read stored in a mapping. -/
def owedRead : Fml Arrays [] :=
  dl!{ ∀ uint i; i < xs.length → [ owed[i] = xs[i]; ] owed[i] == xs[i] }

end

/-- info: "proved" -/
#guard_msgs in #eval verdict inRange
/-- info: "refuted" -/
#guard_msgs in #eval verdict inRangeBad
/-- info: "refuted" -/
#guard_msgs in #eval verdict pastEnd
/-- info: "proved" -/
#guard_msgs in #eval verdict inRangeReturns
/-- info: "proved" -/
#guard_msgs in #eval verdict writeSame
/-- info: "proved" -/
#guard_msgs in #eval verdict writeKeep
/-- info: "refuted" -/
#guard_msgs in #eval verdict writeOther
/-- info: "proved" -/
#guard_msgs in #eval verdict writeRead
/-- info: "proved" -/
#guard_msgs in #eval verdict rowWrite
/-- info: "refuted" -/
#guard_msgs in #eval verdict rowPast
/-- info: "refuted" -/
#guard_msgs in #eval verdict shadowRead
/-- info: "proved" -/
#guard_msgs in #eval verdict rowPastRead
/-- info: "proved" -/
#guard_msgs in #eval verdict owedRead

/-- Kernel-checked coverage: the read past the length, the write then read
at equal indices, and the Theory's read. -/
theorem pastEnd_covered : pastEnd.Covered = true := by decide +kernel
theorem writeSame_covered : writeSame.Covered = true := by decide +kernel
theorem inRange_covered : inRange.Covered = true := by decide +kernel

/-- `decideLeaf_complete`, applied to a read past the length. -/
theorem pastEnd_answers : decideLeaf pastEnd ≠ .unknown := decideLeaf_complete pastEnd_covered

/-- `decideLeaf_proved_iff`, applied: the verdict on an in-range read is exact. -/
theorem inRange_iff : decideLeaf inRange = .proved ↔ Fml.Valid inRange :=
  decideLeaf_proved_iff inRange_covered

/-- `decideGoal_complete`, applied: no hash, so no premise. -/
theorem writeSame_answers : decideGoal writeSame ≠ .unknown :=
  decideGoal_complete writeSame_covered rfl

/-! Two leaves of the named fragment once pinned as counterexamples to
`DecisionTheorem` (`Gaps`): plain storage-array reads, now decided. -/

theorem arrayRead_inTarget : arrayRead.inTarget {} = true := by decide +kernel
theorem fixedRead_inTarget : fixedRead.inTarget {} = true := by decide +kernel
theorem arrayRead_covered : arrayRead.Covered = true := by decide +kernel
theorem fixedRead_covered : fixedRead.Covered = true := by decide +kernel

/-- info: ["proved", "proved"] -/
#guard_msgs in #eval [arrayRead, fixedRead].map verdict

end Solidity.Examples.Decision
