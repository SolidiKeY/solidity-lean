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
`<<` and a low mask `& (2^k - 1)` by a literal, `+%`, `-%`; and, written
through those, `&`, `|`, `^`, `*%` with any literal, `**` by `0` or `1`,
`/` and `%` at `int`.  Each has a
proved and a refuted verdict pinned and a kernel-checked covered leaf.  The
verdicts are the compiled ones, except `sortedLe`, whose exact verdict is
kernel-certified and replayed below: the kernel's arithmetic decision over
256-bit codes is too deep for the language server (as in
`Examples/AutoComplete.lean`); the theorems' fragment checks are the
kernel's, the `#eval` pins the compiled ones.

Presburger quantifiers past the prefix (M7, step 4) are decided by the
quantified pipeline (`quantReduction?`, `QFml.decide_iff`): an `∃` or a
`∀` in a hypothesis, an alternation `∀∃`, beside a storage write, and one
whose body reads storage at no variable it binds (`evenRead`: the read
hoisted out, `hoistPrep`; since feature 17 the `∃` of a hypothesis is
dropped to a fresh atom first, and `evenGoal`'s, in a consequent, is
hoisted).

`Fml.inTarget` is the fragment the user named, on program-free leaves: a
negative-position quantifier over a mapping is in it only when it is in
the array property fragment (a conservative reading).  `decideLeaf` decides such a block over a
mapping at a root (M7, step 5: `apf`, instantiated at the index set,
`apfPrep`), a block over an inner mapping (`rowApf`), and since features
16 to 19 a bound index not the last of its path (`gapColumn`), at two
depths (`gapTwoPaths`), past a member (`gapStructValue`), a `bool` block
(`gapBoolKeyed`), a guard that may halt (`gapPartialGuard`) and a
positive `∀` past the prefix (`gapPositiveForall`).  Two bound indices on one
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
/-- Since feature 17 the `∃` in those hypotheses is a positive `∀`, dropped
to a fresh atom; a read under a negative quantifier is still hoisted: an
`∃` in a consequent. -/
def evenGoal : Fml Bank [] := dl!{ ∀ uint k; balances[k] == 4 → (∃ uint y; balances[k] == y + y) }
def evenGoalBad : Fml Bank [] := dl!{ ∀ uint k; balances[k] == 5 → (∃ uint y; balances[k] == y + y) }

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
`FloorShape`): decided, and false variants (another row, a key past the guard);
the row a parameter. -/
def rowApf : Fml Allow [] := dl!{ (∀ uint k; k < 10 → allow[3][k] == 0) → allow[3][5] == 0 }
def rowBad : Fml Allow [] := dl!{ (∀ uint k; k < 10 → allow[3][k] == 0) → allow[4][5] == 0 }
def rowOut : Fml Allow [] := dl!{ (∀ uint k; k < 10 → allow[3][k] == 0) → allow[3][12] == 0 }
def rowVar : Fml Allow [] := dl!{ ∀ uint x; (∀ uint k; k < 10 → allow[x][k] == 0) → allow[x][5] == 0 }
/-- A key the solver places past `2^200`: refuted by a rebuilt mapping
listed region by region, the keys past the guard's bound up to the far
key reading the far key's word, the default (`lastIn`, `regionList`), not
`2^200` entries. -/
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

end Solidity.Examples.Decision
