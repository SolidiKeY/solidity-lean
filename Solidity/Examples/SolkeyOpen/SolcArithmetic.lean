import Solidity.Calculus.Closers
import Solidity.Tools.Counterexample

/-!
# solkey open problems: `SolcArithmetic`

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/semantics/open/SolcArithmetic.sol>.
Changes: the unused modifier `addUnchecked` dropped.  A function solkey tags `@custom:key box` or specifies has the obligation `spec!{f}`; an untagged
one solkey's diamond, `msg.value == 0 → wt(storage) → ⟨ f(); ⟩ true`.
solkey's integers are unbounded; the model's wrap, so the `unchecked` ports close
(`Examples/Tactics/SolcOpen.lean`, `Examples/Tactics/SignedCasts.lean` prove such programs inline).
-/

namespace Solidity.Examples.SolkeyOpen.SolcArithmetic

def SolcArithmetic : Contract := contract!{
  uint[] array;
  mapping(uint => uint) map;
  function addUnchecked16(uint16 a, uint16 b) internal pure returns (uint16) { unchecked { return a + b; } }
  function add16(uint16 a, uint16 b) internal pure returns (uint16) { return a + b; }
  function uncheckedCalledByCheckedWraps(uint16 a) public pure {
    require(a == 0xffff);
    uint16 r = addUnchecked16(a, 0x100) + 0x100;
    assert(r == 511);
  }
  function checkedCalledByUncheckedWraps(uint16 a, uint16 b, uint16 c) public pure {
    require(a == 0xe000 && b == 0x1000 && c == 0x1000);
    uint16 r;
    unchecked { r = add16(a, b) + c; }
    assert(r == 0);
  }
  function blockInsideUnchecked() public pure {
    uint y;
    unchecked {{ uint max = 2**256 - 1; uint x = max + 1; y = x; }}
    assert(y == 0);
  }
  function uncheckedIncrementWraps() public pure { uint x = 2**256 - 1; unchecked { ++x; } assert(x == 0); }
  function uncheckedUint8SubWraps() public pure {
    uint8 x = 0;
    uint8 y;
    unchecked { y = x - 1; }
    assert(y == 255);
    unchecked { y = x - 255; }
    assert(y == 1);
  }
  function uncheckedInt8SumWraps() public pure {
    int8 x = 127;
    int8 y;
    unchecked { y = x + 1; }
    int8 e1 = -128;
    assert(y == e1);
    unchecked { y = x + 127; }
    int8 e2 = -2;
    assert(y == e2);
    x = -127;
    unchecked { y = x + -127; }
    assert(y == 2);
  }
  function uncheckedInt8MulWraps() public pure {
    int8 x = 100;
    int8 y;
    unchecked { y = x * 2; }
    int8 e = -56;
    assert(y == e);
  }
}

local instance : InContract := ⟨SolcArithmetic⟩
open scoped Scoped

/-- `uint16` `0xffff + 0x100` wraps to `0xff`; `0xff + 0x100 == 511`.  Proved. -/
theorem spec_uncheckedCalledByCheckedWraps : ⊢ spec!{ uncheckedCalledByCheckedWraps } := by sol_prove
/-- Unknown: `sol_prove` leaves `se1 == 57344, se2 == 4096, se3 == 4096, se9 := se1 + se2,
se14 := se9 +% se3, se4 := se14 % 65536 ⟹ se4 == 0`; `sol_leaf; sol_close` times out and `sol_refute`
finds nothing.  Missing closer: `+%` and `% 2^16` under equations of the parameters
(`Examples/Tactics/SolcOpen.lean` proves the run from literals). -/
def checkedCalledByUncheckedWraps_obligation : Fml SolcArithmetic [] := spec!{ checkedCalledByUncheckedWraps }
/-- `2**256 - 1 + 1` wraps to `0` inside `unchecked`.  Proved. -/
theorem total_blockInsideUnchecked : ⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ blockInsideUnchecked(); ⟩ true } := by sol_prove
/-- Refuted in the model: outside `unchecked` the model's `2**256` is a checked `uint` power and
reverts, where solc folds the literal expression `2**256 - 1` (a deviation of the front end). -/
example : ¬ (⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ uncheckedIncrementWraps(); ⟩ true }) := by sol_refute
/-- `uint8` `0 - 1` wraps to `255`.  Proved. -/
theorem total_uncheckedUint8SubWraps : ⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ uncheckedUint8SubWraps(); ⟩ true } := by sol_prove
/-- `int8` `127 + 1` wraps to `-128`.  Proved. -/
theorem total_uncheckedInt8SumWraps : ⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ uncheckedInt8SumWraps(); ⟩ true } := by sol_prove
/-- `int8` `100 * 2` wraps to `-56`.  Proved. -/
theorem total_uncheckedInt8MulWraps : ⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ uncheckedInt8MulWraps(); ⟩ true } := by sol_prove

end Solidity.Examples.SolkeyOpen.SolcArithmetic
