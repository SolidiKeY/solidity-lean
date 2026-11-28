import Solidity.Calculus.Closers
import Solidity.Tools.Counterexample

/-!
# solkey open problems: `SolcTypes`

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/semantics/open/SolcTypes.sol>.
Changes: none (comments dropped).  A function solkey tags `@custom:key box` or specifies has the obligation `spec!{f}`; an untagged
one solkey's diamond, `msg.value == 0 → wt(storage) → ⟨ f(); ⟩ true`.
solkey's casts are the identity and it has no rule for `E(x)`; the model's casts wrap and `E(x)`
asserts membership, so all but two close.
-/

namespace Solidity.Examples.SolkeyOpen.SolcTypes

def SolcTypes : Contract := contract!{
  enum Truth { False, True }
  enum ActionChoices { GoLeft, GoRight, GoStraight }
  enum D { Left, Right }
  ActionChoices choice;
  address a;
  uint c;
  function constructingEnumsFromInts() public pure { uint r = uint256(Truth(uint8(0x1))); assert(r == 1); }
  function enumExplicitConversionInRange() public {
    uint x = 2;
    choice = ActionChoices(x);
    uint r = uint256(choice);
    assert(r == 2);
  }
  function enumFromUint(uint x) public pure { require(x == 0); D p = D(x); assert(p == D.Left); }
  function storageValueVarsNonNegative() public view {
    require(a < 0x0000000000000000000000000000000000000100);
    assert(c >= 0);
  }
  function castSmallerBoundsRange(uint16 x) public pure { uint8 y = uint8(x); assert(y < 300); }
  function castSmallerTruncates() public pure {
    uint32 p = 0x12345678;
    uint16 q = uint16(p);
    assert(q == 0x5678);
  }
  function downcastTruncates() public pure {
    int8 y = int8(uint8(uint16(200)));
    uint8 v = uint8(int8(int16(300)));
    int8 e = -56;
    assert(y == e);
    assert(v == 44);
  }
  function sameSizeReinterprets() public pure {
    int8 p = int8(uint8(200));
    uint8 q = uint8(int8(-100));
    int8 e = -56;
    assert(p == e);
    assert(q == 156);
  }
  function upcastAfterTruncation() public pure { int z = int(int8(int(255))); int e = -1; assert(z == e); }
  function numberLiteralWraps() public pure {
    uint b = 115792089237316195423570985008687907853269984665640564039457584007913129639935;
    int d = -1;
    uint e = uint(d);
    assert(b == e);
  }
  function typeConversionCleanup() public pure {
    uint200 mx = 1606938044258990275541962092341162602522202993782792835301375;
    uint r = uint(uint160(address(uint160(uint128(mx)))));
    assert(r == 0xffffffffffffffffffffffffffffffff);
  }
  function packingSignedTypes() public pure { uint8 x = 0xfa; int8 y = int8(x); int8 e = -6; assert(y == e); }
  function nestedTuplesParenthesized() public pure {
    int x;
    bool b;
    ((x, b)) = (2, true);
    assert(x == 2);
    assert(b);
  }
  function ternaryLiteralOverflow() public pure {
    bool t = true;
    bool f = false;
    uint16 r = (t ? 63 : 255) + (f ? 63 : 255);
    assert(r == 318);
  }
}

local instance : InContract := ⟨SolcTypes⟩
open scoped Scoped

/-- `Truth(uint8(1))` is `Truth.True`.  Proved. -/
theorem total_constructingEnumsFromInts : ⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ constructingEnumsFromInts(); ⟩ true } := by sol_prove
/-- `ActionChoices(2)` is stored and read back.  Proved. -/
theorem total_enumExplicitConversionInRange : ⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ enumExplicitConversionInRange(); ⟩ true } := by sol_prove
/-- `D(0)` is `D.Left`.  Proved. -/
theorem spec_enumFromUint : ⊢ spec!{ enumFromUint } := by sol_prove
/-- A `uint` state variable is non-negative.  Proved. -/
theorem spec_storageValueVarsNonNegative : ⊢ spec!{ storageValueVarsNonNegative } := by sol_prove
/-- `uint8(x) < 300` for a `uint16` argument.  Proved. -/
theorem total_castSmallerBoundsRange : ⊢ dl!{ x <= 65535 → msg.value == 0 → wt(storage) →
    ⟨ castSmallerBoundsRange(uint16(x)); ⟩ true } := by sol_prove
/-- `uint16(0x12345678) == 0x5678`.  Proved. -/
theorem total_castSmallerTruncates : ⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ castSmallerTruncates(); ⟩ true } := by sol_prove
/-- Narrowing and sign-changing casts wrap.  Proved. -/
theorem total_downcastTruncates : ⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ downcastTruncates(); ⟩ true } := by sol_prove
/-- A same-width signed/unsigned cast reinterprets the bits.  Proved. -/
theorem total_sameSizeReinterprets : ⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ sameSizeReinterprets(); ⟩ true } := by sol_prove
/-- `int8(int(255))` is `-1`.  Proved. -/
theorem total_upcastAfterTruncation : ⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ upcastAfterTruncation(); ⟩ true } := by sol_prove
/-- `uint(int(-1))` is `2**256 - 1`.  Proved. -/
theorem total_numberLiteralWraps : ⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ numberLiteralWraps(); ⟩ true } := by sol_prove
/-- `uint128(x)` keeps the low 128 bits.  Proved. -/
theorem total_typeConversionCleanup : ⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ typeConversionCleanup(); ⟩ true } := by sol_prove
/-- `int8(uint8(0xfa))` is `-6`.  Proved. -/
theorem total_packingSignedTypes : ⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ packingSignedTypes(); ⟩ true } := by sol_prove
-- Unknown: the front end refuses `((x, b)) = (2, true)`, so there is no obligation.  Missing: a
-- parenthesized tuple as an assignment target (solkey: "has no rule").
/-- error: Solidity elaboration failed: a tuple is the right-hand side of a tuple assignment or of a `return` -/
#guard_msgs in #check dl!{ ⟨ nestedTuplesParenthesized(); ⟩ true }
/-- Refuted, as solkey notes ("closes in KeY, but panics with 0x11 on the EVM"): `t ? 63 : 255` is a
`uint8`, so `63 + 255` reverts (`Examples/Tactics/SolcOpen.lean`, `ternaryLiteralOverflow`). -/
example : ¬ (⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ ternaryLiteralOverflow(); ⟩ true }) := by sol_refute

end Solidity.Examples.SolkeyOpen.SolcTypes
