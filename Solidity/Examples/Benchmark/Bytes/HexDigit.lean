import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: hex digit encoding

Source: <https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/v5.3.0/contracts/utils/Strings.sol>, lines 16 and 90 (OpenZeppelin 5.3.0
`Strings`: `HEX_DIGITS` and the digit lookup `HEX_DIGITS[localValue & 0xf]`
of `toHexString`).
Adaptation: the lookup alone, as a function of `value`; the constant is a
local of the same value.  (`toHexString` returns a `string memory`, which
an obligation cannot name: `refReturnMsg`, `Calculus/SurfaceSpec.lean`.)

Natural specification: the low nibble `d` of `value` maps to ASCII
`'0' + d` below ten and `'a' + d - 10` from ten.

Status of `hexDigit`: **unknown**.  `sol_prove` leaves the leaf
`se5 := value & 15`, `se9 := se4 >> 8 * (15 - se5)`, `se8 := se9 % 256`
`⊢ result = 48 + value % 16`.  Missing closer facts: `x & (2^k - 1) = x % 2^k`
and the byte of a literal `bytes16` at a symbolic index below 16 (a case
split over the sixteen indices).  Two lookups are proved concretely.
-/

namespace Solidity.Examples.Benchmark.Bytes.HexDigit

def HexDigit : Contract := contract!{
  ensures value % 16 < 10 -> \result == 48 + value % 16;
  ensures value % 16 >= 10 -> \result == 87 + value % 16;
  function hexDigit(uint256 value) public pure returns (bytes1) {
    bytes16 HEX_DIGITS = "0123456789abcdef";
    return HEX_DIGITS[value & 0xf];
  }
}

local instance : InContract := ⟨HexDigit⟩
open scoped Scoped

/-- Unknown: the two clauses of `hexDigit` (see the module docstring). -/
def hexDigitTarget := spec!{ hexDigit }

/-- `hexDigit(0x3c)` is `'c'`, the low nibble 12. -/
theorem hexDigit_c : ⊢ dl!{ [ bytes1 r = hexDigit(60); ] r == 99 } := by
  sol_prove

/-- `hexDigit(0x29)` is `'9'`. -/
theorem hexDigit_9 : ⊢ dl!{ [ bytes1 r = hexDigit(41); ] r == 57 } := by
  sol_prove

end Solidity.Examples.Benchmark.Bytes.HexDigit
