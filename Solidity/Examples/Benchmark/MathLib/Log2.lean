import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: floor of the binary logarithm

Source: OpenZeppelin Contracts v4.9.6, `Math.log2`,
<https://github.com/OpenZeppelin/openzeppelin-contracts/blob/dc44c9f1a4c3b10af99492eed84f83ed244203f6/contracts/utils/math/Math.sol#L195-L238>.

Changes: `public` instead of `internal` and the `@custom:key` clauses. The
body is the source's, its parameter `value` shifted in place.

Natural specification: `log2(0) = 0` and, for `value > 0`,
`2^result <= value < 2^(result + 1)` (`NaturalSpec`). The clause language
has neither `**` nor `>>`, so only its consequences `value == 0 -> result
== 0` and `result < 256` are written as clauses; they are not the
specification.
-/
namespace Solidity.Examples.Benchmark.MathLib.Log2

/-- The natural specification, over the naturals. -/
def NaturalSpec (value result : Nat) : Prop :=
  (value = 0 → result = 0) ∧ (0 < value → 2 ^ result ≤ value ∧ value < 2 ^ (result + 1))

def Log2 : Contract := contract!{
  ensures value == 0 -> \result == 0;
  ensures \result < 256;
  function log2(uint256 value) public pure returns (uint256) {
    uint256 result = 0;
    unchecked {
      if (value >> 128 > 0) { value >>= 128; result += 128; }
      if (value >> 64 > 0) { value >>= 64; result += 64; }
      if (value >> 32 > 0) { value >>= 32; result += 32; }
      if (value >> 16 > 0) { value >>= 16; result += 16; }
      if (value >> 8 > 0) { value >>= 8; result += 8; }
      if (value >> 4 > 0) { value >>= 4; result += 4; }
      if (value >> 2 > 0) { value >>= 2; result += 2; }
      if (value >> 1 > 0) { result += 1; }
    }
    return result;
  }
}
local instance : InContract := ⟨Log2⟩
open scoped Scoped

/-- Unknown, even for the two written consequences: the leaf carries eight
joined conditional updates of `result` and `value`;
`sol_close_ite_split` splits at most six (`CloseSplit.splitMax`) and
`sol_close_join_steps` finds no summary. Missing: `**`/`>>` in `SpecExpr`
for `NaturalSpec`, and a closer for long chains of joined shifts. -/
def log2Target := spec!{ log2 }

end Solidity.Examples.Benchmark.MathLib.Log2
