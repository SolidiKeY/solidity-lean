import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `bytes32` / `uint256` casts round trip

Source: <https://raw.githubusercontent.com/ethereum/solidity/v0.8.28/docs/types/conversion.rst>, lines 100–108 (Solidity 0.8.28
documentation: integers and fixed-size byte arrays of the same size convert
explicitly, `uint32(bytes4(a))`).
Adaptation: the conversions at 32 bytes, each way and both round trips.

Natural specification: a `bytes32` holds its bytes big-endian, so each
conversion keeps the number and each round trip is the identity.
Status: `toBytes32`, `toUint256`, `uintRoundTrip`, `bytesRoundTrip`
all **proved**.
-/

namespace Solidity.Examples.Benchmark.Bytes.Bytes32Cast

def Bytes32Cast : Contract := contract!{
  ensures \result == x;
  function toBytes32(uint256 x) public pure returns (bytes32) {
    return bytes32(x);
  }
  ensures \result == b;
  function toUint256(bytes32 b) public pure returns (uint256) {
    return uint256(b);
  }
  ensures \result == x;
  function uintRoundTrip(uint256 x) public pure returns (uint256) {
    return uint256(bytes32(x));
  }
  ensures \result == b;
  function bytesRoundTrip(bytes32 b) public pure returns (bytes32) {
    return bytes32(uint256(b));
  }
}

local instance : InContract := ⟨Bytes32Cast⟩
open scoped Scoped

/-- `bytes32(x)` keeps the number. -/
theorem spec_toBytes32 : ⊢ spec!{ toBytes32 } := by
  sol_prove
/-- `uint256(b)` keeps the number. -/
theorem spec_toUint256 : ⊢ spec!{ toUint256 } := by
  sol_prove
/-- `uint256(bytes32(x)) == x`. -/
theorem spec_uintRoundTrip : ⊢ spec!{ uintRoundTrip } := by
  sol_prove
/-- `bytes32(uint256(b)) == b`. -/
theorem spec_bytesRoundTrip : ⊢ spec!{ bytesRoundTrip } := by
  sol_prove

end Solidity.Examples.Benchmark.Bytes.Bytes32Cast
