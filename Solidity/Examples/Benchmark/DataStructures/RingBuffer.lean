import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: fixed-size ring buffer

Source (OpenZeppelin 5.1.0):
<https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/69c8def5f222ff96f2b5beff05dfba996368aa79/contracts/utils/structs/CircularBuffer.sol>.
The `Bytes32CircularBuffer` fields become state variables, with `_data` a
fixed `bytes32[4]` in place of `setup`'s `Arrays.unsafeSetLength` (so the
buffer has its fixed size from the start); `Arrays.unsafeAccess` becomes
indexing (in range: the index is reduced modulo the length), `Math.min` an
`if`, and `Panic.panic(ARRAY_OUT_OF_BOUNDS)` `revert()`.  `push`, `count`,
`last` are kept; `setup`, `clear`, `length`, `includes` are omitted.

Natural specification: `push` advances the counter and writes slot
`old count % 4`, keeping the other slots; `count` is `min(_count, 4)`; `last(i)` is slot
`(_count - i - 1) % 4` for `i < min(_count, 4)`.

Verdicts: `push`, `count`, `last`: proved.
-/
namespace Solidity.Examples.Benchmark.DataStructures.RingBuffer

def RingBuffer : Contract := contract!{
  uint256 _count;
  bytes32[4] _data;
  ensures _count == \old(_count) + 1;
  ensures _data[\old(_count) % 4] == value;
  ensures \forall uint256 j; j < 4 && j != \old(_count) % 4 -> _data[j] == \old(_data[j]);
  function push(bytes32 value) public {
    uint256 index = _count++;
    uint256 modulus = _data.length;
    _data[index % modulus] = value;
  }
  ensures _count < 4 -> \result == _count;
  ensures _count >= 4 -> \result == 4;
  function count() public view returns (uint256) {
    if (_count < _data.length) {
      return _count;
    }
    return _data.length;
  }
  requires i < _count && i < 4;
  ensures \result == _data[(_count - i - 1) % 4];
  function last(uint256 i) public view returns (bytes32) {
    uint256 index = _count;
    uint256 modulus = _data.length;
    uint256 total = modulus;
    if (index < modulus) {
      total = index;
    }
    if (i >= total) {
      revert();
    }
    return _data[(index - i - 1) % modulus];
  }
}
local instance : InContract := ⟨RingBuffer⟩
open scoped Scoped
/-- `push`: counter and slot. -/
theorem spec_push : ⊢ spec!{ push } := by
  sol_prove
/-- `count`: `min(_count, 4)`. -/
theorem spec_count : ⊢ spec!{ count } := by
  sol_prove
/-- `last(i)`: the `i`-th most recent slot. -/
theorem spec_last : ⊢ spec!{ last } := by
  sol_prove
end Solidity.Examples.Benchmark.DataStructures.RingBuffer
