import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: two-index queue

Source (OpenZeppelin 4.9.6):
<https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/dc44c9f1a4c3b10af99492eed84f83ed244203f6/contracts/utils/structs/DoubleEndedQueue.sol>.
The `Bytes32Deque` struct's fields become state variables and the queue end
of the library (`pushBack`, `popFront`, `front`) becomes public functions,
`empty(deque)` inlined as `_end <= _begin`.  Bodies are otherwise as published.
`pushFront`, `popBack`, `back`, `at`, `clear`, `length` are omitted.

Natural specification: `pushBack` stores at the old back index and advances
`_end`; `popFront` returns and clears the front slot and advances `_begin`;
`front` returns the front slot; other slots are kept.  `pushBack` requires
`_end < type(int128).max`: the library's documented assumption (the
`unchecked` increment wraps there, where the natural clause is false).

Verdicts: `front` proved.  `pushBack`, `popFront`: unknown (slot
components proved).  Each obligation stops on the `unchecked` int128
increment, symbolically `toInt((toUint(e) +% 1 +% 2^127) % 2^128 -% 2^127)`
against `e + 1`: no closer normalizes the int128 wrap under the range
premise `e < 2^127 - 1`.
-/
namespace Solidity.Examples.Benchmark.DataStructures.Queue

def Queue : Contract := contract!{
  int128 _begin;
  int128 _end;
  mapping(int128 => bytes32) _data;
  error Empty();
  requires _end < 170141183460469231731687303715884105727;
  ensures _data[\old(_end)] == value && _end == \old(_end) + 1 && _begin == \old(_begin);
  ensures \forall int k; k != \old(_end) -> _data[k] == \old(_data[k]);
  function pushBack(bytes32 value) public {
    int128 backIndex = _end;
    _data[backIndex] = value;
    unchecked {
      _end = backIndex + 1;
    }
  }
  ensures \result == \old(_data[_begin]) && _begin == \old(_begin) + 1 && _end == \old(_end);
  ensures _data[\old(_begin)] == 0;
  ensures \forall int k; k != \old(_begin) -> _data[k] == \old(_data[k]);
  function popFront() public returns (bytes32 value) {
    if (_end <= _begin) {
      revert Empty();
    }
    int128 frontIndex = _begin;
    value = _data[frontIndex];
    delete _data[frontIndex];
    unchecked {
      _begin = frontIndex + 1;
    }
  }
  ensures \result == _data[_begin];
  function front() public view returns (bytes32 value) {
    if (_end <= _begin) {
      revert Empty();
    }
    int128 frontIndex = _begin;
    return _data[frontIndex];
  }
}
local instance : InContract := ⟨Queue⟩
open scoped Scoped
/-- Unknown: int128 wrap of the `unchecked` increment (module docstring). -/
def pushBackTarget := spec!{ pushBack }
/-- Unknown: int128 wrap of the `unchecked` increment (module docstring). -/
def popFrontTarget := spec!{ popFront }

/-- Component of `pushBack`: the value lands at the old back index. -/
theorem pushBack_slot : ⊢ dl!{ [ int128 e = _end; pushBack(v); ] _data[e] == v } := by
  sol_prove
/-- Component of `popFront`: the old front is returned and its slot cleared. -/
theorem popFront_slot : ⊢ dl!{
    [ int128 b = _begin; bytes32 x = _data[b]; bytes32 r = popFront(); ] (r == x ∧ _data[b] == 0) } := by
  sol_prove
/-- `front()`: returns the front slot. -/
theorem spec_front : ⊢ spec!{ front } := by
  sol_prove
end Solidity.Examples.Benchmark.DataStructures.Queue
