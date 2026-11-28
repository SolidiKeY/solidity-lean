import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers


/-!
# Benchmark: bitmap set

Source (OpenZeppelin 4.9.6):
<https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/dc44c9f1a4c3b10af99492eed84f83ed244203f6/contracts/utils/structs/BitMaps.sol>.
The `BitMap` struct's `_data` becomes a state variable and `get`, `set`,
`unset` public functions with the published bodies; `setTo` is omitted.

Natural specification: after `set(i)`, `get(i)` is true; after `unset(i)`, it
is false; other buckets are kept.  The `@custom:key` grammar has no
bitwise operators, so the membership clauses are stated as boxes over
`get` (`set_get`, `unset_get`) and the clauses keep the frame, the bucket
written as `index / 256`.

Verdicts: `get` has no clauses of its own; membership (`get` after `set`,
`unset`) and the `set`, `unset` clauses: unknown.  Membership stops on raw
`band`/`bor`/`bnot`/`<<` terms (`(x | 1 << (i & 255)) & 1 << (i & 255) != 0`):
no closer has bitwise laws.  The frame clauses stop on
`b != index / 256` against the written bucket `index >> 8`: no law equates
`>> 8` with `/ 256`.  The frame against `i >> 8` itself is proved
(`set_frame`, `unset_frame`).
-/
namespace Solidity.Examples.Benchmark.DataStructures.BitMap

def BitMap : Contract := contract!{
  mapping(uint256 => uint256) _data;
  function get(uint256 index) public view returns (bool) {
    uint256 bucket = index >> 8;
    uint256 mask = 1 << (index & 0xff);
    return _data[bucket] & mask != 0;
  }
  ensures \forall uint256 b; b != index / 256 -> _data[b] == \old(_data[b]);
  function set(uint256 index) public {
    uint256 bucket = index >> 8;
    uint256 mask = 1 << (index & 0xff);
    _data[bucket] |= mask;
  }
  ensures \forall uint256 b; b != index / 256 -> _data[b] == \old(_data[b]);
  function unset(uint256 index) public {
    uint256 bucket = index >> 8;
    uint256 mask = 1 << (index & 0xff);
    _data[bucket] &= ~mask;
  }
}
local instance : InContract := ⟨BitMap⟩
open scoped Scoped

/-- Unknown: bitwise laws (module docstring). -/
def setGetTarget := dl!{ [ set(i); bool r = get(i); ] r == true }
/-- Unknown: bitwise laws (module docstring). -/
def unsetGetTarget := dl!{ [ unset(i); bool r = get(i); ] r == false }
/-- `set(i)` keeps every other bucket. -/
theorem set_frame : ⊢ dl!{ v == _data[b] → [ uint k = i >> 8; set(i); ] (k != b → _data[b] == v) } := by
  sol_prove
/-- `unset(i)` keeps every other bucket. -/
theorem unset_frame : ⊢ dl!{ v == _data[b] → [ uint k = i >> 8; unset(i); ] (k != b → _data[b] == v) } := by
  sol_prove
/-- Unknown: `>> 8` against `/ 256` (module docstring). -/
def setTarget := spec!{ set }
/-- Unknown: `>> 8` against `/ 256` (module docstring). -/
def unsetTarget := spec!{ unset }

end Solidity.Examples.Benchmark.DataStructures.BitMap
