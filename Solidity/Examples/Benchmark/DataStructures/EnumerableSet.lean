import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: enumerable set (swap-and-pop)

Source (OpenZeppelin 4.9.6):
<https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/dc44c9f1a4c3b10af99492eed84f83ed244203f6/contracts/utils/structs/EnumerableSet.sol>.
The private `Set` core (`_add`, `_remove`, `_contains`) with its fields as
state variables, at `uint256` element type (the library's `UintSet` view;
`bytes32` stays out because `@custom:key` quantifiers range over
`uint`/`int`/`bool`/`address` only); `_contains` inlined in `_add`.
`_length`, `_at`, `_values` getters and the typed wrappers are omitted.

Natural specification: the representation invariant (`_indexes` is the
1-based inverse of `_values`) is required and re-established; `add`
reports a fresh element and makes it a member, growing the array exactly
then; `remove` reports a member and makes it a non-member, shrinking the array exactly
then; `contains` reads
membership.

Verdicts: `contains` proved.  `add`, `remove`: unknown (`remove`'s
non-membership proved; even `add`'s membership, `contains(v)` after `add(v)`,
stops on reading `_indexes[v] = _values.length` back through the push).
The obligations stop with the quantified invariant uninstantiated and on array element frames
(`find(save(s, _values[k], v), _values[j])`, symbolic `j`, `k`): no closer
instantiates the `\forall` premises at the read indices, and none has an
array-element distinctness law (see `Stack`).
-/
namespace Solidity.Examples.Benchmark.DataStructures.EnumerableSet

def EnumerableSet : Contract := contract!{
  uint256[] _values;
  mapping(uint256 => uint256) _indexes;
  requires \forall uint256 j; j < _values.length -> _indexes[_values[j]] == j + 1;
  requires \forall uint256 v; _indexes[v] != 0 -> _indexes[v] <= _values.length && _values[_indexes[v] - 1] == v;
  ensures \result == (\old(_indexes[value]) == 0);
  ensures _indexes[value] != 0 && _values[_indexes[value] - 1] == value;
  ensures \old(_indexes[value]) == 0 -> _values.length == \old(_values.length) + 1;
  ensures \old(_indexes[value]) != 0 -> _values.length == \old(_values.length);
  ensures \forall uint256 j; j < _values.length -> _indexes[_values[j]] == j + 1;
  ensures \forall uint256 v; _indexes[v] != 0 -> _indexes[v] <= _values.length && _values[_indexes[v] - 1] == v;
  function add(uint256 value) public returns (bool) {
    if (!(_indexes[value] != 0)) {
      _values.push(value);
      _indexes[value] = _values.length;
      return true;
    } else {
      return false;
    }
  }
  requires \forall uint256 j; j < _values.length -> _indexes[_values[j]] == j + 1;
  requires \forall uint256 v; _indexes[v] != 0 -> _indexes[v] <= _values.length && _values[_indexes[v] - 1] == v;
  ensures \result == (\old(_indexes[value]) != 0);
  ensures _indexes[value] == 0;
  ensures \old(_indexes[value]) != 0 -> _values.length == \old(_values.length) - 1;
  ensures \old(_indexes[value]) == 0 -> _values.length == \old(_values.length);
  ensures \forall uint256 j; j < _values.length -> _indexes[_values[j]] == j + 1;
  ensures \forall uint256 v; _indexes[v] != 0 -> _indexes[v] <= _values.length && _values[_indexes[v] - 1] == v;
  function remove(uint256 value) public returns (bool) {
    uint256 valueIndex = _indexes[value];
    if (valueIndex != 0) {
      uint256 toDeleteIndex = valueIndex - 1;
      uint256 lastIndex = _values.length - 1;
      if (lastIndex != toDeleteIndex) {
        uint256 lastValue = _values[lastIndex];
        _values[toDeleteIndex] = lastValue;
        _indexes[lastValue] = valueIndex;
      }
      _values.pop();
      delete _indexes[value];
      return true;
    } else {
      return false;
    }
  }
  ensures \result == (_indexes[value] != 0);
  function contains(uint256 value) public view returns (bool) {
    return _indexes[value] != 0;
  }
}
local instance : InContract := ⟨EnumerableSet⟩
open scoped Scoped
/-- Unknown: invariant instantiation, array frame (module docstring). -/
def addTarget := spec!{ add }
/-- Unknown: invariant instantiation, array frame (module docstring). -/
def removeTarget := spec!{ remove }

/-- Component of `remove`: the element is no longer a member. -/
theorem remove_not_contains : ⊢ dl!{ [ bool r = remove(v); bool c = contains(v); ] c == false } := by
  sol_prove
/-- `contains`: reads membership. -/
theorem spec_contains : ⊢ spec!{ contains } := by
  sol_prove
end Solidity.Examples.Benchmark.DataStructures.EnumerableSet
