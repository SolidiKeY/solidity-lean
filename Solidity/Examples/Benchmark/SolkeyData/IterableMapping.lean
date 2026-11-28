import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `IterableMapping` (solkey real-world)

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/contracts/real-world/IterableMapping.sol>
(after Solidity by Example's `app/iterable-mapping/IterableMapping.sol`,
revision `5bcdca02`).

Changes: none but the spelling of `contract!{ … }` (solkey already merges the
library into `TestIterableMap`, inlining each library body with `map` for
the `Map` parameter and a local `key = msg.sender`, and names the results).
The three class invariants are `invariant` clauses, assumed and owed by
every `spec!{f}`.  Verdicts: all five obligations unknown (the quantified
invariants; see "The obligations"); every `ensures` clause proved by hand
without the invariants.

```solidity
/// @custom:key invariant \forall address a; map.values[a] >= 0 && (!map.inserted[a] -> map.values[a] == 0)
/// @custom:key invariant \forall address a; map.inserted[a] -> map.indexOf[a] >= 0 && map.indexOf[a] < map.keys.length && map.keys[map.indexOf[a]] == a
/// @custom:key invariant \forall uint i; 0 <= i && i < map.keys.length -> map.inserted[map.keys[i]] && map.indexOf[map.keys[i]] == i
contract IterableMapping {
    struct Map {
        address[] keys;
        mapping(address => uint256) values;
        mapping(address => uint256) indexOf;
        mapping(address => bool) inserted;
    }

    Map private map;

    /// @custom:key requires val >= 0
    /// @custom:key ensures map.values[msg.sender] == val && map.inserted[msg.sender]
    /// @custom:key ensures \old(map.inserted[msg.sender]) -> map.keys.length == \old(map.keys.length)
    /// @custom:key ensures !\old(map.inserted[msg.sender]) -> map.keys.length == \old(map.keys.length) + 1 && map.keys[\old(map.keys.length)] == msg.sender && map.indexOf[msg.sender] == \old(map.keys.length)
    function setInMapping(uint256 val) public {
        address key = msg.sender;
        if (map.inserted[key]) {
            map.values[key] = val;
        } else {
            map.inserted[key] = true;
            map.values[key] = val;
            map.indexOf[key] = map.keys.length;
            map.keys.push(key);
        }
    }

    /// @custom:key ensures v == map.values[msg.sender]
    function getFromMap() public view returns (uint256 v) {
        return map.values[msg.sender];
    }

    /// @custom:key ensures k == map.keys[index]
    function getKeyAtIndex(uint256 index) public view returns (address k) {
        return map.keys[index];
    }

    /// @custom:key ensures s == map.keys.length
    function sizeOfMapping() public view returns (uint256 s) {
        return map.keys.length;
    }

    /// @custom:key ensures !map.inserted[msg.sender] && map.values[msg.sender] == 0
    /// @custom:key ensures \old(map.inserted[msg.sender]) -> map.keys.length == \old(map.keys.length) - 1
    /// @custom:key ensures !\old(map.inserted[msg.sender]) -> map.keys.length == \old(map.keys.length)
    function removeFromMapping() public {
        address key = msg.sender;
        if (!map.inserted[key]) {
            return;
        }

        delete map.inserted[key];
        delete map.values[key];

        uint256 index = map.indexOf[key];
        address lastKey = map.keys[map.keys.length - 1];

        map.indexOf[lastKey] = index;
        delete map.indexOf[key];

        map.keys[index] = lastKey;
        map.keys.pop();
    }
}
```
-/

namespace Solidity.Examples.Benchmark.SolkeyData.IterableMapping

/-- `IterableMapping.sol`, as solkey publishes it, with its clauses. -/
def IterableMapping : Contract := contract!{
  invariant \forall address a; map.values[a] >= 0 && (!map.inserted[a] -> map.values[a] == 0);
  invariant \forall address a; map.inserted[a] -> map.indexOf[a] >= 0 && map.indexOf[a] < map.keys.length && map.keys[map.indexOf[a]] == a;
  invariant \forall uint i; 0 <= i && i < map.keys.length -> map.inserted[map.keys[i]] && map.indexOf[map.keys[i]] == i;
  struct Map {
    address[] keys;
    mapping(address => uint256) values;
    mapping(address => uint256) indexOf;
    mapping(address => bool) inserted;
  }
  Map private map;
  requires val >= 0;
  ensures map.values[msg.sender] == val && map.inserted[msg.sender];
  ensures \old(map.inserted[msg.sender]) -> map.keys.length == \old(map.keys.length);
  ensures !\old(map.inserted[msg.sender]) -> map.keys.length == \old(map.keys.length) + 1 && map.keys[\old(map.keys.length)] == msg.sender && map.indexOf[msg.sender] == \old(map.keys.length);
  function setInMapping(uint256 val) public {
    address key = msg.sender;
    if (map.inserted[key]) {
      map.values[key] = val;
    } else {
      map.inserted[key] = true;
      map.values[key] = val;
      map.indexOf[key] = map.keys.length;
      map.keys.push(key);
    }
  }
  ensures v == map.values[msg.sender];
  function getFromMap() public view returns (uint256 v) {
    return map.values[msg.sender];
  }
  ensures k == map.keys[index];
  function getKeyAtIndex(uint256 index) public view returns (address k) {
    return map.keys[index];
  }
  ensures s == map.keys.length;
  function sizeOfMapping() public view returns (uint256 s) {
    return map.keys.length;
  }
  ensures !map.inserted[msg.sender] && map.values[msg.sender] == 0;
  ensures \old(map.inserted[msg.sender]) -> map.keys.length == \old(map.keys.length) - 1;
  ensures !\old(map.inserted[msg.sender]) -> map.keys.length == \old(map.keys.length);
  function removeFromMapping() public {
    address key = msg.sender;
    if (!map.inserted[key]) {
      return;
    }
    delete map.inserted[key];
    delete map.values[key];
    uint256 index = map.indexOf[key];
    address lastKey = map.keys[map.keys.length - 1];
    map.indexOf[lastKey] = index;
    delete map.indexOf[key];
    map.keys[index] = lastKey;
    map.keys.pop();
  }
}

local instance : InContract := ⟨IterableMapping⟩

open scoped Scoped

/-! ## The clauses by hand

Each `ensures` clause, without the class invariants, by `sol_prove`;
`\old(…)` is a parameter `n` for the old length, and the case split on
`\old(map.inserted[msg.sender])` is a premise. -/

/-- `getFromMap()`: `ensures v == map.values[msg.sender]`. -/
theorem getFromMap_clause : ⊢ dl!{ [ uint y = getFromMap(); ] y == map.values[msg.sender] } := by
  sol_prove
/-- `sizeOfMapping()`: `ensures s == map.keys.length`. -/
theorem sizeOfMapping_clause : ⊢ dl!{ [ uint y = sizeOfMapping(); ] y == map.keys.length } := by
  sol_prove
/-- `getKeyAtIndex(index)`: `ensures k == map.keys[index]`. -/
theorem getKeyAtIndex_clause : ⊢ dl!{ [ uint y = getKeyAtIndex(i); ] y == map.keys[i] } := by
  sol_prove
/-- `setInMapping(val)`: `ensures map.values[msg.sender] == val && map.inserted[msg.sender]`. -/
theorem setInMapping_entry :
    ⊢ dl!{ [ setInMapping(x); ] map.values[msg.sender] == x && map.inserted[msg.sender] == true } := by
  sol_prove
/-- `setInMapping(val)`, a new key: `!\old(map.inserted[msg.sender]) -> map.keys.length ==
\old(map.keys.length) + 1 && map.keys[\old(map.keys.length)] == msg.sender && map.indexOf[msg.sender] == \old(map.keys.length)`. -/
theorem setInMapping_new :
    ⊢ dl!{ map.inserted[msg.sender] == false && n == map.keys.length → [ setInMapping(x); ]
      map.keys.length == n + 1 && map.keys[n] == msg.sender && map.indexOf[msg.sender] == n } := by
  sol_prove
/-- `setInMapping(val)`, a known key: `\old(map.inserted[msg.sender]) -> map.keys.length == \old(map.keys.length)`. -/
theorem setInMapping_known :
    ⊢ dl!{ map.inserted[msg.sender] == true && n == map.keys.length → [ setInMapping(x); ]
      map.keys.length == n } := by
  sol_prove
/-- `removeFromMapping()`, a known key: `ensures !map.inserted[msg.sender] && map.values[msg.sender] == 0`. -/
theorem removeFromMapping_entry_known :
    ⊢ dl!{ map.inserted[msg.sender] == true → [ removeFromMapping(); ]
      map.inserted[msg.sender] == false && map.values[msg.sender] == 0 } := by
  sol_prove
/-- `removeFromMapping()`, an absent key: the same clause, where the first
class invariant gives `map.values[msg.sender] == 0` (the function returns
at once). -/
theorem removeFromMapping_entry_absent :
    ⊢ dl!{ map.inserted[msg.sender] == false && map.values[msg.sender] == 0 → [ removeFromMapping(); ]
      map.inserted[msg.sender] == false && map.values[msg.sender] == 0 } := by
  sol_prove
/-- `removeFromMapping()`, a known key: `\old(map.inserted[msg.sender]) -> map.keys.length == \old(map.keys.length) - 1`. -/
theorem removeFromMapping_known :
    ⊢ dl!{ map.inserted[msg.sender] == true && n == map.keys.length → [ removeFromMapping(); ]
      map.keys.length == n - 1 } := by
  sol_prove
/-- `removeFromMapping()`, an absent key: `!\old(map.inserted[msg.sender]) -> map.keys.length == \old(map.keys.length)`. -/
theorem removeFromMapping_absent :
    ⊢ dl!{ map.inserted[msg.sender] == false && n == map.keys.length → [ removeFromMapping(); ]
      map.keys.length == n } := by
  sol_prove

/-! ## The obligations

Unknown, all five.  `spec!{f}` assumes and owes the three quantified class
invariants.  Even for the getters, whose leaf after `sol_derive` is the
assumed invariants owed again over the same storage
(`(∀ a, …) ∧ (∀ a, …) ∧ (∀ i, …) ⟹ (∀ a, …) ∧ (∀ a, …) ∧ (∀ i, …) ∧ result = …`),
`sol_spec` stops at `maximum recursion depth` (and at the heartbeat limit
with a larger `maxRecDepth`), `sol_decide` and `sol_close_quantified` leave
it open.  Missing: a closer step that discharges an owed quantified
invariant by the identical assumed one before unfolding the reads, and,
for `setInMapping` and `removeFromMapping`, the invariants re-established
past the writes (for `removeFromMapping`, the swap with the last key, a
two-index argument over `map.keys` and `map.indexOf`). -/

/-- Unknown: `getFromMap()`'s obligation (see above). -/
def getFromMapTarget := spec!{ getFromMap }
/-- Unknown: `getKeyAtIndex(index)`'s obligation. -/
def getKeyAtIndexTarget := spec!{ getKeyAtIndex }
/-- Unknown: `sizeOfMapping()`'s obligation. -/
def sizeOfMappingTarget := spec!{ sizeOfMapping }
/-- Unknown: `setInMapping(val)`'s obligation. -/
def setInMappingTarget := spec!{ setInMapping }
/-- Unknown: `removeFromMapping()`'s obligation. -/
def removeFromMappingTarget := spec!{ removeFromMapping }

end Solidity.Examples.Benchmark.SolkeyData.IterableMapping
