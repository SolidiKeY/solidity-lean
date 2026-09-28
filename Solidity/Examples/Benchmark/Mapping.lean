import Solidity.Calculus.DecideComplete

/-!
# Benchmark: `Mapping` and `NestedMapping`

Source: <https://raw.githubusercontent.com/Cyfrin/solidity-by-example.github.io/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/mapping/Mapping.sol>
(solkey's `keyext.solidity.examples/benchmark/Mapping.sol`).

Changes: none but the spelling of `contract!{ … }` (two contracts, as the
file has).  solkey's clauses are the theorems below; `\forall address a;
a != _addr -> myMap[a] == \old(myMap[a])` is stated for one key `b`, a
parameter, with `v` its old value.  A free name of a formula is a `uint`
parameter, so `NestedMapping.set`'s `bool` is passed as both literals.  The
`remove` clauses carry a premise that the old entry has its declared type
(`remove_spec`).

```solidity
contract Mapping {
    // Mapping from address to uint
    mapping(address => uint256) public myMap;

    function get(address _addr) public view returns (uint256) {
        // Mapping always returns a value.
        // If the value was never set, it will return the default value.
        return myMap[_addr];
    }

    function set(address _addr, uint256 _i) public {
        // Update the value at this address
        myMap[_addr] = _i;
    }

    function remove(address _addr) public {
        // Reset the value to the default value.
        delete myMap[_addr];
    }
}

contract NestedMapping {
    // Nested mapping (mapping from address to another mapping)
    mapping(address => mapping(uint256 => bool)) public nested;

    function get(address _addr1, uint256 _i) public view returns (bool) {
        // You can get values from a nested mapping
        // even when it is not initialized
        return nested[_addr1][_i];
    }

    function set(address _addr1, uint256 _i, bool _boo) public {
        nested[_addr1][_i] = _boo;
    }

    function remove(address _addr1, uint256 _i) public {
        delete nested[_addr1][_i];
    }
}
```
-/

namespace Solidity.Examples.Benchmark.Mapping

open Proves

/-- `Mapping`, as published. -/
def Mapping : Contract := contract!{
  mapping(address => uint256) public myMap;
  function get(address _addr) public view returns (uint256) {
    return myMap[_addr];
  }
  function set(address _addr, uint256 _i) public {
    myMap[_addr] = _i;
  }
  function remove(address _addr) public {
    delete myMap[_addr];
  }
}

/-- `NestedMapping`, as published. -/
def NestedMapping : Contract := contract!{
  mapping(address => mapping(uint256 => bool)) public nested;
  function get(address _addr1, uint256 _i) public view returns (bool) {
    return nested[_addr1][_i];
  }
  function set(address _addr1, uint256 _i, bool _boo) public {
    nested[_addr1][_i] = _boo;
  }
  function remove(address _addr1, uint256 _i) public {
    delete nested[_addr1][_i];
  }
}

section Mapping

local instance : InContract := ⟨Mapping⟩

/-- `set(a, i)`: `ensures myMap[_addr] == _i`. -/
theorem set_spec : ⊨ dl!{ [ set(a, i); ] myMap[a] == i } := by
  sol_symex
  sol_close

/-- `set(a, i)`: every other key keeps its value. -/
theorem set_frame : ⊨ dl!{ b != a && v == myMap[b] → [ set(a, i); ] myMap[b] == v } := by
  sol_symex
  sol_close

/-- `remove(a)`: `ensures myMap[_addr] == 0`, where `myMap[a]` held a
`uint` (`myMap[a] + 0` evaluates).  A `delete` leaves the default of the old
value, and `⊨` ranges over every storage, `myMap[a]` holding a `bool` too
(`Decide.deleteWithoutWrite`): the premise is the typing every storage of
this contract has. -/
theorem remove_spec : ⊨ dl!{ myMap[a] + 0 == myMap[a] → [ remove(a); ] myMap[a] == 0 } := by
  sol_symex
  sol_decide

/-- `remove(a)`: every other key keeps its value. -/
theorem remove_frame : ⊨ dl!{ b != a && v == myMap[b] → [ remove(a); ] myMap[b] == v } := by
  sol_symex
  sol_close

/-- `set(a, i)` then `get(a)` returns `i`. -/
theorem set_get : ⊨ dl!{ [ set(a, i); uint y = get(a); ] y == i } := by
  sol_symex
  sol_close

end Mapping

section NestedMapping

local instance : InContract := ⟨NestedMapping⟩

/-- `set(a, i, true)`: `ensures nested[_addr1][_i] == _boo`. -/
theorem nested_set_spec_true : ⊨ dl!{ [ set(a, i, true); ] nested[a][i] == true } := by
  sol_symex
  sol_close

/-- `set(a, i, false)`: the same, for the other `bool`. -/
theorem nested_set_spec_false : ⊨ dl!{ [ set(a, i, false); ] nested[a][i] == false } := by
  sol_symex
  sol_close

/-- `remove(a, i)`: `ensures !nested[_addr1][_i]`, where `nested[a][i]`
held a `bool`, `true` or `false` (as `remove_spec`). -/
theorem nested_remove_spec :
    ⊨ dl!{ (nested[a][i] == true → [ remove(a, i); ] nested[a][i] == false) ∧
           (nested[a][i] == false → [ remove(a, i); ] nested[a][i] == false) } := by
  sol_symex
  sol_decide

end NestedMapping

end Solidity.Examples.Benchmark.Mapping
