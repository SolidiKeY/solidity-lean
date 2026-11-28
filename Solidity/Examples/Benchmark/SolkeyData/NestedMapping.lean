import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `NestedMapping` (solkey real-world)

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/contracts/real-world/NestedMapping.sol>
(after Solidity by Example's `mapping/Mapping.sol`, revision `5bcdca02`).

The program is the one `Examples/Benchmark/Mapping.lean` already has, from
solkey's `benchmark/Mapping.sol`; what is new here are the real-world
clauses: a named result `v` for `get`, and the two-key frame
`\forall address a; \forall uint j; a != _addr1 || j != _i -> …` for
`set` and `remove`.  Only the obligations `spec!{f}` are stated (the
single-entry clauses are proved by hand in `Mapping.lean`).

Changes: none but the spelling of `contract!{ … }`.  Verdicts: `get` proved;
`set` and `remove` unknown (the two-key frame), each frame case proved by hand.

```solidity
contract NestedMapping {
    mapping(address => mapping(uint256 => bool)) public nested;

    /// @custom:key ensures v == nested[_addr1][_i]
    function get(address _addr1, uint256 _i) public view returns (bool v) {
        return nested[_addr1][_i];
    }

    /// @custom:key ensures nested[_addr1][_i] == _boo
    /// @custom:key ensures \forall address a; \forall uint j; a != _addr1 || j != _i -> nested[a][j] == \old(nested[a][j])
    function set(address _addr1, uint256 _i, bool _boo) public {
        nested[_addr1][_i] = _boo;
    }

    /// @custom:key ensures !nested[_addr1][_i]
    /// @custom:key ensures \forall address a; \forall uint j; a != _addr1 || j != _i -> nested[a][j] == \old(nested[a][j])
    function remove(address _addr1, uint256 _i) public {
        delete nested[_addr1][_i];
    }
}
```
-/

namespace Solidity.Examples.Benchmark.SolkeyData.NestedMapping

/-- `NestedMapping.sol`, as solkey publishes it, with its clauses. -/
def NestedMapping : Contract := contract!{
  mapping(address => mapping(uint256 => bool)) public nested;
  ensures v == nested[_addr1][_i];
  function get(address _addr1, uint256 _i) public view returns (bool v) {
    return nested[_addr1][_i];
  }
  ensures nested[_addr1][_i] == _boo;
  ensures \forall address a; \forall uint j; a != _addr1 || j != _i -> nested[a][j] == \old(nested[a][j]);
  function set(address _addr1, uint256 _i, bool _boo) public {
    nested[_addr1][_i] = _boo;
  }
  ensures !nested[_addr1][_i];
  ensures \forall address a; \forall uint j; a != _addr1 || j != _i -> nested[a][j] == \old(nested[a][j]);
  function remove(address _addr1, uint256 _i) public {
    delete nested[_addr1][_i];
  }
}

local instance : InContract := ⟨NestedMapping⟩

open scoped Scoped

/-- `get(_addr1, _i)`: `ensures v == nested[_addr1][_i]`. -/
theorem spec_get : ⊢ spec!{ get } := by
  sol_prove
/-- Unknown: `set(_addr1, _i, _boo)`'s obligation.  After `sol_derive` one
leaf is left, the written entry and the two-key frame
`∀ a j, ¬a = _addr1 ∨ ¬j = _i → find(storage, nested[a][j]) = find(old, nested[a][j])`
past `save(storage, nested[_addr1][_i], _boo)`; `sol_spec`, `sol_decide`,
`sol_close_quantified` and `sol_close` (heartbeat timeout) leave it open.
Missing: a closer that splits the disjunctive key inequality into the
row case (a different outer key) and the column case (the same row, a
different inner key) under a nested `save`; the one-key frame of
`Mapping.lean` closes.  Each case alone is proved below. -/
def setTarget := spec!{ set }
/-- Unknown: `remove(_addr1, _i)`'s obligation, the same leaf with
`delete` (the default `false` saved). -/
def removeTarget := spec!{ remove }

/-- `set(a, i, false)`, other row: `a != _addr1 -> nested[a][j] == \old(nested[a][j])`. -/
theorem set_frame_row :
    ⊢ dl!{ b != a && nested[b][j] == true → [ set(a, i, false); ] nested[b][j] == true } := by
  sol_prove
/-- `set(a, i, false)`, same row, other column: `j != _i -> …`. -/
theorem set_frame_column :
    ⊢ dl!{ j != i && nested[a][j] == true → [ set(a, i, false); ] nested[a][j] == true } := by
  sol_prove
/-- `remove(a, i)`, other row. -/
theorem remove_frame_row :
    ⊢ dl!{ b != a && nested[b][j] == true → [ remove(a, i); ] nested[b][j] == true } := by
  sol_prove
/-- `remove(a, i)`, same row, other column. -/
theorem remove_frame_column :
    ⊢ dl!{ j != i && nested[a][j] == true → [ remove(a, i); ] nested[a][j] == true } := by
  sol_prove

end Solidity.Examples.Benchmark.SolkeyData.NestedMapping
