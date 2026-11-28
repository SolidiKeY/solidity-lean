import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# SWC-105: `MultiOwnable` with `onlyOwner` (fixed)

Source: SWC registry, `multiowned_not_vulnerable.sol`, pinned revision:
<https://github.com/SmartContractSecurity/SWC-registry/blob/1b6227074ecd180b374e4844153afdda0332f979/entries/docs/SWC-105.md#multiowned_not_vulnerablesol>.

The changes and clauses are those of the vulnerable
`multiowned_vulnerable.sol` (`Swc/MultiOwnedVulnerable.lean`); the only
difference in the source is the modifier on `newOwner`:

```solidity
  function newOwner(address _owner) onlyOwner external returns (bool) {
```

Verdicts: constructor, `newOwner`, `deleteOwner` proved.
-/
namespace Solidity.Examples.Benchmark.Swc.MultiOwnedFixed
/-- `multiowned_not_vulnerable.sol` with the owners' natural clauses. -/
def MultiOwnable : Contract := contract!{
  address public root;
  mapping(address => address) public owners;
  ensures root == msg.sender && owners[msg.sender] == msg.sender;
  constructor() {
    root = msg.sender;
    owners[root] = root;
  }
  modifier onlyOwner() {
    require(owners[msg.sender] != 0);
    _;
  }
  ensures \old(owners[msg.sender]) != 0 && owners[_owner] == msg.sender && \result;
  function newOwner(address _owner) onlyOwner external returns (bool) {
    require(_owner != 0);
    owners[_owner] = msg.sender;
    return true;
  }
  ensures \old(owners[msg.sender]) != 0 && owners[_owner] == 0 && \result;
  function deleteOwner(address _owner) onlyOwner external returns (bool) {
    require(owners[_owner] == msg.sender || (owners[_owner] != 0 && msg.sender == root));
    owners[_owner] = 0;
    return true;
  }
}
local instance : InContract := ⟨MultiOwnable⟩
open scoped Scoped
/-- `constructor`: the deployer is the root and its own parent. -/
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove
/-- `newOwner`: only an owner adds owners, and the new owner's parent is the sender. -/
theorem spec_newOwner : ⊢ spec!{ newOwner } := by
  sol_prove
/-- `deleteOwner`: only an owner deletes, and the owner is cleared. -/
theorem spec_deleteOwner : ⊢ spec!{ deleteOwner } := by
  sol_prove
end Solidity.Examples.Benchmark.Swc.MultiOwnedFixed
