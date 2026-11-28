import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Run

/-!
# SWC-105: `MultiOwnable` without `onlyOwner` (vulnerable)

Source: SWC registry, `multiowned_vulnerable.sol`, pinned revision:
<https://github.com/SmartContractSecurity/SWC-registry/blob/1b6227074ecd180b374e4844153afdda0332f979/entries/docs/SWC-105.md#multiowned_vulnerablesol>.

The access modifier `onlyOwner` is missing on `newOwner` ("Note that the
"onlyOwner" modifier is missing here."), so anyone makes anyone an owner.

Changes: address zero is spelled `0`; NatSpec comments dropped; the test
harness `TestContract is MultiOwnable` (an `onlyOwner` `withdrawAll` and an
empty payable fallback) is not modelled: its guard is the modifier proved in
`deleteOwner`.  The natural clauses state that only an owner (a sender with a
nonzero parent) adds or deletes owners; they are those of the fixed
`multiowned_not_vulnerable.sol` (`Swc/MultiOwnedFixed.lean`).

Verdicts: constructor and `deleteOwner` proved; `newOwner` refuted (a
kernel-checked run below).
-/
namespace Solidity.Examples.Benchmark.Swc.MultiOwnedVulnerable
/-- `multiowned_vulnerable.sol` with the owners' natural clauses. -/
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
  function newOwner(address _owner) external returns (bool) {
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
/-- `deleteOwner`: only an owner deletes, and the owner is cleared. -/
theorem spec_deleteOwner : ⊢ spec!{ deleteOwner } := by
  sol_prove
/-- `newOwner`: only an owner adds owners; refuted below. -/
def newOwner_obligation : Fml MultiOwnable [] := spec!{ newOwner }

/-- Root `1`, the only owner. -/
private def rootStore : Storage MultiOwnable :=
  .cons (.prim (uintOfNat 1))
    (.cons (.map (.cons (uintOfNat 1) (.prim (uintOfNat 1)) .nil)
      (.prim (uintOfNat 0))) .nil)

/-- Refuted: account `7`, no owner (`owners[7] == 0`), calls `newOwner(7)`
and returns with `owners[7] == 7`: it is now an owner. -/
example :
    ((Prog.run { State.ofStorage rootStore with tx := { msgSender := uintOfNat 7 } }
      (sol{ address p = owners[msg.sender]; bool r = newOwner(7);
            address q = owners[msg.sender]; })).toOption.map
        fun o => (o.st.env.2.2.1.1, o.st.env.1.1)) = some (0, 7) := by
  decide +kernel
end Solidity.Examples.Benchmark.Swc.MultiOwnedVulnerable
