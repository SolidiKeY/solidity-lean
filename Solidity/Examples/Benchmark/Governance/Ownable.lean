import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Governance benchmark: Ownable
Source: OpenZeppelin Contracts v4.9.6, access/Ownable.sol:
<https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v4.9.6/contracts/access/Ownable.sol>.
The owner state machine is flattened: Context._msgSender is msg.sender,
modifiers and internal _transferOwnership are inlined, events omitted.
Address zero is spelled 0 (addresses use the model's uint representation).
No claim about event logs or inheritance is made.
Every function below has a natural @custom:key clause.
The verdicts below concern this model only. Complete-original executable
modeling remains an obligation; no full-source verification credit is claimed.
Model verdicts: constructor, owner, renounceOwnership, transferOwnership: proved.
-/
namespace Solidity.Examples.Benchmark.Governance.Ownable
def Ownable : Contract := contract!{
  address private currentOwner;
  ensures currentOwner == msg.sender;
  constructor() { currentOwner = msg.sender; }
  ensures \result == currentOwner;
  function owner() public view returns (address) { return currentOwner; }
  ensures msg.sender == \old(currentOwner) && currentOwner == 0;
  function renounceOwnership() public {
    require(msg.sender == currentOwner);
    currentOwner = 0;
  }
  ensures msg.sender == \old(currentOwner) && currentOwner == newOwner && newOwner != 0;
  function transferOwnership(address newOwner) public {
    require(msg.sender == currentOwner);
    require(newOwner != 0);
    currentOwner = newOwner;
  }
}
local instance : InContract := ⟨Ownable⟩
open scoped Scoped
/-- `@custom:key` obligation for `constructor`. -/
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove
/-- `@custom:key` obligation for `owner`. -/
theorem spec_owner : ⊢ spec!{ owner } := by
  sol_prove
/-- `@custom:key` obligation for `renounceOwnership`. -/
theorem spec_renounceOwnership : ⊢ spec!{ renounceOwnership } := by
  sol_prove
/-- `@custom:key` obligation for `transferOwnership`. -/
theorem spec_transferOwnership : ⊢ spec!{ transferOwnership } := by
  sol_prove
end Solidity.Examples.Benchmark.Governance.Ownable
