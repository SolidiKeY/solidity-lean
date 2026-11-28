import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Patterns benchmark: two-step ownership handover

Source: Compound Protocol, `Unitroller.sol` (`_setPendingAdmin`,
`_acceptAdmin`), pinned revision:
<https://github.com/compound-finance/compound-protocol/blob/a3214f67b73310d547e00fc578e8355911c9d376/contracts/Unitroller.sol>.

Not OpenZeppelin's `Ownable2Step`: a failed check returns an error code
instead of reverting. Changes: only the admin handover of `Unitroller` is
kept (no implementation slot or delegation); `fail(Error.UNAUTHORIZED, …)`,
which logs and returns the code, is `return uint(Error.UNAUTHORIZED);`
(`1`), and the events are dropped by elaboration. Natural `@custom:key`
clauses: a nomination succeeds for the admin only, acceptance for the nominee
only, and a failed call changes nothing.

Verdicts: constructor, _setPendingAdmin, _acceptAdmin proved (the last by
`sol_auto`: `sol_prove` alone leaves the short-circuit `||` leaf).
-/
namespace Solidity.Examples.Benchmark.Patterns.TwoStepOwnership
def Unitroller : Contract := contract!{
  enum Error { NO_ERROR, UNAUTHORIZED }
  address public admin;
  address public pendingAdmin;
  event NewPendingAdmin(address oldPendingAdmin, address newPendingAdmin);
  event NewAdmin(address oldAdmin, address newAdmin);
  ensures admin == msg.sender;
  constructor() {
    admin = msg.sender;
  }
  ensures admin == \old(admin);
  ensures \result == 0 -> msg.sender == admin && pendingAdmin == newPendingAdmin;
  ensures \result != 0 -> msg.sender != admin && pendingAdmin == \old(pendingAdmin);
  function _setPendingAdmin(address newPendingAdmin) public returns (uint) {
    if (msg.sender != admin) {
      return uint(Error.UNAUTHORIZED);
    }
    address oldPendingAdmin = pendingAdmin;
    pendingAdmin = newPendingAdmin;
    emit NewPendingAdmin(oldPendingAdmin, newPendingAdmin);
    return uint(Error.NO_ERROR);
  }
  ensures \result == 0 -> msg.sender == \old(pendingAdmin) && msg.sender != 0 && admin == msg.sender && pendingAdmin == 0;
  ensures \result != 0 -> admin == \old(admin) && pendingAdmin == \old(pendingAdmin);
  function _acceptAdmin() public returns (uint) {
    if (msg.sender != pendingAdmin || msg.sender == address(0)) {
      return uint(Error.UNAUTHORIZED);
    }
    address oldAdmin = admin;
    address oldPendingAdmin = pendingAdmin;
    admin = pendingAdmin;
    pendingAdmin = address(0);
    emit NewAdmin(oldAdmin, admin);
    emit NewPendingAdmin(oldPendingAdmin, pendingAdmin);
    return uint(Error.NO_ERROR);
  }
}
local instance : InContract := ⟨Unitroller⟩
open scoped Scoped
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove
theorem spec__setPendingAdmin : ⊢ spec!{ _setPendingAdmin } := by
  sol_prove
theorem spec__acceptAdmin : ⊢ spec!{ _acceptAdmin } := by
  sol_auto
end Solidity.Examples.Benchmark.Patterns.TwoStepOwnership
