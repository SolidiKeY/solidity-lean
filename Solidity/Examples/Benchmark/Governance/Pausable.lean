import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Governance benchmark: Pausable
Source: OpenZeppelin Contracts v4.9.6, security/Pausable.sol:
<https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v4.9.6/contracts/security/Pausable.sol>.
Internal _pause/_unpause are exposed as functions for direct specification;
whenNotPaused/whenPaused are inlined and event emissions omitted.
This base class deliberately supplies no caller authorization, just as the source.
Every function below has a natural @custom:key clause.
Verdicts: constructor, paused, pause, unpause: proved.
-/
namespace Solidity.Examples.Benchmark.Governance.Pausable
def Pausable : Contract := contract!{
  bool private stopped;
  ensures !stopped;
  constructor() { stopped = false; }
  ensures \result == stopped;
  function paused() public view returns (bool) { return stopped; }
  ensures !\old(stopped) && stopped;
  function pause() public {
    require(!stopped);
    stopped = true;
  }
  ensures \old(stopped) && !stopped;
  function unpause() public {
    require(stopped);
    stopped = false;
  }
}
local instance : InContract := ⟨Pausable⟩
open scoped Scoped
/-- `@custom:key` obligation for `constructor`. -/
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove
/-- `@custom:key` obligation for `paused`. -/
theorem spec_paused : ⊢ spec!{ paused } := by
  sol_prove
/-- `@custom:key` obligation for `pause`. -/
theorem spec_pause : ⊢ spec!{ pause } := by
  sol_prove
/-- `@custom:key` obligation for `unpause`. -/
theorem spec_unpause : ⊢ spec!{ unpause } := by
  sol_prove
end Solidity.Examples.Benchmark.Governance.Pausable
