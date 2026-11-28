import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# SWC-100: `HashForEther`, explicit visibility (fixed)

Source: SWC registry, `visibility_not_set_fixed.sol`, pinned revision:
<https://github.com/SmartContractSecurity/SWC-registry/blob/1b6227074ecd180b374e4844153afdda0332f979/entries/docs/SWC-100.md#visibility_not_set_fixedsol>.

The changes and the clause are those of the vulnerable
`visibility_not_set.sol` (`Swc/HashForEther.lean`).  `_sendWinnings` is now
`internal`: no longer an entry point, it carries no clause.

Verdict: `withdrawWinnings` (the only public function) proved.
-/
namespace Solidity.Examples.Benchmark.Swc.HashForEtherFixed
/-- `visibility_not_set_fixed.sol`. -/
def HashForEther : Contract := contract!{
  function _sendWinnings() internal {
    payable(msg.sender).transfer(address(this).balance);
  }
  ensures msg.sender % 4294967296 == 0;
  function withdrawWinnings() public {
    require(uint32(msg.sender) == 0);
    _sendWinnings();
  }
}
local instance : InContract := ⟨HashForEther⟩
open scoped Scoped
/-- `withdrawWinnings`: only a winner is paid. -/
theorem spec_withdrawWinnings : ⊢ spec!{ withdrawWinnings } := by
  sol_prove
end Solidity.Examples.Benchmark.Swc.HashForEtherFixed
