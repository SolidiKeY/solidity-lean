import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Run

/-!
# SWC-100: `HashForEther`, default visibility (vulnerable)

Source: SWC registry, `visibility_not_set.sol`, pinned revision:
<https://github.com/SmartContractSecurity/SWC-registry/blob/1b6227074ecd180b374e4844153afdda0332f979/entries/docs/SWC-100.md#visibility_not_setsol>.

Under 0.4 a function without a visibility specifier is `public`, so anyone
calls `_sendWinnings` and is paid without the winner check.

Changes: the implicit `public` is written; `this.balance` is
`address(this).balance` and `msg.sender.transfer` is
`payable(msg.sender).transfer` (the 0.4 `uint32(msg.sender)` is kept); `_sendWinnings` is declared first
(`contract!` resolves a call against earlier functions).  The natural clause,
on every public function: it returns only to a winner, `uint32(msg.sender)
== 0`, written `msg.sender % 4294967296 == 0` (the clause grammar has no
conversions; `uint32` keeps the low 32 bits).

Verdicts: `withdrawWinnings` proved; `_sendWinnings` refuted (a
kernel-checked run below).  Fixed variant: `Swc/HashForEtherFixed.lean`.
-/
namespace Solidity.Examples.Benchmark.Swc.HashForEther
/-- `visibility_not_set.sol`, the default visibility written out. -/
def HashForEther : Contract := contract!{
  ensures msg.sender % 4294967296 == 0;
  function _sendWinnings() public {
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
/-- `_sendWinnings`: only a winner is paid; refuted below. -/
def sendWinnings_obligation : Fml HashForEther [] := spec!{ _sendWinnings }

/-- Refuted: account `1` (`uint32(1) == 1`, not a winner) calls
`_sendWinnings()` on a contract holding `5` and the call returns, unguarded. -/
example :
    (Prog.run { State.ofStorage (show Storage HashForEther from .nil) with
        selfBalance := uintOfNat 5,
        tx := { msgSender := uintOfNat 1, selfAddress := uintOfNat 2 } }
      (sol{ _sendWinnings(); })).toOption.isSome = true := by
  decide +kernel
end Solidity.Examples.Benchmark.Swc.HashForEther
