import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# SWC-105: `Wallet` (fixed)

Source: SWC registry, `wallet_01_ok.sol`, pinned revision:
<https://github.com/SmartContractSecurity/SWC-registry/blob/1b6227074ecd180b374e4844153afdda0332f979/entries/docs/SWC-105.md#wallet_01_oksol>.

"User can add pay in and withdraw Ether. Nobody can withdraw more Ether than
they paid in."  The changes and clauses are those of the vulnerable
`wallet_02_refund_nosub.sol` (`Swc/WalletRefundNoSub.lean`); the only
difference in the source is the debit `balances[msg.sender] = 0` in `refund`.

Verdicts: constructor, `withdraw`, `refund`, `migrateTo` proved; `deposit`
unknown (closer gap, below).

```solidity
    function refund() public {
        msg.sender.transfer(balances[msg.sender]);
        balances[msg.sender] = 0;
    }
```
-/

namespace Solidity.Examples.Benchmark.Swc.WalletOk

/-- `wallet_01_ok.sol` with the wallet's natural clauses. -/
def Wallet : Contract := contract!{
  address creator;
  mapping(address => uint256) balances;
  ensures creator == msg.sender;
  constructor() { creator = msg.sender; }
  ensures balances[msg.sender] == \old(balances[msg.sender]) + msg.value;
  function deposit() public payable {
    require(balances[msg.sender] + msg.value > balances[msg.sender]);
    balances[msg.sender] += msg.value;
  }
  ensures balances[msg.sender] == \old(balances[msg.sender]) - amount;
  function withdraw(uint256 amount) public {
    require(amount <= balances[msg.sender]);
    msg.sender.transfer(amount);
    balances[msg.sender] -= amount;
  }
  ensures balances[msg.sender] == 0;
  function refund() public {
    msg.sender.transfer(balances[msg.sender]);
    balances[msg.sender] = 0;
  }
  ensures msg.sender == creator;
  function migrateTo(address to) public {
    require(creator == msg.sender);
    to.transfer(address(this).balance);
  }
}

local instance : InContract := ⟨Wallet⟩
open scoped Scoped

/-- `constructor`: `ensures creator == msg.sender`. -/
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove

/-- `refund`: `ensures balances[msg.sender] == 0`. -/
theorem spec_refund : ⊢ spec!{ refund } := by
  sol_prove

/-- `migrateTo`: only the creator migrates. -/
theorem spec_migrateTo : ⊢ spec!{ migrateTo } := by
  sol_prove

/-- `withdraw`: `ensures balances[msg.sender] == \old(balances[msg.sender]) - amount`. -/
theorem spec_withdraw : ⊢ spec!{ withdraw } := by
  sol_prove

/-- `deposit`: unknown.  `sol_prove` leaves one leaf: after the payable
snapshot `{ old := storage ‖ net := … ‖ selfBalance := … }` and the save
of `balances[msg.sender]`, `find(storage, balances[msg.sender]) =
find(old, balances[msg.sender]) + msg.value`.  The closer does not resolve
`old` through the parallel payable update (the gap of
`Benchmark/Defi/Escrow.lean`'s `deposit`). -/
def deposit_obligation : Fml Wallet [] := spec!{ deposit }

end Solidity.Examples.Benchmark.Swc.WalletOk
