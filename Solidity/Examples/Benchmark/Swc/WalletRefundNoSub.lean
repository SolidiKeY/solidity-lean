import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Run

/-!
# SWC-105: `Wallet`, refund without debit (vulnerable)

Source: SWC registry, `wallet_02_refund_nosub.sol`, pinned revision:
<https://github.com/SmartContractSecurity/SWC-registry/blob/1b6227074ecd180b374e4844153afdda0332f979/entries/docs/SWC-105.md#wallet_02_refund_nosubsol>.

"Unfortunately the developer forgot set the user's balance to 0 when
refund() is called. An attacker can pay in a small amount of Ether and call
refund() repeatedly to empty the contract."

Changes: `this.balance` is spelled `address(this).balance`; `assert` is
`require` (both revert; the model has no distinct panic); comments dropped.
The 0.4 arithmetic is kept as written: each `+=`/`-=` is guarded so that
checked and wrapping arithmetic agree.  The clauses are the ones the fixed
`wallet_01_ok.sol` (`Swc/WalletOk.lean`) is held to.

Verdicts: constructor, `withdraw`, `migrateTo` proved; `refund` refuted (a
kernel-checked run below); `deposit` unknown (closer gap, below).

```solidity
contract Wallet {
    address creator;
    mapping(address => uint256) balances;
    constructor() public { creator = msg.sender; }
    function deposit() public payable {
        assert(balances[msg.sender] + msg.value > balances[msg.sender]);
        balances[msg.sender] += msg.value;
    }
    function withdraw(uint256 amount) public {
        require(amount <= balances[msg.sender]);
        msg.sender.transfer(amount);
        balances[msg.sender] -= amount;
    }
    function refund() public {
        msg.sender.transfer(balances[msg.sender]);
    }
    function migrateTo(address to) public {
        require(creator == msg.sender);
        to.transfer(this.balance);
    }
}
```
-/

namespace Solidity.Examples.Benchmark.Swc.WalletRefundNoSub

/-- `wallet_02_refund_nosub.sol` with the wallet's natural clauses. -/
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

/-- `refund`: `ensures balances[msg.sender] == 0`, refuted below. -/
def refund_obligation : Fml Wallet [] := spec!{ refund }

/-- Account `1` credited `5`; the creator is `0`. -/
private def creditedStore : Storage Wallet :=
  .cons (.prim (uintOfNat 0))
    (.cons (.map (.cons (uintOfNat 1) (.prim (uintOfNat 5)) .nil)
      (.prim (uintOfNat 0))) .nil)

/-- Refuted: account `1`, credited `5` in a wallet holding `5`, is paid by
`refund()` and keeps its credit `5`, so a second `refund()` is funded again. -/
example :
    ((Prog.run { State.ofStorage creditedStore with
        selfBalance := uintOfNat 5,
        tx := { msgSender := uintOfNat 1, selfAddress := uintOfNat 2 } }
      (sol{ refund(); uint b = balances[msg.sender]; })).toOption.map
        fun o => o.st.env.1.1) = some 5 := by
  decide +kernel

end Solidity.Examples.Benchmark.Swc.WalletRefundNoSub
