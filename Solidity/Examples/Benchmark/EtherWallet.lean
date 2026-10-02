import Solidity.Calculus.Close

/-!
# Benchmark: `EtherWallet`

Source: solkey's `keyext.solidity.examples/benchmark/EtherWallet.sol`, itself
from
<https://raw.githubusercontent.com/Cyfrin/solidity-by-example.github.io/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/app/ether-wallet/EtherWallet.sol>.
Changes from the published text, as solkey's benchmark file makes them: the
`require` message is dropped (a string literal).  Here besides:
`payable(msg.sender)` and `payable(…)` are the identity on a `uint` and are
written without the conversion (stream A's `payable(x)`); the `payable`
`receive()` is dropped, since nothing here calls it; the constructor's body
`owner = msg.sender;` is stated on its own (`ctor`).  `getBalance()`, which
solkey's copy drops because `address(this).balance` crashed its parser, is
back (`getBalance`).

`@custom:key ensures net(owner) == \old(net(owner)) - _amount`: no term
reads the `net` ledger (`Close.lean`), so the clause is shown as a run of
the interpreter (`withdrawRunNet`), as `Examples/Tactics/Net.lean` shows the ledger.
What a formula does read is the funds, `address(this).balance`, which the
same `transfer` spends: `withdrawFunds` is that clause's other half.  The
payment runs with `transferNoCallback`, as solkey's net rules do; with
callbacks the recipient could change the funds before control returns
(`Semantics/Callback.lean`).
-/

namespace Solidity.Examples.Benchmark.EtherWallet

open Proves

def EtherWallet : Contract := contract!{
  address owner;
  function withdraw(uint _amount) {
    require(msg.sender == owner);
    msg.sender.transfer(_amount);
  }
  function getBalance() returns (uint) {
    return address(this).balance;
  }
}

local instance : InContract := ⟨EtherWallet⟩

/-- `owner = msg.sender;` — the constructor's body. -/
theorem ctor : ⊨ dl!{ [ owner = msg.sender; ] owner == msg.sender } := by
  sol_symex
  sol_close

/-- `ensures msg.sender == owner && owner == \old(owner)`. -/
theorem withdrawOwner :
    ⊨ dl!{ [ uint o = owner; withdraw(x); ] msg.sender == o && owner == o } := by
  sol_symex
  sol_close

/-- The funds are less by the amount paid: `address(this).balance` after
`withdraw(x)` is `f`, computed as `address(this).balance - x` before it (a
`uint` subtraction, which reverts where the funds do not cover `x`, as the
payment does). -/
theorem withdrawFunds :
    ⊨ dl!{ [ uint f = address(this).balance - x; withdraw(x); ] address(this).balance == f } := by
  sol_symex
  sol_close

/-- `getBalance()` returns the funds. -/
theorem getBalanceFunds :
    ⊨ dl!{ [ uint f = address(this).balance; uint g = getBalance(); ] g == f } := by
  sol_symex
  sol_close

/-! ## Runs: the ledger

`7` deploys the wallet with `100` wei and withdraws `30`. -/

/-- A fresh wallet holding `100`, called by `7`. -/
def store : Semantics.State :=
  { storage := [("owner", .int 0)], selfBalance := 100,
    tx := { msgSender := 7 } }

/-- `ensures net(owner) == \old(net(owner)) - _amount`: `7`'s entry is `30`
less, and the funds are `70`. -/
theorem withdrawRunNet :
    (do let σ ← Prog.run store (sol{ owner = msg.sender; withdraw(30); } : Prog EtherWallet)
        pure (σ.getNet 7, σ.selfBalance)) = .ok (-30, 70) := rfl

/-- More than the funds: the payment reverts. -/
theorem withdrawRunUnfunded :
    Prog.run store (sol{ owner = msg.sender; withdraw(130); } : Prog EtherWallet) =
      .error .revert := rfl

/-- Anyone but the owner: `withdraw` reverts. -/
theorem withdrawRunOther :
    Prog.run store (sol{ owner = 3; withdraw(30); } : Prog EtherWallet) = .error .revert := rfl

end Solidity.Examples.Benchmark.EtherWallet
