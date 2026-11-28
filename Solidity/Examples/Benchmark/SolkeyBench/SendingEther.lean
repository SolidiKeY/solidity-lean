import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `SendingEther`

Source: <https://github.com/SolidiKeY/solkey/blob/50a1469c8c34abf522c7027e47e6f53292d6920a/keyext.solidity.examples/contracts/benchmark/SendingEther.sol>.

Changes beyond `contract!{ … }` spelling; the `@custom:key` clauses are written above their functions, invariants first. `payable(x)` is the identity on an address and is dropped (as in `Benchmark/EtherWallet.lean`); `if (c) s;` gets braces. Only `SendEther` is ported: `ReceiveEther` has empty `receive`/`fallback` and no clauses. `address payable` is `address`.

Verdicts are on the declarations below: a `theorem` is proved, a `def …_obligation` is unknown (its stuck goal and the missing closer or rule in its docstring).
-/

namespace Solidity.Examples.Benchmark.SolkeyBench.SendingEther

def SendEther : Contract := contract!{
  ensures _to != this && _to != msg.sender -> net(_to) == \old(net(_to)) - msg.value && net(msg.sender) == \old(net(msg.sender)) + msg.value;
  ensures _to == msg.sender -> net(msg.sender) == \old(net(msg.sender));
  function sendViaTransfer(address payable _to) public payable {
    _to.transfer(msg.value);
  }
  ensures _to != this && _to != msg.sender -> net(_to) == \old(net(_to)) - msg.value && net(msg.sender) == \old(net(msg.sender)) + msg.value;
  ensures _to == msg.sender -> net(msg.sender) == \old(net(msg.sender));
  function sendViaSend(address payable _to) public payable {
    bool sent = _to.send(msg.value);
    require(sent);
  }
  ensures _to != this && _to != msg.sender -> net(_to) == \old(net(_to)) - msg.value && net(msg.sender) == \old(net(msg.sender)) + msg.value;
  ensures _to == msg.sender -> net(msg.sender) == \old(net(msg.sender));
  function sendViaCall(address payable _to) public payable {
    (bool sent, ) = _to.call{value: msg.value}("");
    require(sent);
  }
}

local instance : InContract := ⟨SendEther⟩

open scoped Scoped

/-- Unknown: both net clauses after pay(_to, msg.value) stay open; calculus pay rule that books net for the payee is missing (pay(se,v) leaf stays open; cf. RefundEscrow.beneficiaryWithdraw). -/
def sendViaTransfer_obligation : Fml SendEther [] := spec!{ sendViaTransfer }
/-- Unknown: both net clauses after pay(_to, msg.value) stay open; calculus pay rule that books net for the payee is missing (pay(se,v) leaf stays open; cf. RefundEscrow.beneficiaryWithdraw). -/
def sendViaSend_obligation : Fml SendEther [] := spec!{ sendViaSend }
/-- Unknown: both net clauses after pay(_to, msg.value) stay open; calculus pay rule that books net for the payee is missing (pay(se,v) leaf stays open; cf. RefundEscrow.beneficiaryWithdraw). -/
def sendViaCall_obligation : Fml SendEther [] := spec!{ sendViaCall }

end Solidity.Examples.Benchmark.SolkeyBench.SendingEther
