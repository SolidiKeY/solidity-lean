import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `SendingEther`

Source: <https://github.com/SolidiKeY/solkey/blob/50a1469c8c34abf522c7027e47e6f53292d6920a/keyext.solidity.examples/contracts/benchmark/SendingEther.sol>.
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

theorem spec_sendViaTransfer : ⊢ spec!{ sendViaTransfer } := by sol_prove
theorem spec_sendViaSend : ⊢ spec!{ sendViaSend } := by sol_prove
theorem spec_sendViaCall : ⊢ spec!{ sendViaCall } := by sol_prove

end Solidity.Examples.Benchmark.SolkeyBench.SendingEther
