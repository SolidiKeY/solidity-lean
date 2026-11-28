import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Run
import Solidity.Tools.Counterexample

/-!
# Benchmark: `SendEther`

Source: solkey's
<https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/contracts/real-world/SendEther.sol>,
itself from
<https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/sending-ether/SendingEther.sol>.
Changes: none but the spelling of `contract!{ … }`; `address payable` is
`address`, and `address(this)` in the clauses is `this`.
-/

namespace Solidity.Examples.Benchmark.SolkeyGames.SendEther

def SendEther : Contract := contract!{
  ensures _to != msg.sender && _to != this -> net(_to) == \old(net(_to)) - msg.value && net(msg.sender) == \old(net(msg.sender)) + msg.value;
  ensures _to == msg.sender -> net(_to) == \old(net(_to));
  ensures _to == this -> net(_to) == \old(net(_to)) && net(msg.sender) == \old(net(msg.sender)) + msg.value;
  function sendViaTransfer(address _to) public payable {
    _to.transfer(msg.value);
  }
  ensures _to != msg.sender && _to != this -> net(_to) == \old(net(_to)) - msg.value && net(msg.sender) == \old(net(msg.sender)) + msg.value;
  ensures _to == msg.sender -> net(_to) == \old(net(_to));
  ensures _to == this -> net(_to) == \old(net(_to)) && net(msg.sender) == \old(net(msg.sender)) + msg.value;
  function sendViaSend(address _to) public payable {
    bool sent = _to.send(msg.value);
    require(sent);
  }
  ensures _to != msg.sender && _to != this -> net(_to) == \old(net(_to)) - msg.value && net(msg.sender) == \old(net(msg.sender)) + msg.value;
  ensures _to == msg.sender -> net(_to) == \old(net(_to));
  ensures _to == this -> net(_to) == \old(net(_to)) && net(msg.sender) == \old(net(msg.sender)) + msg.value;
  function sendViaCall(address _to) public payable {
    (bool sent, ) = _to.call{value: msg.value}("");
    require(sent);
  }
}

local instance : InContract := ⟨SendEther⟩
open scoped Scoped

theorem sendViaTransfer_refuted : ¬ (⊢ spec!{ sendViaTransfer }) := by
  sol_refute

theorem sendViaSend_refuted : ¬ (⊢ spec!{ sendViaSend }) := by
  sol_refute

theorem sendViaCall_refuted : ¬ (⊢ spec!{ sendViaCall }) := by
  sol_refute

end Solidity.Examples.Benchmark.SolkeyGames.SendEther
