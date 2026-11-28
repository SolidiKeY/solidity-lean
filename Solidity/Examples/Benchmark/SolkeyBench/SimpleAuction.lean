import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `SimpleAuction`

Source: <https://github.com/SolidiKeY/solkey/blob/50a1469c8c34abf522c7027e47e6f53292d6920a/keyext.solidity.examples/contracts/benchmark/SimpleAuction.sol>.

Changes beyond `contract!{ … }` spelling; the `@custom:key` clauses are written above their functions, invariants first. `payable(x)` is the identity on an address and is dropped (as in `Benchmark/EtherWallet.lean`); `if (c) s;` gets braces. `if (!payable(msg.sender).send(amount))` binds the result first (`bool sent = …; if (!sent)`), since a send is not an expression operand here. Related but distinct: `Benchmark/Governance/EnglishAuction.lean` ports the upstream Solidity docs text with `block.timestamp` and other clauses; this is solkey's variant (state `timeNow`, its own clauses).

Verdicts are on the declarations below: a `theorem` is proved, a `def …_obligation` is unknown (its stuck goal and the missing closer or rule in its docstring).
-/

namespace Solidity.Examples.Benchmark.SolkeyBench.SimpleAuction

def SimpleAuction : Contract := contract!{
  invariant highestBid >= 0;
  invariant \forall address a; pendingReturns[a] >= 0;
  address public beneficiary;
  uint public auctionEndTime;
  address public highestBidder;
  uint public highestBid;
  mapping(address => uint) pendingReturns;
  bool ended;
  uint timeNow;
  ensures beneficiary == beneficiaryAddress && auctionEndTime == timeNow + biddingTime;
  constructor(uint biddingTime, address beneficiaryAddress) {
    beneficiary = beneficiaryAddress;
    auctionEndTime = timeNow + biddingTime;
  }
  requires timeNow <= auctionEndTime && msg.value > highestBid;
  ensures highestBidder == msg.sender && highestBid == msg.value;
  ensures \old(highestBid) != 0 -> pendingReturns[\old(highestBidder)] == \old(pendingReturns[highestBidder]) + \old(highestBid);
  function bid() external payable {
    if (timeNow > auctionEndTime) { revert(); }
    if (msg.value <= highestBid) { revert(); }
    if (highestBid != 0) {
      address previousBidder = highestBidder;
      uint previousBid = highestBid;
      pendingReturns[previousBidder] += previousBid;
    }
    highestBidder = msg.sender;
    highestBid = msg.value;
  }
  ensures \result -> pendingReturns[msg.sender] == 0;
  ensures \result -> net(msg.sender) == \old(net(msg.sender)) - \old(pendingReturns[msg.sender]);
  ensures !\result -> pendingReturns[msg.sender] == \old(pendingReturns[msg.sender]);
  function withdraw() external returns (bool success) {
    uint amount = pendingReturns[msg.sender];
    if (amount > 0) {
      pendingReturns[msg.sender] = 0;
      bool sent = msg.sender.send(amount);
      if (!sent) {
        pendingReturns[msg.sender] = amount;
        return false;
      }
    }
    return true;
  }
  requires timeNow >= auctionEndTime && !ended && beneficiary != this;
  ensures ended && net(beneficiary) == \old(net(beneficiary)) - \old(highestBid);
  function auctionEnd() external {
    if (timeNow < auctionEndTime) { revert(); }
    if (ended) { revert(); }
    ended = true;
    beneficiary.transfer(highestBid);
  }
}

local instance : InContract := ⟨SimpleAuction⟩

open scoped Scoped

theorem spec_constructor : ⊢ spec!{ constructor } := by sol_prove
/-- Unknown: credit to \old(highestBidder) and new highest bid after payable snapshot and saves; mapping-frame and snapshot closure missing (cf. Escrow.withdraw). -/
def bid_obligation : Fml SimpleAuction [] := spec!{ bid }
/-- Unknown: on the success branch the cleared entry and net(msg.sender) after save then send (pay), on the failure branch the restored entry; mapping/snapshot closure and pay ledger rule missing. -/
def withdraw_obligation : Fml SimpleAuction [] := spec!{ withdraw }
/-- Unknown: net(beneficiary) after ended = true and pay(beneficiary, highestBid); calculus pay rule that books net for the payee is missing (pay(se,v) leaf stays open; cf. RefundEscrow.beneficiaryWithdraw). -/
def auctionEnd_obligation : Fml SimpleAuction [] := spec!{ auctionEnd }

end Solidity.Examples.Benchmark.SolkeyBench.SimpleAuction
