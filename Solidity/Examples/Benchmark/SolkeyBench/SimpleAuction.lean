import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `SimpleAuction`

Source: <https://github.com/SolidiKeY/solkey/blob/50a1469c8c34abf522c7027e47e6f53292d6920a/keyext.solidity.examples/contracts/benchmark/SimpleAuction.sol>.
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
    if (timeNow > auctionEndTime) revert();
    if (msg.value <= highestBid) revert();
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
      if (!msg.sender.send(amount)) {
        pendingReturns[msg.sender] = amount;
        return false;
      }
    }
    return true;
  }
  requires timeNow >= auctionEndTime && !ended && beneficiary != this;
  ensures ended && net(beneficiary) == \old(net(beneficiary)) - \old(highestBid);
  function auctionEnd() external {
    if (timeNow < auctionEndTime) revert();
    if (ended) revert();
    ended = true;
    beneficiary.transfer(highestBid);
  }
}

local instance : InContract := ⟨SimpleAuction⟩

open scoped Scoped

theorem spec_constructor : ⊢ spec!{ constructor } := by sol_prove
theorem spec_bid : ⊢ spec!{ bid } := by sol_prove
theorem spec_withdraw : ⊢ spec!{ withdraw } := by sol_prove
theorem spec_auctionEnd : ⊢ spec!{ auctionEnd } := by sol_prove

end Solidity.Examples.Benchmark.SolkeyBench.SimpleAuction
