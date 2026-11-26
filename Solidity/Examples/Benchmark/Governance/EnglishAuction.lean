import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Governance benchmark: EnglishAuction
Source: Solidity v0.8.26, SimpleAuction:
<https://github.com/ethereum/solidity/blob/v0.8.26/docs/examples/blind-auction.rst>.
The English-auction example's revert-with-error branches become require,
events are omitted. The refund uses send and restores the credit on failure,
as in the source; its result distinguishes a successful refund from failure.
Natural @custom:key clauses state highest bid, accumulated refunds, and payout.
The verdicts below concern this model only. Complete-original executable
modeling remains an obligation; no full-source verification credit is claimed.
Model verdicts: constructor proved; bid, withdraw, auctionEnd unknown (see obligations).
-/
namespace Solidity.Examples.Benchmark.Governance.EnglishAuction
def EnglishAuction : Contract := contract!{
  address public beneficiary;
  uint256 public auctionEndTime;
  address public highestBidder;
  uint256 public highestBid;
  mapping(address => uint256) public pendingReturns;
  bool public ended;
  ensures beneficiary == recipient && auctionEndTime == block.timestamp + biddingTime;
  constructor(uint256 biddingTime, address recipient) {
    beneficiary = recipient;
    auctionEndTime = block.timestamp + biddingTime;
  }
  ensures highestBid == msg.value && highestBidder == msg.sender && highestBid > \old(highestBid);
  ensures \old(highestBid) != 0 -> pendingReturns[\old(highestBidder)] == \old(pendingReturns[highestBidder]) + \old(highestBid);
  function bid() public payable {
    require(block.timestamp <= auctionEndTime);
    require(msg.value > highestBid);
    if (highestBid != 0) { pendingReturns[highestBidder] += highestBid; }
    highestBidder = msg.sender;
    highestBid = msg.value;
  }
  ensures \result -> pendingReturns[msg.sender] == 0;
  ensures !\result -> pendingReturns[msg.sender] == \old(pendingReturns[msg.sender]);
  ensures (\result && msg.sender != this) -> net(msg.sender) == \old(net(msg.sender)) - \old(pendingReturns[msg.sender]);
  function withdraw() public returns (bool) {
    uint256 amount = pendingReturns[msg.sender];
    if (amount > 0) {
      pendingReturns[msg.sender] = 0;
      bool sent = msg.sender.send(amount);
      if (!sent) { pendingReturns[msg.sender] = amount; return false; }
    }
    return true;
  }
  ensures block.timestamp >= auctionEndTime && !\old(ended) && ended;
  ensures beneficiary != this -> net(beneficiary) == \old(net(beneficiary)) - highestBid;
  function auctionEnd() public {
    require(block.timestamp >= auctionEndTime);
    require(!ended);
    ended = true;
    beneficiary.transfer(highestBid);
  }
}
local instance : InContract := ⟨EnglishAuction⟩
open scoped Scoped
/-- `@custom:key` obligation for `constructor`. -/
theorem spec_constructor : ⊢ spec!{ constructor } := by sol_prove
/-- Unknown: the old highest bidder indexes the refund map after both highest
fields change. Missing leaf closure for this snapshot-dependent mapping key. -/
def bid_obligation := spec!{ bid }
/-- Unknown: the send-success and zero-credit branches leave `pay`, `oldNet`
and the old mapping credit. Missing payment/snapshot leaf closure. -/
def withdraw_obligation := spec!{ withdraw }
/-- Unknown: the winning payment leaves a symbolic beneficiary, `pay` and
`oldNet`; the existing leaf closer does not finish that ledger equality. -/
def auctionEnd_obligation := spec!{ auctionEnd }
end Solidity.Examples.Benchmark.Governance.EnglishAuction
