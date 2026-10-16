// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

// Course withdrawal-pattern OneAuction (SolidityCalculus/maltaCourseKey/auction-withdraw)
// in the supported fragment: instead of transferring refunds directly, makeBid and
// closeAuction credit withdrawableBalances and participants pull their funds via
// withdraw. Verified by the auction-withdraw-*.key problems against the course invariant
// over effective_net(a) := net(a) - withdrawableBalances[a]:
//   bid == effective_net(bidder) + effective_net(owner),
//   effective_net(owner) <= 0,
//   mode == Open -> effective_net(owner) == 0.
// Like the course, only makeBid and withdraw have proof obligations: closeAuction
// credits the owner without resetting bid, so the conservation clause does not survive
// it (the sum drops to 0 while bid keeps its value) - provably so, which is why the
// course ships no closeAuction .key either.
contract AuctionWithdrawNet {
    uint mode; // 0 NeverStarted, 1 Open, 2 Closed
    address payable owner;
    uint closingTime;
    address payable bidder;
    uint bid;
    uint timeNow;
    mapping(address => uint) withdrawableBalances;

    function makeBid() public payable {
        require(mode == 1);
        address own = owner;
        require(msg.sender != own);
        uint currentBid = bid;
        require(msg.value > currentBid);
        require(timeNow <= closingTime);
        address bdr = bidder;
        uint wb = withdrawableBalances[bdr];
        withdrawableBalances[bdr] = wb + currentBid;
        bid = msg.value;
        bidder = payable(msg.sender);
    }

    function closeAuction() public {
        require(mode == 1);
        address own = owner;
        address bdr = bidder;
        require(msg.sender == own || msg.sender == bdr);
        require(timeNow > closingTime);
        mode = 2;
        uint b = bid;
        uint wb = withdrawableBalances[own];
        withdrawableBalances[own] = wb + b;
    }

    function withdraw() public {
        uint tmp = withdrawableBalances[msg.sender];
        withdrawableBalances[msg.sender] = 0;
        payable(msg.sender).transfer(tmp);
    }
}
