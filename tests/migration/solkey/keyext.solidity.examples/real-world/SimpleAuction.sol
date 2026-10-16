// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.4;

// "Simple Open Auction" from the Solidity documentation, Solidity by Example
// (https://docs.soliditylang.org/en/latest/solidity-by-example.html#simple-open-auction).
// Deviations, all forced by the supported fragment: block.timestamp is the timeNow state
// variable; events and custom errors are dropped (`revert Err()` becomes `revert()`); the
// storage reads of bid's refund are bound to locals first; withdraw pays with transfer instead
// of send (send has no rule yet), so a failed payment reverts rather than returning false and
// the function returns nothing.
/// @custom:key invariant highestBid >= 0
/// @custom:key invariant \forall address a; pendingReturns[a] >= 0
/// @custom:key invariant beneficiary != address(this)
contract SimpleAuction {
    address payable public beneficiary;
    uint public auctionEndTime;
    address public highestBidder;
    uint public highestBid;
    mapping(address => uint) pendingReturns;
    bool ended;
    uint timeNow;

    /// @custom:key skip
    constructor(uint biddingTime, address payable beneficiaryAddress) {
        beneficiary = beneficiaryAddress;
        auctionEndTime = timeNow + biddingTime;
    }

    /// @custom:key requires timeNow <= auctionEndTime && msg.value > highestBid
    /// @custom:key ensures highestBidder == msg.sender && highestBid == msg.value
    /// @custom:key ensures \old(highestBid) != 0 -> pendingReturns[\old(highestBidder)] == \old(pendingReturns[highestBidder]) + \old(highestBid)
    function bid() external payable {
        if (timeNow > auctionEndTime) revert();
        if (msg.value <= highestBid) revert();
        uint previousBid = highestBid;
        if (previousBid != 0) {
            address previousBidder = highestBidder;
            pendingReturns[previousBidder] += previousBid;
        }
        highestBidder = msg.sender;
        highestBid = msg.value;
    }

    /// @custom:key ensures pendingReturns[msg.sender] == 0
    /// @custom:key ensures net(msg.sender) == \old(net(msg.sender)) - \old(pendingReturns[msg.sender])
    function withdraw() external {
        uint amount = pendingReturns[msg.sender];
        if (amount > 0) {
            pendingReturns[msg.sender] = 0;
            payable(msg.sender).transfer(amount);
        }
    }

    /// @custom:key requires timeNow >= auctionEndTime && !ended
    /// @custom:key ensures ended && net(beneficiary) == \old(net(beneficiary)) - \old(highestBid)
    function auctionEnd() external {
        if (timeNow < auctionEndTime) revert();
        if (ended) revert();
        ended = true;
        beneficiary.transfer(highestBid);
    }
}
