// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// @custom:key invariant \exists address hb; \forall address a; balances[hb] >= balances[a] && (a != hb && a != auctionOwner -> balances[a] == net(a)) && (state == State.AUCTION_OPEN -> net(auctionOwner) == 0) && balances[hb] == net(hb) + net(auctionOwner)
/// @custom:key invariant state == State.AUCTION_OPEN -> \forall address a; (net(a) > 0 -> bidded[a] == true) && ((\exists uint i; i >= 0 && i < bidders.length && bidders[i] == a) <-> bidded[a] == true)
/// @custom:key invariant !(\exists uint i; i >= 0 && i < bidders.length && bidders[i] == auctionOwner)
/// @custom:key invariant balances[auctionOwner] == 0
/// @custom:key invariant auctionOwner != address(this)
contract MultiAuction {
    address payable private auctionOwner;
    mapping(address => uint) public balances;
    mapping(address => bool) bidded;
    address[] public bidders;

    enum State { AUCTION_OPEN, AUCTION_CLOSED }
    State private state;

    /// @custom:key skip
    constructor() {
        auctionOwner = payable(msg.sender);
        state = State.AUCTION_OPEN;
    }

    /// @custom:key requires state == State.AUCTION_OPEN && msg.sender != auctionOwner && msg.value > 0
    /// @custom:key ensures balances[msg.sender] == \old(balances[msg.sender]) + msg.value
    /// @custom:key assignable balances[msg.sender], bidders[bidders.length], bidders.length, bidded[msg.sender], net(msg.sender)
    function placeOrIncreaseBid() public payable {
        require(state == State.AUCTION_OPEN);
        address own = auctionOwner;
        require(msg.sender != own);
        require(msg.value > 0);
        uint b = balances[msg.sender];
        balances[msg.sender] = b + msg.value;
        bool bid = bidded[msg.sender];
        if (!bid) {
            bidders.push(msg.sender);
            bidded[msg.sender] = true;
        }
    }

    /// @custom:key requires state == State.AUCTION_OPEN
    /// @custom:key ensures net(msg.sender) == 0
    /// @custom:key assignable balances[msg.sender], net(msg.sender)
    function withdraw() public {
        require(state == State.AUCTION_OPEN);
        uint tmp = balances[msg.sender];
        balances[msg.sender] = 0;
        payable(msg.sender).transfer(tmp);
    }

    /// @custom:key requires 0 == 0
    /// @custom:key ensures 1 == 1
    /// @custom:key assignable net(msg.sender)
    function myTest() public {
    }

    /// @custom:key skip
    function closeAuction() public {
        address own = auctionOwner;
        require(msg.sender == own);
        require(state == State.AUCTION_OPEN);
        require(bidders.length > 0);
        state = State.AUCTION_CLOSED;
        uint i;
        address winner;
        uint highestBid = 0;
        for (i = 0; i < bidders.length; i = i + 1) {
            address candidate = bidders[i];
            uint candidateBid = balances[candidate];
            if (candidateBid > highestBid) {
                winner = candidate;
                highestBid = candidateBid;
            }
        }
        auctionOwner.transfer(highestBid);
        for (i = 0; i < bidders.length; i = i + 1) {
            address bidder = bidders[i];
            uint tmp = balances[bidder];
            if (bidder != winner && tmp != 0) {
                balances[bidder] = 0;
                payable(bidder).transfer(tmp);
            }
        }
    }
}
