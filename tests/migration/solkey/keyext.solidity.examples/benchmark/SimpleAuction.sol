// Source: https://raw.githubusercontent.com/ethereum/solidity/v0.8.30/docs/examples/blind-auction.rst
// Changes: events and custom errors are dropped (`revert Err()` becomes `revert()`),
// emits are dropped; block.timestamp is the timeNow state variable; bid binds the outbid
// bidder and bid to locals; withdraw's `returns (bool)` becomes `returns (bool success)`.
// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.4;
/// @custom:key invariant highestBid >= 0
/// @custom:key invariant \forall address a; pendingReturns[a] >= 0
contract SimpleAuction {
    // Parameters of the auction. Times are either
    // absolute unix timestamps (seconds since 1970-01-01)
    // or time periods in seconds.
    address payable public beneficiary;
    uint public auctionEndTime;

    // Current state of the auction.
    address public highestBidder;
    uint public highestBid;

    // Allowed withdrawals of previous bids
    mapping(address => uint) pendingReturns;

    // Set to true at the end, disallows any change.
    // By default initialized to `false`.
    bool ended;
    uint timeNow;

    // Events that will be emitted on changes.

    // Errors that describe failures.

    // The triple-slash comments are so-called natspec
    // comments. They will be shown when the user
    // is asked to confirm a transaction or
    // when an error is displayed.

    /// The auction has already ended.
    /// There is already a higher or equal bid.
    /// The auction has not ended yet.
    /// The function auctionEnd has already been called.

    /// Create a simple auction with `biddingTime`
    /// seconds bidding time on behalf of the
    /// beneficiary address `beneficiaryAddress`.
    /// @custom:key ensures beneficiary == beneficiaryAddress && auctionEndTime == timeNow + biddingTime
    constructor(
        uint biddingTime,
        address payable beneficiaryAddress
    ) {
        beneficiary = beneficiaryAddress;
        auctionEndTime = timeNow + biddingTime;
    }

    /// Bid on the auction with the value sent
    /// together with this transaction.
    /// The value will only be refunded if the
    /// auction is not won.
    /// @custom:key requires timeNow <= auctionEndTime && msg.value > highestBid
    /// @custom:key ensures highestBidder == msg.sender && highestBid == msg.value
    /// @custom:key ensures \old(highestBid) != 0 -> pendingReturns[\old(highestBidder)] == \old(pendingReturns[highestBidder]) + \old(highestBid)
    function bid() external payable {
        // No arguments are necessary, all
        // information is already part of
        // the transaction. The keyword payable
        // is required for the function to
        // be able to receive Ether.

        // Revert the call if the bidding
        // period is over.
        if (timeNow > auctionEndTime)
            revert();

        // If the bid is not higher, send the
        // Ether back (the revert statement
        // will revert all changes in this
        // function execution including
        // it having received the Ether).
        if (msg.value <= highestBid)
            revert();

        if (highestBid != 0) {
            // Sending back the Ether by simply using
            // highestBidder.send(highestBid) is a security risk
            // because it could execute an untrusted contract.
            // It is always safer to let the recipients
            // withdraw their Ether themselves.
            address previousBidder = highestBidder;
            uint previousBid = highestBid;
            pendingReturns[previousBidder] += previousBid;
        }
        highestBidder = msg.sender;
        highestBid = msg.value;
    }

    /// Withdraw a bid that was overbid.
    /// @custom:key ensures \result -> pendingReturns[msg.sender] == 0
    /// @custom:key ensures \result -> net(msg.sender) == \old(net(msg.sender)) - \old(pendingReturns[msg.sender])
    /// @custom:key ensures !\result -> pendingReturns[msg.sender] == \old(pendingReturns[msg.sender])
    function withdraw() external returns (bool success) {
        uint amount = pendingReturns[msg.sender];
        if (amount > 0) {
            // It is important to set this to zero because the recipient
            // can call this function again as part of the receiving call
            // before `send` returns.
            pendingReturns[msg.sender] = 0;

            // msg.sender is not of type `address payable` and must be
            // explicitly converted using `payable(msg.sender)` in order
            // use the member function `send()`.
            if (!payable(msg.sender).send(amount)) {
                // No need to call throw here, just reset the amount owing
                pendingReturns[msg.sender] = amount;
                return false;
            }
        }
        return true;
    }

    /// End the auction and send the highest bid
    /// to the beneficiary.
    /// @custom:key requires timeNow >= auctionEndTime && !ended && beneficiary != address(this)
    /// @custom:key ensures ended && net(beneficiary) == \old(net(beneficiary)) - \old(highestBid)
    function auctionEnd() external {
        // It is a good guideline to structure functions that interact
        // with other contracts (i.e. they call functions or send Ether)
        // into three phases:
        // 1. checking conditions
        // 2. performing actions (potentially changing conditions)
        // 3. interacting with other contracts
        // If these phases are mixed up, the other contract could call
        // back into the current contract and modify the state or cause
        // effects (ether payout) to be performed multiple times.
        // If functions called internally include interaction with external
        // contracts, they also have to be considered interaction with
        // external contracts.

        // 1. Conditions
        if (timeNow < auctionEndTime)
            revert();
        if (ended)
            revert();

        // 2. Effects
        ended = true;

        // 3. Interaction
        beneficiary.transfer(highestBid);
    }
}
