// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.4;

// "Safe Remote Purchase" from the Solidity documentation, Solidity by Example
// (https://docs.soliditylang.org/en/latest/solidity-by-example.html#safe-remote-purchase).
// Deviations, all forced by the supported fragment: the onlyBuyer/onlySeller/inState/condition
// modifiers are inlined as the same checks; events and custom errors are dropped; storage reads
// inside a comparison or a product are bound to locals first; abort pays out 2 * value instead of
// address(this).balance, which is the same amount unless ether was forced into the contract.
// The invariant books every state against the ledger: the contract holds 2 * value while
// Created, 4 * value while Locked, 3 * value while Release, and nothing once Inactive.
// confirmPurchase assumes a fresh buyer (not the seller, nothing paid in before), which the
// original does not enforce.
/// @custom:key invariant value >= 0 && seller != buyer
/// @custom:key invariant state == State.Created -> net(seller) == 2 * value && net(buyer) == 0
/// @custom:key invariant state == State.Locked -> net(seller) == 2 * value && net(buyer) == 2 * value
/// @custom:key invariant state == State.Release -> net(seller) == 2 * value && net(buyer) == value
/// @custom:key invariant state == State.Inactive -> net(seller) + net(buyer) == 0
contract Purchase {
    uint public value;
    address payable public seller;
    address payable public buyer;

    enum State { Created, Locked, Release, Inactive }
    State public state;

    /// @custom:key skip
    constructor() payable {
        seller = payable(msg.sender);
        value = msg.value / 2;
        uint doubled = 2 * value;
        if (doubled != msg.value) revert();
    }

    /// @custom:key requires msg.sender == seller && state == State.Created
    /// @custom:key ensures state == State.Inactive && net(seller) == 0
    function abort() external {
        address s = seller;
        if (msg.sender != s) revert();
        if (state != State.Created) revert();
        state = State.Inactive;
        uint deposit = 2 * value;
        seller.transfer(deposit);
    }

    /// @custom:key requires state == State.Created && msg.value == 2 * value
    /// @custom:key requires msg.sender != seller && net(msg.sender) == 0
    /// @custom:key ensures state == State.Locked && buyer == msg.sender
    function confirmPurchase() external payable {
        if (state != State.Created) revert();
        uint price = 2 * value;
        require(msg.value == price);
        buyer = payable(msg.sender);
        state = State.Locked;
    }

    /// @custom:key requires msg.sender == buyer && state == State.Locked
    /// @custom:key ensures state == State.Release && net(buyer) == value
    function confirmReceived() external {
        address b = buyer;
        if (msg.sender != b) revert();
        if (state != State.Locked) revert();
        state = State.Release;
        buyer.transfer(value);
    }

    /// @custom:key requires msg.sender == seller && state == State.Release
    /// @custom:key ensures state == State.Inactive && net(seller) == -value && net(buyer) == value
    function refundSeller() external {
        address s = seller;
        if (msg.sender != s) revert();
        if (state != State.Release) revert();
        state = State.Inactive;
        uint refund = 3 * value;
        seller.transfer(refund);
    }
}
