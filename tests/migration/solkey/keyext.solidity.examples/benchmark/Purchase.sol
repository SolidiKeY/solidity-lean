// Source: https://raw.githubusercontent.com/ethereum/solidity/v0.8.30/docs/examples/safe-remote.rst
// Changes: events and custom errors are dropped (`revert Err()` becomes `revert()`),
// emits are dropped; abort pays 2 * value instead of address(this).balance (the same amount
// under the invariant, unless ether was forced in). The modifiers are kept.
// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.4;
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
    // The state variable has a default value of the first member, `State.created`
    State public state;

    modifier condition(bool condition_) {
        require(condition_);
        _;
    }

    /// Only the buyer can call this function.
    /// Only the seller can call this function.
    /// The function cannot be called at the current state.
    /// The provided value has to be even.

    modifier onlyBuyer() {
        if (msg.sender != buyer)
            revert();
        _;
    }

    modifier onlySeller() {
        if (msg.sender != seller)
            revert();
        _;
    }

    modifier inState(State state_) {
        if (state != state_)
            revert();
        _;
    }


    // Ensure that `msg.value` is an even number.
    // Division will truncate if it is an odd number.
    // Check via multiplication that it wasn't an odd number.
    /// @custom:key requires msg.sender != address(0)
    /// @custom:key ensures seller == msg.sender && 2 * value == msg.value && state == State.Created
    constructor() payable {
        seller = payable(msg.sender);
        value = msg.value / 2;
        if ((2 * value) != msg.value)
            revert();
    }

    /// Abort the purchase and reclaim the ether.
    /// Can only be called by the seller before
    /// the contract is locked.
    /// @custom:key requires msg.sender == seller && state == State.Created
    /// @custom:key ensures state == State.Inactive && net(seller) == 0
    function abort()
        external
        onlySeller
        inState(State.Created)
    {
        state = State.Inactive;
        // We use transfer here directly. It is
        // reentrancy-safe, because it is the
        // last call in this function and we
        // already changed the state.
        seller.transfer(2 * value);
    }

    /// Confirm the purchase as buyer.
    /// Transaction has to include `2 * value` ether.
    /// The ether will be locked until confirmReceived
    /// is called.
    /// @custom:key requires state == State.Created && msg.value == 2 * value
    /// @custom:key requires msg.sender != seller && net(msg.sender) == 0
    /// @custom:key ensures state == State.Locked && buyer == msg.sender
    function confirmPurchase()
        external
        inState(State.Created)
        condition(msg.value == (2 * value))
        payable
    {
        buyer = payable(msg.sender);
        state = State.Locked;
    }

    /// Confirm that you (the buyer) received the item.
    /// This will release the locked ether.
    /// @custom:key requires msg.sender == buyer && state == State.Locked
    /// @custom:key ensures state == State.Release && net(buyer) == value
    function confirmReceived()
        external
        onlyBuyer
        inState(State.Locked)
    {
        // It is important to change the state first because
        // otherwise, the contracts called using `send` below
        // can call in again here.
        state = State.Release;

        buyer.transfer(value);
    }

    /// This function refunds the seller, i.e.
    /// pays back the locked funds of the seller.
    /// @custom:key requires msg.sender == seller && state == State.Release
    /// @custom:key ensures state == State.Inactive && net(seller) == -value && net(buyer) == value
    function refundSeller()
        external
        onlySeller
        inState(State.Release)
    {
        // It is important to change the state first because
        // otherwise, the contracts called using `send` below
        // can call in again here.
        state = State.Inactive;

        seller.transfer(3 * value);
    }
}
