// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

// solidiKeY escrow-v2 (solidity-contracts-examples/temp/escrow-v2.sol) with its specification
// carried in @custom:key natspec tags instead of the SoliditySpecCompiler's /*@ ... */ blocks.
// Deviations from the original, all forced by the supported fragment: the by/stateIs
// modifiers are inlined requires, `now` is the timeNow state variable, storage reads that
// the original placed inside a comparison or a compound expression are bound to a local
// first.
/// @custom:key invariant sender != receiver
/// @custom:key invariant amountInEscrow == net(sender) + net(receiver)
/// @custom:key invariant state != State.AwaitingDeposit || net(sender) == 0
/// @custom:key invariant state == State.DepositPlaced || amountInEscrow == 0
contract Escrow {
    enum State { AwaitingDeposit, DepositPlaced, Withdrawn }

    address public sender;
    address payable public receiver;
    uint public delayUntilRelease;
    uint public releaseTime;
    uint public amountInEscrow;
    bool public releasedBySender;
    bool public releasedByReceiver;
    State public state;
    uint timeNow;

    constructor(address _sender, address payable _receiver, uint _delayUntilRelease) {
        require(_sender != _receiver);
        sender = _sender;
        receiver = _receiver;
        delayUntilRelease = _delayUntilRelease;
        releasedBySender = false;
        releasedByReceiver = false;
        state = State.AwaitingDeposit;
    }

    /// @custom:key requires msg.sender == sender && state == State.AwaitingDeposit && msg.value > 0
    /// @custom:key ensures net(sender) == msg.value && state == State.DepositPlaced
    function placeInEscrow() public payable {
        require(state == State.AwaitingDeposit);
        address snd = sender;
        require(msg.sender == snd);
        require(msg.value > 0);
        amountInEscrow = msg.value;
        uint rt = timeNow + delayUntilRelease;
        releaseTime = rt;
        state = State.DepositPlaced;
    }

    /// @custom:key requires state == State.DepositPlaced
    /// @custom:key ensures msg.sender == sender -> releasedBySender == true
    /// @custom:key ensures msg.sender == receiver -> releasedByReceiver == true
    function releaseEscrow() public {
        require(state == State.DepositPlaced);
        address snd = sender;
        address rcv = receiver;
        if (msg.sender == snd) {
            releasedBySender = true;
        }
        if (msg.sender == rcv) {
            releasedByReceiver = true;
        }
    }

    /// @custom:key requires releasedByReceiver && releasedBySender && msg.sender == receiver && state == State.DepositPlaced
    /// @custom:key ensures net(receiver) == -net(sender) && state == State.Withdrawn
    function withdrawFromEscrow() public {
        address rcv = receiver;
        require(msg.sender == rcv);
        require(state == State.DepositPlaced);
        require(timeNow >= releaseTime);
        require(releasedByReceiver == true);
        require(releasedBySender == true);
        state = State.Withdrawn;
        receiver.transfer(amountInEscrow);
        amountInEscrow = 0;
    }
}
