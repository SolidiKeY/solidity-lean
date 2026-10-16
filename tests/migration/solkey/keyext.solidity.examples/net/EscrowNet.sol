// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

// Course escrow-v2 (SolidityCalculus/maltaCourseKey/escrow) in the supported fragment:
// the State enum is a uint (0 AwaitingDeposit, 1 DepositPlaced, 2 Withdrawn), modifiers
// are inlined requires, `now` is the timeNow state variable. Verified per function by the
// escrow-*.key problems beside this file against the course invariant
//   sender != receiver,
//   amountInEscrow == net(sender) + net(receiver),
//   state == AwaitingDeposit -> net(sender) == 0,
//   state != DepositPlaced   -> amountInEscrow == 0.
contract EscrowNet {
    address sender;
    address payable receiver;
    uint delayUntilRelease;
    uint releaseTime;
    uint amountInEscrow;
    bool releasedBySender;
    bool releasedByReceiver;
    uint state; // 0 AwaitingDeposit, 1 DepositPlaced, 2 Withdrawn
    uint timeNow;

    function placeInEscrow() public payable {
        address snd = sender;
        require(msg.sender == snd);
        require(state == 0);
        require(msg.value > 0);
        amountInEscrow = msg.value;
        uint rt = timeNow + delayUntilRelease;
        releaseTime = rt;
        state = 1;
    }

    function releaseEscrow() public {
        require(state == 1);
        address snd = sender;
        address rcv = receiver;
        if (msg.sender == snd) {
            releasedBySender = true;
        }
        if (msg.sender == rcv) {
            releasedByReceiver = true;
        }
    }

    function withdrawFromEscrow() public {
        address rcv = receiver;
        require(msg.sender == rcv);
        require(state == 1);
        require(timeNow >= releaseTime);
        require(releasedByReceiver);
        require(releasedBySender);
        state = 2;
        receiver.transfer(amountInEscrow);
        amountInEscrow = 0;
    }
}
