// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

// Source: https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/hacks/self-destruct/PreventForceEther.sol
// Changes: comments and require messages dropped. The specification language has no ether
// units, so the deposit clause writes 1 ether as 1000000000000000000.
/// @custom:key invariant balance >= 0 && balance <= TARGET_AMOUNT
contract EtherGame {
    uint256 public constant TARGET_AMOUNT = 7 ether;
    uint256 public balance;
    address public winner;

    /// @custom:key ensures msg.value == 1000000000000000000 && balance == \old(balance) + msg.value
    /// @custom:key ensures balance == TARGET_AMOUNT -> winner == msg.sender
    /// @custom:key ensures balance < TARGET_AMOUNT -> winner == \old(winner)
    function deposit() public payable {
        require(msg.value == 1 ether);

        balance += msg.value;
        require(balance <= TARGET_AMOUNT);

        if (balance == TARGET_AMOUNT) {
            winner = msg.sender;
        }
    }

    /// @custom:key ensures msg.sender == winner && winner == \old(winner) && balance == 0
    /// @custom:key ensures net(msg.sender) == \old(net(msg.sender)) - \old(balance)
    function claimReward() public {
        require(msg.sender == winner);
        uint256 amount = balance;
        balance = 0;
        (bool sent,) = msg.sender.call{value: amount}("");
        require(sent);
    }
}
