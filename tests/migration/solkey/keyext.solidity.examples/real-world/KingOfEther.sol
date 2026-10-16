// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

// Source: https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/hacks/denial-of-service/PreventDenialOfService.sol
// Changes: comments and require messages dropped; claimThrone binds the storage reads king and
// balance to locals before balances[king] += balance, which otherwise stalls (the right side of
// a compound assignment, and its mapping index, must not read storage).
/// @custom:key invariant balance >= 0
/// @custom:key invariant \forall address a; balances[a] >= 0
contract KingOfEther {
    address public king;
    uint256 public balance;
    mapping(address => uint256) public balances;

    /// @custom:key ensures msg.value > \old(balance) && king == msg.sender && balance == msg.value
    /// @custom:key ensures balances[\old(king)] == \old(balances[king]) + \old(balance)
    /// @custom:key ensures \forall address a; a != \old(king) -> balances[a] == \old(balances[a])
    /// @custom:key ensures net(msg.sender) == \old(net(msg.sender)) + msg.value
    function claimThrone() external payable {
        require(msg.value > balance);

        uint256 b = balance;
        address k = king;
        balances[k] += b;

        balance = msg.value;
        king = msg.sender;
    }

    /// @custom:key ensures msg.sender != king && king == \old(king) && balance == \old(balance)
    /// @custom:key ensures balances[msg.sender] == 0
    /// @custom:key ensures net(msg.sender) == \old(net(msg.sender)) - \old(balances[msg.sender])
    function withdraw() public {
        require(msg.sender != king);

        uint256 amount = balances[msg.sender];
        balances[msg.sender] = 0;

        (bool sent,) = msg.sender.call{value: amount}("");
        require(sent);
    }
}
