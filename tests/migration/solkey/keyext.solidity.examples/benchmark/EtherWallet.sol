// Source: https://raw.githubusercontent.com/Cyfrin/solidity-by-example.github.io/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/app/ether-wallet/EtherWallet.sol
// Changes: the require message is dropped (string literal); getBalance() is dropped
// (address(this).balance crashes the parser).
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

contract EtherWallet {
    address payable public owner;

    /// @custom:key ensures owner == msg.sender
    constructor() {
        owner = payable(msg.sender);
    }

    receive() external payable {}

    /// @custom:key requires _amount >= 0
    /// @custom:key ensures msg.sender == owner && owner == \old(owner)
    /// @custom:key ensures net(owner) == \old(net(owner)) - _amount
    function withdraw(uint256 _amount) external {
        require(msg.sender == owner);
        payable(msg.sender).transfer(_amount);
    }
}
