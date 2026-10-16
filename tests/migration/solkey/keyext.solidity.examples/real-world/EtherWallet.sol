// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

// The Ether Wallet of Solidity by Example (https://solidity-by-example.org/app/ether-wallet/).
// Deviations, all forced by the supported fragment: the require message is dropped and the
// owner read is bound to a local; getBalance() (address(this).balance) is dropped.
// withdraw has no requires on the caller: its ensures proves that only the owner can withdraw.
contract EtherWallet {
    address payable public owner;

    /// @custom:key skip
    constructor() {
        owner = payable(msg.sender);
    }

    receive() external payable {}

    /// @custom:key requires _amount >= 0
    /// @custom:key ensures msg.sender == owner && owner == \old(owner)
    /// @custom:key ensures net(owner) == \old(net(owner)) - _amount
    function withdraw(uint256 _amount) external {
        address o = owner;
        require(msg.sender == o);
        payable(msg.sender).transfer(_amount);
    }
}
