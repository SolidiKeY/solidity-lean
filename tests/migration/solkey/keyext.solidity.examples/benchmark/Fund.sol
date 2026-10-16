// Source: https://raw.githubusercontent.com/ethereum/solidity/v0.8.30/docs/security-considerations.rst
// Changes: none (the third `Fund`, the one that zeroes the share before the transfer).
// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.6.0 <0.9.0;

/// @custom:key invariant \forall address a; shares[a] >= 0
contract Fund {
    /// @dev Mapping of ether shares of the contract.
    mapping(address => uint) shares;
    /// Withdraw your share.
    /// @custom:key ensures shares[msg.sender] == 0
    /// @custom:key ensures net(msg.sender) == \old(net(msg.sender)) - \old(shares[msg.sender])
    /// @custom:key ensures \forall address a; a != msg.sender -> shares[a] == \old(shares[a])
    function withdraw() public {
        uint share = shares[msg.sender];
        shares[msg.sender] = 0;
        payable(msg.sender).transfer(share);
    }
}
