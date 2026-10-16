// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// OpenZeppelin's Ownable (https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/access/Ownable.sol),
// simplified to a concrete contract. Deviations, all forced by the supported fragment: the
// onlyOwner modifier, _checkOwner and _transferOwnership are inlined; events and custom errors
// are dropped; Context._msgSender() is msg.sender.
// Neither function has a requires on the caller: each ensures \old(_owner) == msg.sender proves
// that every call that does not revert was made by the owner.
contract Ownable {
    address private _owner;

    /// @custom:key skip
    constructor(address initialOwner) {
        if (initialOwner == address(0)) revert();
        _owner = initialOwner;
    }

    /// @custom:key skip
    function owner() public view returns (address) {
        return _owner;
    }

    /// @custom:key ensures \old(_owner) == msg.sender && _owner == address(0)
    function renounceOwnership() public {
        address o = _owner;
        if (o != msg.sender) revert();
        _owner = address(0);
    }

    /// @custom:key ensures \old(_owner) == msg.sender && _owner == newOwner && newOwner != address(0)
    function transferOwnership(address newOwner) public {
        address o = _owner;
        if (o != msg.sender) revert();
        if (newOwner == address(0)) revert();
        _owner = newOwner;
    }
}
