// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Source: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v5.0.0/contracts/access/Ownable2Step.sol
// and https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v5.0.0/contracts/access/Ownable.sol
// Changes: Ownable2Step, Ownable and Context flattened into one contract (super.f() fails to load),
// so Ownable's transferOwnership is replaced by its override and _transferOwnership merges both
// bodies; comments, events and custom errors dropped (a bare revert() instead). onlyOwner inlines
// _checkOwner and reads _owner instead of calling owner(), since a call inside a modifier fails to
// load; returns are named. No function has a requires on the caller: each ensures proves that
// every call that does not revert was made by the owner (or the pending owner).
contract OZOwnable2Step {
    address private _owner;
    address private _pendingOwner;

    /// @custom:key ensures initialOwner != address(0) && _owner == initialOwner && _pendingOwner == address(0)
    constructor(address initialOwner) {
        if (initialOwner == address(0)) {
            revert();
        }
        _transferOwnership(initialOwner);
    }

    modifier onlyOwner() {
        if (_owner != msg.sender) {
            revert();
        }
        _;
    }

    /// @custom:key ensures o == _owner && _owner == \old(_owner)
    function owner() public view virtual returns (address o) {
        return _owner;
    }

    function _checkOwner() internal view virtual {
        if (owner() != msg.sender) {
            revert();
        }
    }

    /// @custom:key ensures \old(_owner) == msg.sender && _owner == address(0) && _pendingOwner == address(0)
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /// @custom:key ensures p == _pendingOwner && _pendingOwner == \old(_pendingOwner)
    function pendingOwner() public view virtual returns (address p) {
        return _pendingOwner;
    }

    /// @custom:key ensures \old(_owner) == msg.sender && _owner == \old(_owner) && _pendingOwner == newOwner
    function transferOwnership(address newOwner) public virtual onlyOwner {
        _pendingOwner = newOwner;
    }

    function _transferOwnership(address newOwner) internal virtual {
        delete _pendingOwner;
        _owner = newOwner;
    }

    /// @custom:key ensures \old(_pendingOwner) == msg.sender && _owner == msg.sender && _pendingOwner == address(0)
    function acceptOwnership() public virtual {
        address sender = msg.sender;
        if (pendingOwner() != sender) {
            revert();
        }
        _transferOwnership(sender);
    }
}
