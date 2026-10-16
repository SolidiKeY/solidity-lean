// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Source: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v5.0.0/contracts/utils/ReentrancyGuard.sol
// and https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v5.0.0/contracts/mocks/ReentrancyMock.sol
// Changes: ReentrancyMock and ReentrancyGuard flattened into one contract; comments and the custom
// error dropped. nonReentrant inlines _nonReentrantBefore/_nonReentrantAfter, since a function call
// inside a modifier fails to load. countThisRecursive and countAndCall are dropped (abi.encodeCall,
// external calls on this and on another contract). A constant reads as an unconstrained storage
// field outside the constructor, so the invariant states the two constants' values.
/// @custom:key invariant NOT_ENTERED == 1 && ENTERED == 2
/// @custom:key invariant _status == 1 && counter >= 0
contract OZReentrancyGuard {
    uint256 private constant NOT_ENTERED = 1;
    uint256 private constant ENTERED = 2;

    uint256 private _status;
    uint256 public counter;

    constructor() {
        _status = NOT_ENTERED;
        counter = 0;
    }

    modifier nonReentrant() {
        if (_status == ENTERED) {
            revert();
        }
        _status = ENTERED;
        _;
        _status = NOT_ENTERED;
    }

    function _reentrancyGuardEntered() internal view returns (bool) {
        return _status == ENTERED;
    }

    /// @custom:key ensures counter == \old(counter) + 1
    function callback() external nonReentrant {
        _count();
    }

    /// @custom:key requires n >= 0
    /// @custom:key ensures n == 0 && counter == \old(counter)
    function countLocalRecursive(uint256 n) public nonReentrant {
        if (n > 0) {
            _count();
            countLocalRecursive(n - 1);
        }
    }

    function _count() private {
        counter += 1;
    }

    /// @custom:key ensures counter == \old(counter)
    function guardedCheckEntered() public nonReentrant {
        require(_reentrancyGuardEntered());
    }

    /// @custom:key ensures counter == \old(counter)
    function unguardedCheckNotEntered() public view {
        require(!_reentrancyGuardEntered());
    }
}
