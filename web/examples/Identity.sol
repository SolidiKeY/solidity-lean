// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

contract Identity {
    /// @custom:key ensures \result == value
    function identity(uint256 value) public pure returns (uint256 result) {
        return value;
    }

    function caller() public pure returns (uint256) {
        return identity(1);
    }
}
