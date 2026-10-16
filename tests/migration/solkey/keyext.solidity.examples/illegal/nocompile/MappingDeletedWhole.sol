// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// solc: Built-in unary operator delete cannot be applied to type mapping(uint256 => uint256).
///
/// A single entry may be deleted (`delete balances[1];`); the mapping as a whole may not.
contract MappingDeletedWhole {
    mapping(uint => uint) balances;

    function deleteWhole() public {
        delete balances;
    }
}
