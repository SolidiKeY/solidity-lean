// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// solc: Type mapping(uint256 => uint256) is only valid in storage because it contains a (nested) mapping.
///
/// A mapping exists only in storage; `memory` is not a data location it has.
contract MappingInMemory {
    mapping(uint => uint) balances;

    function toMemory() public view {
        mapping(uint => uint) memory m = balances;
    }
}
