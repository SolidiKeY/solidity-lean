// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// solc: Data location must be "memory" or "calldata" for return parameter in function, but "storage" was given.
///
/// A mapping cannot leave a function whose visibility forces a memory/calldata return.
contract MappingReturn {
    mapping(uint => uint) balances;

    function get() public view returns (mapping(uint => uint) storage) {
        return balances;
    }
}
