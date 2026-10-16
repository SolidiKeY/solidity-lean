// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// solc: Data location must be "memory" or "calldata" for parameter in function, but "storage" was given.
///
/// A mapping parameter is legal only for an `internal`/`private` function or a library.
contract MappingParameter {
    function withMapping(mapping(uint => uint) storage m) public {
        m[1] = 2;
    }
}
