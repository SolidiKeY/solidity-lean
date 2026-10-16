// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// solc: Types in storage containing (nested) mappings cannot be assigned to.
///
/// A row of a nested mapping is itself a mapping, so copying one row onto another is the same case.
contract NestedMappingRowAssigned {
    mapping(uint => mapping(uint => uint)) grid;

    function assign() public {
        grid[1] = grid[2];
    }
}
