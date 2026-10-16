// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// solc: Types in storage containing (nested) mappings cannot be assigned to.
///
/// A mapping cannot be copied, so it cannot be the target of an assignment.
contract MappingAssignedWhole {
    mapping(uint => uint) balances;
    mapping(uint => uint) valuesMap;

    function assign() public {
        balances = valuesMap;
    }
}
