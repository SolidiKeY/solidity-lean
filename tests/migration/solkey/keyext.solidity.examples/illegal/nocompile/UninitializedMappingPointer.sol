// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// solc: Uninitialized mapping. Mappings cannot be created dynamically, you have to assign them from a state variable.
///
/// A storage pointer to a mapping must be bound to a state variable at its declaration.
contract UninitializedMappingPointer {
    function declare() public pure {
        mapping(uint => uint) storage p;
    }
}
