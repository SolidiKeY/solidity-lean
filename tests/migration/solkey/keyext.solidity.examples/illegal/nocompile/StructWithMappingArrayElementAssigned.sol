// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// solc: Types in storage containing (nested) mappings cannot be assigned to.
///
/// An array element of a mapping-carrying struct type is the same case as the whole struct.
contract StructWithMappingArrayElementAssigned {
    struct Ledger { mapping(uint => uint) balances; }

    Ledger[] ledgers;

    function assign() public {
        ledgers[0] = ledgers[1];
    }
}
