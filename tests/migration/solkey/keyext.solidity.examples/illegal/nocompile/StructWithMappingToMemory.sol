// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// solc: Type struct StructWithMappingToMemory.Ledger memory is only valid in storage because it contains a (nested) mapping.
///
/// A struct carrying a mapping has no memory representation.
contract StructWithMappingToMemory {
    struct Ledger { mapping(uint => uint) balances; }

    Ledger ledger;

    function toMemory() public view {
        Ledger memory l = ledger;
    }
}
