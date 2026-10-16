// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// solc: Array containing a (nested) mapping cannot be constructed in memory.
///
/// `new T[](n)` allocates in memory, which a mapping-carrying element type cannot inhabit.
contract MemoryArrayOfStructsWithMapping {
    struct Ledger { mapping(uint => uint) balances; }

    function construct() public pure {
        Ledger[] memory ls = new Ledger[](2);
    }
}
