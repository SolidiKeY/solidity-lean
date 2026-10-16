// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// solc: Types in storage containing (nested) mappings cannot be assigned to.
///
/// Copying a struct that carries a mapping is not assignment solc will perform.
/// Rebinding a local storage pointer is a different statement and stays legal:
/// `Ledger storage l = ledger; l = ledger2;` compiles.
contract StructWithMappingAssigned {
    struct Ledger { mapping(uint => uint) balances; }

    Ledger ledger;
    Ledger ledger2;

    function assign() public {
        ledger = ledger2;
    }
}
