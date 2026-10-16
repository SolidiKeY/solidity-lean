// Source: https://raw.githubusercontent.com/ethereum/solidity/v0.8.30/docs/introduction-to-smart-contracts.rst
// Unmodified; only @custom:key clauses are added.
// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.4.16 <0.9.0;

contract SimpleStorage {
    uint storedData;

    /// @custom:key requires x >= 0
    /// @custom:key ensures storedData == x
    function set(uint x) public {
        storedData = x;
    }

    function get() public view returns (uint) {
        return storedData;
    }
}
