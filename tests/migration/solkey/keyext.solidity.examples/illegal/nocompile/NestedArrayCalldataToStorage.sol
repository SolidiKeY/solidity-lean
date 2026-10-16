// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// solc: Copying nested calldata dynamic arrays to storage is not implemented in the old code generator.
///
/// Copying a nested dynamic array into storage is a deep copy solc's code generator does
/// not emit. The storage-to-storage form (`matrix = otherMatrix;` between two state variables)
/// is a deep copy and does compile; assigning to a *local* storage variable
/// (`uint[][] storage m = matrix;`) assigns a reference and copies nothing. See
/// https://docs.soliditylang.org/en/latest/types.html#data-location-and-assignment-behavior
contract NestedArrayCalldataToStorage {
    uint[][] matrix;

    function copyRows(uint[][] calldata rows) external {
        matrix = rows;
    }
}
