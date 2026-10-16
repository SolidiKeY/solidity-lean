// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

// Source: https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/array/ArrayRemoveByShifting.sol
// Changes: comments and the require message dropped; test is in ../ArrayRemoveByShifting.sol.
// Open: the loop invariant can state neither the shifted prefix nor the unchanged length,
// since it cannot refer to the pre-state (\old is rejected there), and the loop rule
// anonymises all of storage, so the ensures clauses are lost across the loop.
contract ArrayRemoveByShifting {
    uint256[] public arr;

    /// @custom:key requires _index >= 0
    /// @custom:key ensures arr.length == \old(arr.length) - 1
    /// @custom:key ensures \forall uint j; 0 <= j && j < _index -> arr[j] == \old(arr[j])
    /// @custom:key ensures \forall uint j; _index <= j && j < arr.length -> arr[j] == \old(arr[j + 1])
    function remove(uint256 _index) public {
        require(_index < arr.length);

        /// @custom:key invariant i + 1 <= arr.length
        for (uint256 i = _index; i < arr.length - 1; i++) {
            arr[i] = arr[i + 1];
        }
        arr.pop();
    }
}
