// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

// Source: https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/array/ArrayRemoveByShifting.sol
// Changes: comments and the require message dropped; the loop gets an invariant; the array
// literal assignments arr = [1, 2, 3, 4, 5] and arr = [1] do not load, so test clears arr with
// delete and pushes the values. A loop invariant cannot refer to the pre-state, so remove only
// proves the bounds check; test proves the shifting on concrete data, and the full functional
// specification of remove is in open/ArrayRemoveByShifting.sol.
contract ArrayRemoveByShifting {
    uint256[] public arr;

    /// @custom:key requires _index >= 0
    /// @custom:key ensures _index < \old(arr.length)
    function remove(uint256 _index) public {
        require(_index < arr.length);

        /// @custom:key invariant i + 1 <= arr.length
        for (uint256 i = _index; i < arr.length - 1; i++) {
            arr[i] = arr[i + 1];
        }
        arr.pop();
    }

    function test() external {
        delete arr;
        arr.push(1);
        arr.push(2);
        arr.push(3);
        arr.push(4);
        arr.push(5);
        remove(2);
        assert(arr[0] == 1);
        assert(arr[1] == 2);
        assert(arr[2] == 4);
        assert(arr[3] == 5);
        assert(arr.length == 4);

        delete arr;
        arr.push(1);
        remove(0);
        assert(arr.length == 0);
    }
}
