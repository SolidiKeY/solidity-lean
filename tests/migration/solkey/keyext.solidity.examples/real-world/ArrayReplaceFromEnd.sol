// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

// Source: https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/array/ArrayReplaceFromEnd.sol
// Changes: comments dropped; the array literal assignment arr = [1, 2, 3, 4] does not load, so
// test clears arr with delete and pushes the four values.
contract ArrayReplaceFromEnd {
    uint256[] public arr;

    /// @custom:key ensures arr.length == \old(arr.length) - 1
    /// @custom:key ensures index < arr.length -> arr[index] == \old(arr[arr.length - 1])
    /// @custom:key ensures \forall uint i; 0 <= i && i < arr.length && i != index -> arr[i] == \old(arr[i])
    function remove(uint256 index) public {
        arr[index] = arr[arr.length - 1];
        arr.pop();
    }

    function test() public {
        delete arr;
        arr.push(1);
        arr.push(2);
        arr.push(3);
        arr.push(4);

        remove(1);
        assert(arr.length == 3);
        assert(arr[0] == 1);
        assert(arr[1] == 4);
        assert(arr[2] == 3);

        remove(2);
        assert(arr.length == 2);
        assert(arr[0] == 1);
        assert(arr[1] == 4);
    }
}
