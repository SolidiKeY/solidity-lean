// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

contract ArrayScans {
    /// @custom:key box
    function unsignedScan(uint8[] memory xs) public pure {
        uint i = 0;
        /// @custom:key invariant i <= xs.length
        while (i < xs.length) {
            assert(xs[i] <= 255);
            i++;
        }
    }

    function signedScan(int8[] memory xs) public pure {
        uint i = 0;
        /// @custom:key invariant i <= xs.length
        /// @custom:key decreases xs.length - i
        while (i < xs.length) {
            assert(xs[i] >= -128);
            assert(xs[i] <= 127);
            i++;
        }
    }
    /// @custom:key box
    function signedUpperScan(int8[] memory xs) public pure {
        uint i = 0;
        /// @custom:key invariant i <= xs.length
        while (i < xs.length) {
            assert(xs[i] <= 127);
            i++;
        }
    }
}
