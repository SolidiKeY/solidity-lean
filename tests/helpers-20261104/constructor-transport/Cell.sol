// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.34;
contract Cell {
    uint256 saved = 7;
    uint256 captured;
    constructor(uint256 n) { uint256 old = saved; saved = n; captured = old; }
}
