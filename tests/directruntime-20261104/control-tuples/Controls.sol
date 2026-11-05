// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;
contract ControlTuples {
    function executeFirst() external pure returns (uint x) {
        /// @custom:key unwind 1
        do { x = x + 1; } while (false);
    }
    function whileZero() external pure returns (uint x) {
        while (false) { x = x + 1; }
    }
    function continueTest() external pure returns (uint x) {
        do { x = x + 1; continue; } while (x < 2);
    }
    function breakTest() external pure returns (uint x) {
        do { x = x + 1; break; } while (true);
    }
    function earlyReturn() external pure returns (uint) {
        do { return 7; } while (true);
    }
    function swap(uint a, uint b) external pure returns (uint, uint) {
        (a, b) = (b, a); return (a, b);
    }
    function declaration() external pure returns (uint, bool) {
        (uint a, , bool b) = (3, 4, true); return (a, b);
    }
    function skipped(uint a) external pure returns (uint) {
        (, a) = (9, 5); return a;
    }
    function repeated(uint a) external pure returns (uint) {
        (a, a) = (1, 2); return a;
    }
    function aliased(uint i) external pure returns (uint) {
        uint[2] memory a; (a[i], a[i]) = (1, 2); return a[i];
    }
    function sideEffect(uint a) external pure returns (uint, uint) {
        (a, ) = (a + 1, a++); return (a, a);
    }
    function inlineArray() external pure returns (uint) {
        uint8[2] memory a = [uint8(1), 2]; return a[0];
    }
    function internalPair() internal pure returns (uint, uint) { return (1, 2); }
    function callTuple() external pure returns (uint, uint) {
        (uint a, uint b) = internalPair(); return (a, b);
    }
}
