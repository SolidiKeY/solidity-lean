// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

// Compiler-mode fixture; the corresponding inhabited typed source/machine
// simulations are in Evm/MemoryLoopSourceExamples and MemoryLoopAllocExamples.
contract MemoryCompilerLoops {
    struct Record { uint n; int signed; }

    function arrays() public pure returns (uint) {
        uint[] memory xs = new uint[](2);
        uint[] memory same = xs;
        uint i = 0;
        while (i < xs.length) { xs[i] = i + 3; i++; }
        return same[1];
    }

    function records() public pure returns (uint) {
        Record memory r = Record(0, 5);
        Record memory same = r;
        while (r.n < 3) { r.n++; r.signed -= 2; }
        require(same.signed == -1);
        return same.n;
    }

    function allocateTurn() public pure returns (uint) {
        uint i = 2;
        while (i > 0) {
            uint[] memory fresh = new uint[](0);
            require(fresh.length == 0);
            i = 0;
        }
        return i;
    }

    function allocationBeforeRevert() public pure {
        uint i = 2;
        while (i > 0) {
            uint[] memory fresh = new uint[](0);
            require(fresh.length == 0);
            revert();
        }
    }


    function scopedArrays() public pure returns (uint) {
        uint[] memory xs = new uint[](2);
        uint[] memory same = xs;
        uint i = 0;
        if (true) { while (i < xs.length) { xs[i] = i + 3; i++; } }
        return same[1];
    }

    function scopedRecords() public pure returns (uint) {
        Record memory r = Record(0, 5);
        Record memory same = r;
        if (true) { while (r.n < 3) { r.n++; r.signed -= 2; } }
        require(same.signed == -1);
        return same.n;
    }

    function scopedAllocateTurn() public pure returns (uint) {
        uint i = 2;
        if (true) { while (i > 0) {
            uint[] memory fresh = new uint[](0);
            require(fresh.length == 0);
            i = 0;
        } }
        return i;
    }

    function scopedAllocationBeforeRevert() public pure {
        uint i = 2;
        if (true) { while (i > 0) {
            uint[] memory fresh = new uint[](0);
            require(fresh.length == 0);
            revert();
        } }
    }
}
