// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.28;
contract TransientProduct {
    uint public saved;
    uint transient scratch;
    constructor(bool fail) {
        scratch = 9;
        saved = scratch;
        if (fail) revert();
    }
    function checkFrame() external view { assert(scratch == 9 && saved == 9); }
    function checkReset() external view { assert(scratch == 0 && saved == 9); }
    function write() external { scratch = 7; saved = 11; }
    function checkWritten() external view { assert(scratch == 7 && saved == 11); }
    function checkLater() external view { assert(scratch == 0 && saved == 11); }
    function falseShared() external view { assert(scratch == saved); }
    function fail() external { scratch = 5; saved = 99; revert(); }
}
contract TransientFactory {
    function make() external returns (TransientProduct) { return new TransientProduct(false); }
    function failMake() external returns (TransientProduct) { return new TransientProduct(true); }
    function caught() external returns (bool) {
        try new TransientProduct(true) returns (TransientProduct child) { return true; }
        catch { return false; }
    }
}
