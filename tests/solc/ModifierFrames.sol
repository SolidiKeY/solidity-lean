// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
contract ModifierFrames {
    uint public total;
    enum E { A, B }
    uint[] data;
    uint[] other;
    modifier repeatCount(uint count) { for (uint i = 0; i < count; ++i) _; }
    modifier maybeTwice(bool twice) { if (twice) _; _; }
    modifier twice() { _; _; }
    modifier afterBody() { _; total += 10; }
    modifier skipBody(bool skip) { if (!skip) _; }
    modifier observe(uint a) { total = total * 10 + a; _; }
    modifier input(uint a) { _; }
    modifier stop(uint a) { if (a == 0) _; }
    function assignedReturn() public input(x = 2) input(y = 3) returns (uint x, uint y) {}
    function assignedSkipped() public stop(x = 2) returns (uint x) {}
    function loop() public repeatCount(10) returns (uint r) { r += 1; }
    function multi(bool b) public maybeTwice(b) returns (uint r) { r += 1; }
    function parameter(uint a) public twice returns (uint r) { r = a++; }
    function nested() public twice twice returns (uint r) { r += 1; }
    function skips() public twice skipBody(true) returns (uint r) { r += 1; }
    function early() public afterBody twice returns (uint r) { total++; r++; return r; }
    function argument(uint a) public twice observe(a++) returns (uint r) { r = a; }
    function memoryAlias(uint[] memory a) public twice returns (uint r) { a[0]++; r = a[0]; a = new uint[](1); }
    function narrow(uint8 a) public twice returns (uint8 r) { r = a++; }
    function pair() public twice returns (uint a, bool b) { a++; b = !b; }
    function packed(E e) public twice returns (uint r) { r = abi.encodePacked(e).length; }
    function packedArray(E[] memory e) public twice returns (uint r) { r = abi.encodePacked(e).length; }
    function stringLength(string memory s) public twice returns (uint r) { r = bytes(s).length; }
    function inc(uint a) internal pure returns (uint) { return a + 1; }
    function invoke(function(uint) internal pure returns(uint) h) internal twice returns(uint r) { r = h(7); }
    function functionSlot() public returns(uint) { return invoke(inc); }
    function storageWork(uint[] storage a) internal twice returns(uint r) { a[0]++; r = a[0]; a = other; }
    function storageAlias() public returns(uint) { data.push(); other.push(); return storageWork(data); }
    function memRet() internal twice returns(uint[] memory r) { r = new uint[](1); r[0] = 7; }
    function memoryReturn() public returns(uint) { uint[] memory r = memRet(); return r[0]; }
    function failRepeat() public twice { total++; if (total == 2) revert(); }
    function rollback() public returns(uint) { try this.failRepeat() {} catch {} return total; }
}
