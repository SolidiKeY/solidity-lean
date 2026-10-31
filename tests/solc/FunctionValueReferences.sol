// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Internal function values with a memory- or storage-array parameter
// (docs/feature-work/finite-dispatch.md, "Reference arguments").
contract FunctionValueReferences {
    struct P { uint a; uint b; }
    struct Q { uint a; uint b; }
    uint calls;
    uint[] values;
    P stored;
    function(uint[] memory) internal returns (uint) op;
    function(uint[] memory, uint) internal returns (uint) op2;

    function sum2(uint[] memory xs) internal pure returns (uint) { return xs[0] + xs[1]; }
    function bump(uint[] memory xs) internal returns (uint) { calls++; xs[0] += 10; return xs[0]; }
    function pair(uint[] memory xs, uint k) internal pure returns (uint) { return xs[0] * 100 + k; }
    function triple(uint[] memory xs, uint k) internal pure returns (uint) { return xs[0] * 1000 + k; }
    function setFirst() internal returns (uint) { values[0] = 9; return 1; }
    function swapOp2() internal returns (uint) { op2 = triple; return 2; }
    function firstStored(uint[] storage xs) internal returns (uint) { xs[0] += 5; return xs[0]; }
    function pairStored(uint[] storage xs, uint k) internal view returns (uint) { return xs[0] * 100 + k; }
    function fill(uint[] memory xs, uint k) internal pure returns (bytes memory b) {
        b = new bytes(xs.length); b[0] = bytes1(uint8(k));
    }
    function grow(uint[] memory xs) internal pure returns (uint[] memory ys) { ys = xs; ys[0] += 1; }
    function fresh(uint[] memory xs) internal pure returns (uint[] memory ys) {
        ys = new uint[](1); ys[0] = xs[0] * 2;
    }
    function bumpP(P memory p) internal pure returns (uint) { p.a += 1; return p.a; }
    function sumQ(Q memory q) internal pure returns (uint) { return q.a + q.b; }
    function bumpStoredP(P storage p) internal returns (uint) { p.a += 7; return p.a; }
    function narrowFirst(uint8[] memory xs) internal pure returns (uint) { return xs[0]; }

    function aliasing() public returns (uint, uint, uint) {
        uint[] memory xs = new uint[](2);
        xs[0] = 1; xs[1] = 2;
        function(uint[] memory) internal returns (uint) h = bump;
        uint r = h(xs);
        return (r, xs[0], calls);
    }

    function storageCopy() public returns (uint, uint, uint) {
        delete values; values.push(1); values.push(2);
        function(uint[] memory) internal returns (uint) h = bump;
        uint r = h(values);
        return (r, values[0], calls);
    }

    function argumentOrder() public returns (uint, uint) {
        delete values; values.push(1);
        function(uint[] memory, uint) internal returns (uint) h = pair;
        uint r = h(values, setFirst());
        return (r, values[0]);
    }

    function argumentOrderDirect() public returns (uint, uint) {
        delete values; values.push(1);
        uint r = pair(values, setFirst());
        return (r, values[0]);
    }

    function calleeOrder() public returns (uint) {
        uint[] memory xs = new uint[](1);
        xs[0] = 4;
        op2 = pair;
        return op2(xs, swapOp2());
    }

    function branches(bool b) public returns (uint) {
        op = b ? bump : sum2;
        uint[] memory xs = new uint[](2);
        xs[0] = 3; xs[1] = 4;
        return op(xs);
    }

    function unassigned() public returns (uint) {
        function(uint[] memory) internal returns (uint) h;
        uint[] memory xs = new uint[](1);
        return h(xs);
    }

    function deleted() public returns (uint) {
        op = sum2;
        delete op;
        uint[] memory xs = new uint[](2);
        return op(xs);
    }

    function narrow() public pure returns (uint) {
        uint8[] memory xs = new uint8[](1);
        xs[0] = 200;
        function(uint8[] memory) internal pure returns (uint) h = narrowFirst;
        return h(xs);
    }

    function storageAlias() public returns (uint, uint) {
        delete values; values.push(1);
        uint[] storage s = values;
        function(uint[] storage) internal returns (uint) h = firstStored;
        uint r = h(s);
        return (r, values[0]);
    }

    function storageOrder() public returns (uint, uint) {
        delete values; values.push(1);
        function(uint[] storage, uint) internal view returns (uint) h = pairStored;
        uint r = h(values, setFirst());
        return (r, values[0]);
    }

    function arrayReturn(bool b) public pure returns (uint, uint, uint) {
        uint[] memory xs = new uint[](1);
        xs[0] = 5;
        function(uint[] memory) internal pure returns (uint[] memory) h = b ? grow : fresh;
        uint[] memory ys = h(xs);
        ys[0] += 100;
        return (xs[0], ys[0], ys.length);
    }

    function bytesReturn() public pure returns (uint, uint) {
        uint[] memory xs = new uint[](3);
        function(uint[] memory, uint) internal pure returns (bytes memory) h = fill;
        bytes memory b = h(xs, 65);
        return (b.length, uint8(b[0]));
    }

    function structMemory() public returns (uint, uint, uint) {
        P memory p;
        p.a = 1; p.b = 2;
        function(P memory) internal pure returns (uint) h = bumpP;
        uint r = h(p);
        stored.a = 3;
        uint s = h(stored);
        return (r, p.a, s * 10 + stored.a);
    }

    function structStorage() public returns (uint, uint) {
        stored.a = 1;
        function(P storage) internal returns (uint) h = bumpStoredP;
        uint r = h(stored);
        return (r, stored.a);
    }

    function nominalQ() public pure returns (uint) {
        Q memory q;
        q.a = 4; q.b = 5;
        function(Q memory) internal pure returns (uint) h = sumQ;
        return h(q);
    }

    function falseObservation() public returns (uint) {
        uint[] memory xs = new uint[](2);
        xs[0] = 1;
        function(uint[] memory) internal returns (uint) h = bump;
        h(xs);
        assert(xs[0] == 1);
        return xs[0];
    }
}
