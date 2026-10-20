// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
// Struct constructor calls, positional and named: a memory struct built, its
// members read, and the struct assigned to storage; narrow members keep
// their widths.  The structs are the table's (`Semantics.structDef`).
struct Pair { uint a; uint b; }
struct Inner { uint a; uint b; uint c; }
struct Outer { uint a; Inner s; }
struct Packed { uint8 a; int16 b; uint c; uint8[] xs; }

contract StructLiterals {
    Pair stored;
    Packed packed;
    mapping(uint => Pair) pairs;

    function positional() public pure {
        Pair memory p = Pair(1, 2);
        assert(p.a == 1 && p.b == 2);
    }
    function named() public pure {
        Pair memory p = Pair({b: 4, a: 3});
        assert(p.a == 3);
        assert(p.b == 4);
    }
    function fromParameters(uint x, uint y) public pure {
        Pair memory p = Pair(x, y);
        assert(p.a == x);
        assert(p.b == y);
    }
    function nested(uint x) public pure {
        Outer memory o = Outer(x, Inner(1, 2, 3));
        assert(o.a == x);
        assert(o.s.c == 3);
    }
    function toStorage(uint x) public {
        stored = Pair(x, 7);
        assert(stored.a == x);
        assert(stored.b == 7);
    }
    function toMapping(uint k) public {
        pairs[k] = Pair({a: k, b: 1});
        assert(pairs[k].a == k);
        assert(pairs[k].b == 1);
    }
    function narrowMembers(uint8 x, int16 y) public pure {
        uint8[] memory m = new uint8[](1);
        Packed memory q = Packed(x, y, 3, m);
        assert(q.a == x);
        assert(q.b == y);
    }
    function narrowNamed() public pure {
        uint8[] memory m = new uint8[](0);
        Packed memory q = Packed({xs: m, c: 1, b: -300, a: 255});
        assert(q.a == 255 && q.b == -300);
    }
    function narrowToStorage(uint8 x) public {
        uint8[] memory m = new uint8[](0);
        packed = Packed(x, -1, 2, m);
        assert(packed.a == x);
        assert(packed.b == -1);
    }
    /// @custom:key box
    function narrowMemberOverflowPanics(uint8 x) public pure {
        require(x == 255);
        uint8[] memory m = new uint8[](0);
        Packed memory q = Packed(x, 0, 0, m);
        q.a += 1;
        assert(false);
    }
    // a false claim stays pending
    function wrongMember() public pure {
        Pair memory p = Pair(1, 2);
        assert(p.a == 2);
    }
}
