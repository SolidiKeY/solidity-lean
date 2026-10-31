// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.38;
type Token is uint8;
contract SliceReferenceCopies {
    struct Pair { uint value; }
    enum Kind { One, Two }
    uint8[2][] stored;
    uint marker;
    function copies(uint8[2][] calldata xs) public pure {
        uint8[2][] calldata v = xs[1:3];
        uint8[2][] memory a = v;
        uint8[2][] memory b = v;
        a[0][0] = 21; a[1][1] = 31; b[0][1] = 41;
        assert(xs[1][0] == 5 && v[1][1] == 10);
        assert(a[0][1] == 6 && b[0][0] == 5 && b[1][1] == 10);
    }
    function independent(uint8[2][] calldata xs) public pure {
        uint8[2][] memory m = xs[:]; m[0][0] = 99;
        assert(xs[0][0] == 5 && xs[1][0] == 5 && m[1][0] == 5);
    }
    function rebound(uint8[2][] calldata xs, uint8[2][] calldata ys) public pure {
        uint8[2][] calldata v = xs[1:2]; xs = ys;
        uint8[2][] memory m = v; m[0][0] = 99;
        assert(v[0][0] == 5 && xs[0][0] == 3);
    }
    function endpoints(uint8[2][] calldata xs) public pure {
        uint lo = 0; uint hi = 2;
        uint8[2][] memory m = xs[lo++:hi++];
        assert(lo == 1 && hi == 3 && m.length == 2 && m[1][0] == 5);
    }
    function mutate(uint8[2][] memory m) internal pure returns (uint r) {
        m[0][0] = 99; r = m.length;
    }
    function passing(uint8[2][] calldata xs) public pure {
        uint n = mutate(xs[1:2]); assert(n == 1 && xs[1][0] == 5);
        bool r = false && mutate(xs[99:100]) == 0; assert(!r);
    }
    function echo(uint8[2][] calldata xs) internal pure returns (uint8[2][] memory r) {
        r = xs[1:3];
    }
    function returned(uint8[2][] calldata xs) public pure {
        uint8[2][] memory m = echo(xs); m[0][0] = 99;
        assert(m[1][1] == 10 && xs[1][0] == 5);
    }
    function storageCopy(uint8[2][] calldata xs) public {
        stored = xs[1:3]; stored[0][0] = 99;
        assert(xs[1][0] == 5 && stored[1][1] == 10);
    }
    function empty(uint8[2][] calldata xs) public pure {
        uint8[2][] memory m = xs[1:1]; assert(m.length == 0);
    }
    function signed(int8[2][] calldata xs) public pure {
        int8[2][] memory m = xs[:]; m[0][0] = -1;
        assert(xs[0][0] == -128 && m[0][1] == 127);
    }
    function kinds(bool[2][] calldata flags, bytes2[2][] calldata pairs, address[2][] calldata addrs) public pure {
        bool[2][] memory f = flags[:]; bytes2[2][] memory b = pairs[:];
        address[2][] memory a = addrs[:];
        f[0][0] = false; b[0][0] = 0x5678; a[0][0] = address(99);
        assert(flags[0][0] && pairs[0][0] == 0x1234 && addrs[0][0] == address(17));
        assert(b[0][1] == 0xabcd && a[0][1] == address(18));
    }
    function inlineCopy(uint8[2][] calldata xs) public pure {
        uint8[2][] memory m = [xs[1:3]][0]; m[0][0] = 99;
        uint8[2][] calldata v = xs[1:3];
        uint8[2][] memory n = [v[0:2]][0]; n[0][1] = 98;
        uint8[2][] memory z = [v][0]; z[1][0] = 97;
        assert(xs[1][0] == 5 && xs[1][1] == 6 && m[1][1] == 10 && n[1][1] == 10 && xs[2][0] == 9 && m[1][0] == 9 && n[1][0] == 9);
        uint k = mutate([xs[1:2]][0]); assert(k == 1 && xs[1][0] == 5);
        bool r = false && mutate([xs[99:100]][0]) == 0; assert(!r);
    }
    function invalidRange(uint8[2][] calldata xs) public {
        marker = 7; uint8[2][] memory m = xs[2:1]; assert(m.length == 0);
    }
    function rowBounds(uint8[2][] calldata xs) public pure returns (uint8 r) {
        uint8[2][] memory m = xs[0:1]; uint i = 2; r = m[0][i];
    }
    function falsePost(uint8[2][] calldata xs) public pure {
        uint8[2][] memory m = xs[0:1]; m[0][0] = 99; assert(xs[0][0] == 99);
    }
    function narrowFailure(uint8[2][] calldata xs) public pure {
        uint8[2][] memory m = xs[:]; m[0][0] += 1;
    }
    function getMarker() public view returns (uint) { return marker; }
    // Explicit refusals: these require separate interfaces or nominal premises.
    function nominal(Token[2][] calldata xs) public pure { Token[2][] memory m = xs[:]; }
    function enums(Kind[2][] calldata xs) public pure { Kind[2][] memory m = xs[:]; }
    function structs(Pair[] calldata xs) public pure { Pair[] memory m = xs[:]; }
}
