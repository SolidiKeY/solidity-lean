// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
contract SliceCopies {
    uint[] stored;
    uint[][] rows;
    function read(uint[] calldata v) internal pure returns (uint) { return v[0] + v.length; }
    function mutate(uint[] memory v) internal pure returns (uint) { v[0] = 99; return v.length; }
    function echo(uint[] calldata xs) internal pure returns (uint[] memory) { return xs[1:3]; }
    /// @custom:key box
    function copies(uint[] calldata xs) public pure {
        require(xs.length == 4 && xs[0] == 3 && xs[1] == 5 && xs[2] == 7 && xs[3] == 9);
        uint[] calldata view_ = xs[1:4];
        uint[] memory a = view_[0:2];
        uint[] memory b = view_;
        a[0] = 21; b[1] = 31;
        assert(xs[1] == 5 && view_[1] == 7 && a[1] == 7 && b[0] == 5);
        uint k = 0;
        uint[] memory effects = xs[k++:k++ + 1];
        assert(k == 2 && effects.length == 2 && effects[0] == 3 && effects[1] == 5);
        uint[] memory empty = xs[2:2]; assert(empty.length == 0);
    }
    /// @custom:key box
    function passing(uint[] calldata xs) public pure {
        require(xs.length == 4 && xs[1] == 5 && xs[2] == 7);
        uint[] calldata v = xs[1:3];
        assert(read(v) == 7 && read(xs[1:3]) == 7);
        assert(mutate(v) == 2 && mutate(xs[1:3]) == 2);
        uint[] memory returned = echo(xs);
        returned[0] = 43;
        assert(v[0] == 5 && xs[1] == 5 && returned[1] == 7);
    }
    /// @custom:key box
    function storageCopy(uint[] calldata xs) public {
        require(xs.length == 4 && xs[1] == 5 && xs[2] == 7);
        uint[] calldata v = xs[1:3];
        stored = v; rows.push(xs[1:3]);
        stored[0] = 81; rows[0][1] = 82;
        assert(v[0] == 5 && v[1] == 7 && stored.length == 2 && rows[0][0] == 5);
    }
    /// @custom:key box
    function hashes(bytes calldata data) public pure {
        require(data.length == 5 && data[1] == 0x61 && data[2] == 0x62 && data[3] == 0x63);
        bytes calldata v = data[1:4];
        bytes memory m = v;
        m[0] = 0x78;
        assert(keccak256(v) == keccak256("abc"));
        assert(sha256(data[1:4]) == sha256("abc"));
        assert(ripemd160(v) == ripemd160("abc"));
        assert(v[0] == 0x61 && m[0] == 0x78);
    }
    /// @custom:key box
    function narrow(uint8[] calldata xs, bool[] calldata flags, bytes2[] calldata pairs) public pure {
        require(xs.length == 2 && xs[1] == 255 && flags.length == 2 && flags[1] && pairs.length == 2 && pairs[1] == 0x1234);
        uint8[] memory n = xs[1:]; bool[] memory b = flags[1:]; bytes2[] memory p = pairs[1:];
        n[0] = 1; b[0] = false; p[0] = 0x5678;
        assert(xs[1] == 255 && flags[1] && pairs[1] == 0x1234);
    }
    struct Pair { uint value; }
    /// @custom:key box
    function aliases(Pair calldata p, uint[2] calldata xs) public pure {
        Pair calldata q = p; uint[2] calldata ys = xs;
        assert(q.value == p.value && ys[1] == xs[1]);
    }
    function lazy(uint[] calldata xs) public pure returns (bool) {
        return false && mutate(xs[9:10]) == 0;
    }
    function invalidRange(uint[] calldata xs) public pure returns (uint[] memory) { return xs[2:1]; }
    /// @custom:key box
    function falsePost(uint[] calldata xs) public pure {
        require(xs.length == 3 && xs[1] == 5);
        uint[] memory m = xs[1:2]; m[0] = 99; assert(xs[1] == 99);
    }
}
