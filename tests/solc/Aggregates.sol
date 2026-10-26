// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
contract Aggregates {
    uint[] values;
    uint[4] tail;
    uint[][] rows;
    uint[1] cell;
    struct Pair { uint n; bool b; }
    function change() internal returns (uint[1] storage r) { cell[0] = 9; return cell; }
    function changeMem(uint[1] memory c) internal pure returns (uint[1] memory r) { c[0] = 9; return c; }
    /// @custom:key box
    function literals() public pure {
        uint16[2] memory m = [1, 256];
        bool[2] memory b = [true, false];
        bytes2[2] memory bs = [bytes2(hex"0102"), bytes2(hex"0304")];
        assert(m[1] == 256 && b[0] && !b[1] && bs[1] == hex"0304");
    }
    /// @custom:key box
    function copies() public {
        values.push(8); values.push(8); values.push(8);
        uint[2] memory m = [uint(1), 2];
        values = m; tail = m; rows.push(m); m[0] = 7; values.push();
        assert(values.length == 3 && values[0] == 1 && values[2] == 0);
        assert(tail[3] == 0 && rows[0][1] == 2);
    }
    function storageElements() public {
        cell[0] = 1;
        uint[1][2] memory a = [cell, change()];
        assert(a[0][0] == 1 && a[1][0] == 9);
    }
    function memoryElements() public pure {
        uint[1] memory c = [uint(1)];
        uint[1][2] memory a = [c, changeMem(c)];
        assert(a[0][0] == 9 && a[1][0] == 9);
    }
    function tuples() public pure {
        uint[1] memory a = [uint(1)]; uint[1] memory b = [uint(2)];
        (a, b) = (b, a); assert(a[0] == 2 && b[0] == 1);
    }
    function nested() public pure {
        uint[2][2] memory a = [[uint(1), 2], [uint(3), 4]];
        Pair[2] memory ps = [Pair(1, true), Pair(2, false)];
        assert(a[1][0] == 3 && ps[1].n == 2 && ps[0].b);
    }
    function abiLiteral() public pure {
        bytes memory data = abi.encode([uint(1), 2]);
        uint[2] memory a = abi.decode(data, (uint[2]));
        assert(a[0] == 1 && a[1] == 2);
    }
    function narrowNested() public pure {
        uint8[2][2] memory a = [[uint8(1), 2], [uint8(3), 4]];
        assert(a[1][0] == 3);
    }
    /// @custom:key box
    function falsePost() public pure {
        uint[2] memory a = [uint(1), 2]; assert(a[1] == 3);
    }
    function bounds(uint k) public pure {
        uint[1] memory a = [uint(1)]; require(k == 1); uint x = a[k]; assert(x == 1);
    }
}
