// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
// Narrow types inside types: an array's element, a mapping's key and value,
// a struct's member; in state variables, locals, parameters and memory. Each
// position keeps its width.
struct Packed { uint8 a; int16 b; uint c; uint8[] xs; }

contract NarrowNested {
    uint8[] small;
    Packed p;
    mapping(uint => Packed) byId;
    modifier atMost(uint8 cap) { require(cap > 1); _; }
    mapping(uint => int8) temps;
    mapping(uint8 => uint) byKey;
    mapping(uint => mapping(uint => uint16)) grid;
    /// @custom:key box
    function valueOverflowPanics() public {
        temps[1] = 127;
        temps[1] += 1;
        assert(false);
    }
    function valueInRange() public {
        temps[1] = -100;
        temps[1] -= 28;
        assert(temps[1] == -128);
    }
    /// @custom:key box
    function elementTypeChecked() public {
        grid[1][2] = 60000;
        uint w = grid[1][2] + grid[1][2];
        assert(false);
    }
    function uncheckedWraps() public {
        grid[0][0] = 65535;
        unchecked { grid[0][0] += 1; }
        assert(grid[0][0] == 0);
    }
    function narrowKey(uint8 k) public {
        byKey[k] = 1;
        assert(byKey[k] == 1);
    }
    /// @custom:key box
    function pushOverflowPanics() public {
        small.push(255);
        small[small.length - 1] += 1;
        assert(false);
    }
    /// @custom:key box
    function memberOverflowPanics() public {
        p.a = 250;
        p.a += 6;
        assert(false);
    }
    function memberInRange() public {
        p.b = -32768;
        p.b += 32767;
        assert(p.b == -1);
    }
    /// @custom:key box
    function valueMemberPanics() public {
        byId[1].a = 200;
        byId[1].a += 100;
        assert(false);
    }
    /// @custom:key box
    function memberArrayPanics() public {
        p.xs.push(255);
        p.xs[p.xs.length - 1] += 1;
        assert(false);
    }
    /// @custom:key box
    function memoryMemberPanics() public {
        Packed memory q;
        q.a = 255;
        q.a++;
        assert(false);
    }
    /// @custom:key box
    function aliasPanics() public {
        uint8[] storage s = small;
        s.push(255);
        s[s.length - 1] += 1;
        assert(false);
    }
    /// @custom:key box
    function memoryPanics() public {
        uint8[] memory m = new uint8[](2);
        m[0] = 255;
        m[0] += 1;
        assert(false);
    }
    /// @custom:key box
    function copyPanics() public {
        uint8[] memory m = small;
        m[0] = 255;
        m[0]++;
        assert(false);
    }
    function sum(uint8[] memory xs) internal pure returns (uint8) {
        return xs[0] + xs[1];
    }
    /// @custom:key box
    function memoryParamPanics() public {
        uint8[] memory m = new uint8[](2);
        m[0] = 200;
        m[1] = 100;
        sum(m);
        assert(false);
    }
    function memoryWraps() public {
        uint8[] memory m = new uint8[](1);
        m[0] = 255;
        unchecked { m[0] += 2; }
        assert(m[0] == 1);
    }
    /// @custom:key box
    function modifierParam(uint8 c) public atMost(c) {
        assert(c > 1);
    }
}
