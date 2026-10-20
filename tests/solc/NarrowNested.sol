// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
// Narrow types inside a state variable's type: an array's element, a
// mapping's key and value. Each position keeps its width.
contract NarrowNested {
    uint8[] small;
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
}
