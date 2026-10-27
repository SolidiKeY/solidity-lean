// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
library StructNameLib {
    struct Box { uint8 value; }
    function inc(Box storage b) internal { unchecked { b.value++; } }
}
contract StructNameCollision {
    struct Box { uint unused; }
    struct Box_4 { uint value; }
    StructNameLib.Box b;
    /// @custom:key box
    function wraps() public {
        b.value = 255;
        StructNameLib.inc(b);
        assert(b.value == 0);
    }
    function wrapValue() public returns (uint) {
        b.value = 255;
        StructNameLib.inc(b);
        return b.value;
    }
    /// @custom:key box
    function falsePost() public {
        b.value = 255;
        StructNameLib.inc(b);
        uint result = b.value;
        assert(result == 256);
    }
}
