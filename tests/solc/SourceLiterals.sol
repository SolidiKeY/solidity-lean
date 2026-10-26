// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;
pragma abicoder v2;

contract SourceLiterals {
    uint constant N = 1 + 2;
    uint[N] bounded;
    uint[2][N] nested;

    /// @custom:key box
    function rationalRemainders() public pure {
        uint a = uint((1.5 % 1) * 2);
        uint b = uint((1.5 % 0.4) * 10);
        int c = int((-1.5 % 1) * 2);
        assert(a == 1 && b == 3 && c == -1);
    }

    /// @custom:key box
    function signedConstants() public pure {
        int a = (-5) >> 1;
        int b = -1 & 3;
        int c = -1 | 3;
        int d = -1 ^ 3;
        int e = -1 & -3;
        int f = -1 | -3;
        int g = -1 ^ -3;
        assert(a == -3 && b == 3 && c == -1 && d == -4);
        assert(e == -3 && f == -1 && g == 2);
    }

    /// @custom:key box
    function computedBounds() public {
        bounded[2] = 7;
        nested[2][1] = 9;
        assert(bounded.length == 3 && nested.length == 3);
        assert(bounded[2] == 7 && nested[2][1] == 9);
    }

    /// @custom:key box
    function byteSequences() public pure {
        bytes memory a = hex"ff";
        bytes memory b = "\xff";
        bytes memory c = hex"ab" hex"cd";
        bytes memory d = bytes(unicode"é" unicode"λ");
        assert(a.length == 1 && b.length == 1 && c.length == 2 && d.length == 4);
        assert(a[0] == hex"ff" && b[0] == hex"ff");
        assert(c[0] == hex"ab" && c[1] == hex"cd");
    }

    /// @custom:key box
    function extremeConstants() public pure {
        uint a = 1 >> 4294967295;
        int b = (-5) >> 4294967295;
        uint c = 0 << 4294967295;
        uint d = 0e5000;
        uint e = 0e-4294967296;
        assert(a == 0 && b == -1 && c == 0 && d == 0 && e == 0);
    }

    /// @custom:key box
    function degeneratePowers() public pure {
        uint a = 0 ** 4294967296;
        uint b = 1 ** (-4294967296);
        int c = (-1) ** 4294967296;
        int d = (-1) ** (-4294967297);
        uint e = 0 ** (-1);
        uint f = 0 ** 0;
        uint g = uint((0.5 ** (-1)));
        assert(a == 0 && b == 1 && c == 1 && d == -1);
        assert(e == 0 && f == 1 && g == 2);
    }

    /// @custom:key box
    function addressContext() public pure {
        bytes memory packed = abi.encodePacked(0x0000000000000000000000000000000000001234);
        assert(packed.length == 20);
        assert(packed[18] == hex"12" && packed[19] == hex"34");
        address[2][1] memory values = [[
            0x0000000000000000000000000000000000001234,
            0x0000000000000000000000000000000000005678
        ]];
        assert(values[0][0] == address(0x1234));
        assert(values[0][1] == address(0x5678));
        bool choose = true;
        bytes memory conditional = abi.encodePacked(choose ? address(0x1234) : address(0x5678));
        assert(conditional.length == 20 && conditional[19] == hex"34");
        bool lazy = false && abi.encodePacked(address(9)).length == 20;
        assert(!lazy);
        bytes memory selector = abi.encodePacked(this.metadataTarget.selector);
        assert(selector.length == 4);
        bytes memory word = abi.encode(this.metadataTarget.selector);
        assert(word.length == 32 && word[4] == hex"00" && word[31] == hex"00");
        assert(word[0] == selector[0] && word[3] == selector[3]);
    }

    function metadataTarget() public pure {}

    /// @custom:key box
    function falseRemainder() public pure {
        assert(uint((1.5 % 1) * 2) == 2);
    }
}

