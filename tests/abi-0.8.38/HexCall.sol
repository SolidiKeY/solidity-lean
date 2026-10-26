// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;
pragma abicoder v2;

contract AbiHexCall {
    function two(bytes2 x) external pure returns (bytes2) { return x; }
    function mixed(bytes2 x, uint y) external pure returns (bytes2, uint) { return (x, y); }
    function selector(bytes4 x) external pure returns (bytes4) { return x; }
    function word(bytes32 x) external pure returns (bytes32) { return x; }

    /// @custom:key box
    function exactHex() public view {
        bytes memory e = abi.encodeCall(this.two, (0xabcd));
        assert(e.length == 36 && e[4] == hex"ab" && e[5] == hex"cd");
        assert(e[6] == hex"00" && e[35] == hex"00");
    }

    /// @custom:key box
    function leadingZero() public view {
        bytes memory e = abi.encodeCall(this.two, ((0x00ab)));
        assert(e.length == 36 && e[4] == hex"00" && e[5] == hex"ab");
    }

    /// @custom:key box
    function mixedHex() public view {
        bytes memory e = abi.encodeCall(this.mixed, (0xAb_Cd, 7));
        assert(e.length == 68 && e[4] == hex"ab" && e[5] == hex"cd");
        assert(e[67] == hex"07");
    }

    /// @custom:key box
    function groupedMixed() public view {
        bytes memory e = abi.encodeCall(this.mixed, ((0x00ab), ((7))));
        assert(e.length == 68 && e[4] == hex"00" && e[5] == hex"ab");
        assert(e[67] == hex"07");
    }

    /// @custom:key box
    function pointerHex() public view {
        function(bytes2) external pure returns (bytes2) p = this.two;
        bytes memory e = abi.encodeCall(p, (0x00ab));
        assert(e.length == 36 && e[4] == hex"00" && e[5] == hex"ab");
    }

    /// @custom:key box
    function selectorArgument() public view {
        bytes memory e = abi.encodeCall(this.selector, (this.two.selector));
        bytes memory expected = abi.encodeWithSelector(this.selector.selector, this.two.selector);
        assert(e.length == 36 && expected.length == 36);
        assert(e[4] == expected[4] && e[5] == expected[5]);
        assert(e[6] == expected[6] && e[7] == expected[7]);
    }

    /// @custom:key box
    function fullWord() public view {
        bytes memory e = abi.encodeCall(this.word,
            (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff));
        assert(e.length == 36 && e[4] == hex"ff" && e[35] == hex"ff");
    }

    /// @custom:key box
    function numericHex() public pure {
        bytes memory p = abi.encode(0xabcd);
        assert(p.length == 32 && p[30] == hex"ab" && p[31] == hex"cd");
    }

    /// @custom:key box
    function falseHex() public view {
        bytes memory e = abi.encodeCall(this.two, (0xabcd));
        assert(e[4] == hex"00");
    }
}
