// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.38;
contract SignedNumeric {
    function shifts() public pure {
        int8 a = -67;
        uint n = 4;
        assert(a >> n == -5);
        assert(a >> 8 == -1);
        assert(a >> 256 == -1);
        assert(a >> (uint(1) << 255) == -1);
        assert(a >> type(uint).max == -1);
        assert(a << 0 == -67);
        assert(a << 1 == 122);
        assert(a << 8 == 0);
        assert(a << type(uint).max == 0);
        int8 one = 1;
        assert(one << 7 == -128);
        int16 wide = -32767;
        assert(wide >> 16 == -1);
        int256 full = -1;
        assert(full << 255 == type(int256).min);
        assert(full << 256 == 0);
        assert((-4267 >> 1) == -2134);
    }
    function contextualNegative(uint n) internal pure returns (int256) { return (-2) ** n; }
    function contextualPositive(uint n) internal pure returns (uint256) { return 2 ** n; }
    function parity() public pure {
        int8 a = -2;
        uint n = 3;
        assert(a ** n == -8);
        assert(a ** 2 == 4);
        assert(contextualNegative(n) == -8);
        assert(contextualPositive(n) == 8);
    }
    function powers() public pure {
        int8 a = -2;
        uint n = 7;
        assert(a ** n == -128);
        assert(a ** 6 == 64);
        assert(a ** 0 == 1);
        int256 m = type(int256).min;
        assert(m ** 1 == m);
        int256 minusOne = -1;
        assert(minusOne ** type(uint).max == -1);
        assert(minusOne ** (type(uint).max - 1) == 1);
        assert((-2) ** n == -128);
        assert(-((-2) ** 6) == -64);
    }
    function uncheckedControls() public pure {
        int8 a = -2;
        unchecked {
            assert(a ** 8 == 0);
            assert(a ** 7 == -128);
            assert(a << 7 == 0);
        }
    }
    function effects() public pure {
        int8 a = -2;
        uint n = 3;
        int8 r = a++ ** n++;
        assert(r == -8);
        assert(a == -1);
        assert(n == 4);
    }
    function checkedOverflow() public pure {
        int8 a = -2;
        uint n = 8;
        int8 r = a ** n;
        assert(r == 0);
    }
    function wrongShift() public pure {
        int8 a = -67;
        uint n = 1;
        assert(a >> n == -33);
    }
    function shadowed() public pure returns (uint8 x) {
        unchecked {
            uint16 x = 0x166;
            return uint8(x) ** uint8(uint8(2) ** uint8(8));
        }
    }
}
