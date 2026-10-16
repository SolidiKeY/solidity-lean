// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
contract UnsignedCoin { type Coin is uint; }
contract SourceTypes {
    type Coin is int;
    /// @custom:key box
    function signedAliasIsNotAlwaysPositive(Coin x) public pure {
        assert(Coin.unwrap(x) >= 0);
    }
    /// @custom:key box
    function negativeAlias() public pure {
        Coin x = Coin.wrap(-1);
        int expected = -1;
        assert(Coin.unwrap(x) == expected);
    }
    // The default obligation is a diamond.
    function narrowOverflowCannotReturn() public pure {
        uint y = type(uint8).max + 1;
        assert(y == 256);
    }
    /// @custom:key box
    function narrowOverflowPanics() public pure {
        uint y = type(uint8).max + 1;
        assert(false);
    }
    // The default obligation is a diamond.
    function signedOverflowCannotReturn() public pure {
        bool y = Coin.unwrap(Coin.wrap(2**255 - 1)) + 1 >= 0;
        assert(y);
    }
    /// @custom:key box
    function signedOverflowPanics() public pure {
        bool y = Coin.unwrap(Coin.wrap(2**255 - 1)) + 1 >= 0;
        assert(false);
    }
    function ternaryOverflowCannotReturn() public pure {
        bool t = true;
        bool f = false;
        uint16 r = (t ? 63 : 255) + (f ? 63 : 255);
        assert(r == 318);
    }
    /// @custom:key box
    function ternaryOverflowPanics() public pure {
        bool t = true;
        bool f = false;
        uint16 r = (t ? 63 : 255) + (f ? 63 : 255);
        assert(false);
    }
    /// @custom:key box
    function ternaryUncheckedWraps() public pure {
        bool t = true;
        bool f = false;
        uint16 r;
        unchecked { r = (t ? 63 : 255) + (f ? 63 : 255); }
        assert(r == 62);
    }
    /// @custom:key box
    function ternaryExplicitWidening() public pure {
        bool t = true;
        bool f = false;
        uint16 a = 63;
        uint16 b = 255;
        uint16 r = (t ? a : b) + (f ? a : b);
        assert(r == 318);
    }
    /// @custom:key box
    function ternaryEffectsOnce() public pure {
        bool t = true;
        bool f = false;
        uint8 x = 5;
        uint8 y = 8;
        uint16 r = (t ? x++ : y++) + (f ? x++ : y++);
        assert(r == 13 && x == 6 && y == 9);
    }
    /// @custom:key box
    function nestedTypedConditionals(bool c, bool d) public pure {
        uint8 x = 1;
        uint8 y = 2;
        uint8 r = c ? (d ? x : y) : y;
        assert(r == 1 || r == 2);
        assert(c || (d ? x : y) <= y);
    }
    function signedTernaryOverflowCannotReturn() public pure {
        bool t = true;
        int8 a = 127;
        int8 b = 1;
        int16 r = (t ? a : b) + (t ? b : a);
        assert(r == 128);
    }
    /// @custom:key box
    function signedLiteralConditional() public pure {
        bool t = true;
        int16 r = t ? -1 : -127;
        assert(r == -1);
    }
    /// @custom:key box
    function nestedLiteralConditional(bool c, bool d) public pure {
        uint16 r = c ? (d ? 1 : 2) : 3;
        assert(r <= 3);
    }
    /// @custom:key box
    function shortCircuitLiteralConditional(bool c, bool d) public pure {
        assert(c || (d ? 1 : 2) <= 2);
    }
}
