// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

contract MemoryPush {
    struct Token { uint value; }
    uint[][] rows;
    uint[][][] cube;
    Token[] tokens;

    /// @custom:key box
    function arrayCopy() public {
        delete rows;
        uint[] memory row = new uint[](2);
        row[1] = 7;
        rows.push(row);
        row[1] = 9;
        assert(rows.length == 1 && rows[0].length == 2 && rows[0][1] == 7);
    }

    /// @custom:key box
    function arrayFalse() public {
        delete rows;
        uint[] memory row = new uint[](1);
        row[0] = 7;
        rows.push(row);
        row[0] = 9;
        assert(rows[0][0] == 9);
    }

    /// @custom:key box
    function structCopy() public {
        delete tokens;
        Token memory token;
        token.value = 11;
        tokens.push(token);
        token.value = 13;
        assert(tokens[0].value == 11);
    }

    /// @custom:key box
    function recycledSlot() public {
        delete rows;
        rows.push(); rows[0].push(17); rows[0].push(19);
        rows.pop();
        uint[] memory row = new uint[](1);
        row[0] = 23;
        rows.push(row);
        assert(rows.length == 1 && rows[0].length == 1 && rows[0][0] == 23);
    }

    /// @custom:key box
    function receiverUsesLength() public {
        delete cube;
        cube.push(); cube.push();
        uint[] memory row = new uint[](1);
        row[0] = 29;
        cube[cube[0].length].push(row);
        assert(cube[0].length == 1 && cube[0][0][0] == 29 && cube[1].length == 0);
    }

    /// @custom:key box
    function receiverFalse() public {
        delete cube;
        cube.push(); cube.push();
        uint[] memory row = new uint[](1);
        row[0] = 29;
        cube[cube[0].length].push(row);
        assert(cube[1].length == 1);
    }

    /// @custom:key box
    function complexMemorySource() public {
        delete tokens;
        Token[] memory ts = new Token[](1);
        ts[0].value = 31;
        tokens.push(ts[0]);
        ts[0].value = 37;
        assert(tokens[0].value == 31);
    }

    /// @custom:key box
    function complexMemoryFalse() public {
        delete tokens;
        Token[] memory ts = new Token[](1);
        ts[0].value = 31;
        tokens.push(ts[0]);
        ts[0].value = 37;
        assert(tokens[0].value == 37);
    }

    /// @custom:key box
    function badMemorySource() public {
        delete tokens;
        Token[] memory ts = new Token[](1);
        tokens.push(ts[1]);
    }
}
