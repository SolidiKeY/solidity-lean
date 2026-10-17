// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract StorageDangling {
    struct Token { uint value; }
    Token[] tokens;
    Token[] emptyTokens;
    uint[][] matrix;

    function testDeleteArrayLeavesDataPastLength() public {
        delete tokens;
        tokens.push();
        Token storage r = tokens[0];
        tokens.pop();
        r.value = 5;
        delete tokens;
        tokens.push();
        assert(tokens[0].value == 5);
    }

    function testDanglingReferenceSurvivesPush() public {
        delete tokens;
        tokens.push();
        Token storage r = tokens[0];
        tokens.pop();
        r.value = 5;
        tokens.push();
        assert(tokens[0].value == 5);
    }

    function testArrayCopyKeepsDestinationTail() public {
        delete emptyTokens;
        delete tokens;
        tokens.push();
        Token storage r = tokens[0];
        tokens.pop();
        r.value = 5;
        tokens = emptyTokens;
        tokens.push();
        assert(tokens[0].value == 5);
    }

    function testDanglingInnerArrayReappearsAfterPush() public {
        delete matrix;
        matrix.push();
        uint[] storage ptr = matrix[0];
        matrix.pop();
        ptr.push(66);
        matrix.push();
        assert(matrix[0].length == 1);
        assert(matrix[0][0] == 66);
    }
}
