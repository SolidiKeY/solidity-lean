// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
contract PushBindings {
    uint[] values;
    uint[3][] rows;
    uint[][] matrix;
    struct Token { uint value; }
    Token[] tokens;
    function zero() internal pure returns (uint) { return 0; }
    /// @custom:key box
    function rootBinding() public {
        delete values;
        uint y = values.push();
        assert(y == 0 && values.length == 1);
        y = values.push();
        assert(y == 0 && values.length == 2);
        uint z = zero();
        assert(z == 0);
    }
    /// @custom:key box
    function falsePost() public {
        delete values;
        uint y = values.push();
        assert(y == 1);
    }
    function fixedReturn() public {
        uint[3] storage row = rows.push();
        assert(row.length == 3 && row[0] == 0 && row[2] == 0);
    }
    function dynamicReturn() public {
        uint[] storage row = matrix.push();
        assert(row.length == 0);
        row.push();
        assert(row[0] == 0);
    }
    function structReturn() public {
        Token storage token = tokens.push();
        assert(token.value == 0);
    }
    function falseReferencePost() public {
        Token storage token = tokens.push();
        assert(token.value == 1);
    }
}
