// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
contract PushSources {
    struct Token { uint value; }
    uint[] values;
    uint[][] rows;
    uint[][] copies;
    uint[][][] deep;
    Token[] records;
    uint source9;

    /// @custom:key box
    function primitive() public {
        delete rows; delete values;
        rows.push(); rows[0].push(7);
        values.push(rows[0][0]);
        assert(values.length == 1 && values[0] == 7);
    }
    /// @custom:key box
    function primitiveField() public {
        delete records; delete values;
        records.push(); records[0].value = 11;
        values.push(records[0].value);
        assert(values[0] == 11);
    }
    /// @custom:key box
    function primitiveFalse() public {
        delete rows; delete values;
        rows.push(); rows[0].push(7);
        values.push(rows[0][0]);
        assert(values[0] == 8);
    }
    /// @custom:key box
    function referenceCopy() public {
        delete rows; delete copies;
        rows.push(); rows[0].push(7);
        copies.push(rows[0]);
        rows[0][0] = 9;
        assert(copies[0][0] == 7);
    }
    /// @custom:key box
    function referenceFalse() public {
        delete rows; delete copies;
        rows.push(); rows[0].push(7);
        copies.push(rows[0]); rows[0][0] = 9;
        assert(copies[0][0] == 9);
    }
    /// @custom:key box
    function selfCopy() public {
        delete rows;
        rows.push(); rows[0].push(13);
        rows.push(rows[0]); rows[0][0] = 17;
        assert(rows.length == 2 && rows[1][0] == 13);
    }
    /// @custom:key box
    function effectfulSource() public {
        delete rows; delete copies;
        rows.push(); rows[0].push(19);
        uint i = 0;
        copies.push(rows[i++]);
        assert(i == 1 && copies[0][0] == 19);
    }
    /// @custom:key box
    function complexReceiver() public {
        delete rows; delete deep;
        rows.push(); rows[0].push(23); deep.push();
        deep[0].push(rows[0]);
        assert(deep[0][0][0] == 23);
    }
    /// @custom:key box
    function badSourceIndex() public {
        delete rows; delete copies;
        rows.push();
        copies.push(rows[5]);
    }
    /// @custom:key box
    function freshSourceNames() public {
        delete rows; delete values;
        rows.push(); rows[0].push(29);
        uint source2 = 0;
        source9 = 0;
        values.push(rows[source2++][source9++]);
        assert(source2 == 1 && source9 == 1 && values[0] == 29);
    }
}
