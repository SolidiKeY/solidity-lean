// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract ArrayMappingShapes {
    mapping(uint => uint[3]) byKey;
    mapping(uint => uint[3])[] rows;

    function deleteKeyResetsFixedValue() public {
        byKey[7][2] = 19;
        byKey[8][1] = 23;
        delete byKey[7];
        assert(byKey[7].length == 3);
        assert(byKey[7][2] == 0);
        assert(byKey[8][1] == 23);
    }

    function deleteNestedKeyResetsOnlyItsValue() public {
        delete rows;
        rows.push();
        rows[0][7][2] = 19;
        rows[0][8][1] = 23;
        delete rows[0][7];
        assert(rows.length == 1);
        assert(rows[0][7].length == 3);
        assert(rows[0][7][2] == 0);
        assert(rows[0][8][1] == 23);
    }

    function popPushKeepsMappingFixedValues() public {
        delete rows;
        rows.push();
        rows[0][7][2] = 19;
        rows.pop();
        rows.push();
        assert(rows[0][7].length == 3);
        assert(rows[0][7][2] == 19);
    }

    function deleteArrayKeepsMappingFixedValues() public {
        delete rows;
        rows.push();
        rows[0][7][2] = 19;
        delete rows;
        rows.push();
        assert(rows[0][7].length == 3);
        assert(rows[0][7][2] == 19);
    }
}
