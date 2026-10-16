// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
contract MappingPush {
    mapping(uint => uint)[] maps;
    function boundPushDiamond() public {
        mapping(uint => uint) storage m = maps.push();
        m[1] = 7;
        assert(m[1] == 7);
    }
    /// @custom:key box
    function barePushKeepsEntries() public {
        delete maps;
        maps.push();
        maps[0][1] = 5;
        maps.pop();
        maps.push();
        assert(maps[0][1] == 5);
    }
    /// @custom:key box
    function boundPushKeepsEntries() public {
        delete maps;
        maps.push();
        maps[0][1] = 7;
        maps.pop();
        mapping(uint => uint) storage m = maps.push();
        assert(m[1] == 7);
        m[2] = 9;
        assert(maps[0][2] == 9);
    }
}
