// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.38;

enum EntryKind { first, second, third }
type EntryInt is int256;
type EntryNarrow is int224;

contract EntryBase {
    function inherited() public pure returns (uint256) { return hidden() - 58; }
    function choose(uint8) public virtual pure returns (uint256) { return 1; }
    function hidden() internal pure returns (uint256) { return 99; }
}

contract Entrypoints is EntryBase {
    uint8 public scalar = 7;
    EntryNarrow public constant typed = EntryNarrow.wrap(17);
    int224 public constant unwrapped = EntryNarrow.unwrap(typed);
    mapping(EntryKind => uint8) public enumerated;
    mapping(EntryInt => int16) public nominalMap;
    mapping(uint256 => int16[][2]) public nested;
    mapping(uint256 => mapping(bool => uint256)) public flags;
    constructor() { nested[2][1].push(-9); flags[4][true] = 12;
        enumerated[EntryKind.third] = 13; nominalMap[EntryInt.wrap(-2)] = -9; }
    function choose(uint8) public override pure returns (uint256) { return 2; }
    function choose(uint256) public pure returns (uint256) { return 3; }
    function kind(EntryKind value) public pure returns (uint256) { return uint256(value); }
    function mutate(EntryKind value) public { scalar = 50 + uint8(value); }
    function nominal(EntryInt value) public pure returns (int256) { return EntryInt.unwrap(value); }
    EntryNarrow public constant negative = EntryNarrow.wrap(-17);
}

contract EntrypointRefusal {
    mapping(uint256 => bytes) public data;
}

contract EntrypointConstructor {
    uint256 public result;
    constructor(EntryKind value) { result = uint256(value); }
}

contract EntrypointEnumRefusal { EntryKind public value; }
