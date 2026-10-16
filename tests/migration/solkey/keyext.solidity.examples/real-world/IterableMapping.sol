// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

// Source: https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/app/iterable-mapping/IterableMapping.sol
// Changes: comments dropped. The library IterableMapping and the contract TestIterableMap are
// merged into one contract: a library call does not load (NullPointerException, and
// using-for is an unknown node), and a Map storage parameter of an internal function crashes
// the proof, so each library body is inlined into the TestIterableMap function that calls it,
// with map for the Map parameter and a local key = msg.sender for the key. Return values are
// named. The invariants state the index structure: every key is inserted and indexed at its
// position, and every inserted address sits at its index.
/// @custom:key invariant \forall address a; map.values[a] >= 0 && (!map.inserted[a] -> map.values[a] == 0)
/// @custom:key invariant \forall address a; map.inserted[a] -> map.indexOf[a] >= 0 && map.indexOf[a] < map.keys.length && map.keys[map.indexOf[a]] == a
/// @custom:key invariant \forall uint i; 0 <= i && i < map.keys.length -> map.inserted[map.keys[i]] && map.indexOf[map.keys[i]] == i
contract IterableMapping {
    struct Map {
        address[] keys;
        mapping(address => uint256) values;
        mapping(address => uint256) indexOf;
        mapping(address => bool) inserted;
    }

    Map private map;

    /// @custom:key requires val >= 0
    /// @custom:key ensures map.values[msg.sender] == val && map.inserted[msg.sender]
    /// @custom:key ensures \old(map.inserted[msg.sender]) -> map.keys.length == \old(map.keys.length)
    /// @custom:key ensures !\old(map.inserted[msg.sender]) -> map.keys.length == \old(map.keys.length) + 1 && map.keys[\old(map.keys.length)] == msg.sender && map.indexOf[msg.sender] == \old(map.keys.length)
    function setInMapping(uint256 val) public {
        address key = msg.sender;
        if (map.inserted[key]) {
            map.values[key] = val;
        } else {
            map.inserted[key] = true;
            map.values[key] = val;
            map.indexOf[key] = map.keys.length;
            map.keys.push(key);
        }
    }

    /// @custom:key ensures v == map.values[msg.sender]
    function getFromMap() public view returns (uint256 v) {
        return map.values[msg.sender];
    }

    /// @custom:key ensures k == map.keys[index]
    function getKeyAtIndex(uint256 index) public view returns (address k) {
        return map.keys[index];
    }

    /// @custom:key ensures s == map.keys.length
    function sizeOfMapping() public view returns (uint256 s) {
        return map.keys.length;
    }

    /// @custom:key ensures !map.inserted[msg.sender] && map.values[msg.sender] == 0
    /// @custom:key ensures \old(map.inserted[msg.sender]) -> map.keys.length == \old(map.keys.length) - 1
    /// @custom:key ensures !\old(map.inserted[msg.sender]) -> map.keys.length == \old(map.keys.length)
    function removeFromMapping() public {
        address key = msg.sender;
        if (!map.inserted[key]) {
            return;
        }

        delete map.inserted[key];
        delete map.values[key];

        uint256 index = map.indexOf[key];
        address lastKey = map.keys[map.keys.length - 1];

        map.indexOf[lastKey] = index;
        delete map.indexOf[key];

        map.keys[index] = lastKey;
        map.keys.pop();
    }
}
