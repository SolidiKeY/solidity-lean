// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

// Source: https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/mapping/Mapping.sol
// Changes: comments dropped; the contract NestedMapping of the same
// file is in NestedMapping.sol; get's return value is named v. Checked arithmetic is not
// modelled, so a uint256 parameter gets a requires >= 0.
/// @custom:key invariant \forall address a; myMap[a] >= 0
contract Mapping {
    mapping(address => uint256) public myMap;

    /// @custom:key ensures v == myMap[_addr]
    function get(address _addr) public view returns (uint256 v) {
        return myMap[_addr];
    }

    /// @custom:key requires _i >= 0
    /// @custom:key ensures myMap[_addr] == _i
    /// @custom:key ensures \forall address a; a != _addr -> myMap[a] == \old(myMap[a])
    function set(address _addr, uint256 _i) public {
        myMap[_addr] = _i;
    }

    /// @custom:key ensures myMap[_addr] == 0
    /// @custom:key ensures \forall address a; a != _addr -> myMap[a] == \old(myMap[a])
    function remove(address _addr) public {
        delete myMap[_addr];
    }
}
