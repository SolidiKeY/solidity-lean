// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

// Source: https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/mapping/Mapping.sol
// Changes: comments dropped; the contract Mapping of the same file is in Mapping.sol; the get
// return value is named v.
contract NestedMapping {
    mapping(address => mapping(uint256 => bool)) public nested;

    /// @custom:key ensures v == nested[_addr1][_i]
    function get(address _addr1, uint256 _i) public view returns (bool v) {
        return nested[_addr1][_i];
    }

    /// @custom:key ensures nested[_addr1][_i] == _boo
    /// @custom:key ensures \forall address a; \forall uint j; a != _addr1 || j != _i -> nested[a][j] == \old(nested[a][j])
    function set(address _addr1, uint256 _i, bool _boo) public {
        nested[_addr1][_i] = _boo;
    }

    /// @custom:key ensures !nested[_addr1][_i]
    /// @custom:key ensures \forall address a; \forall uint j; a != _addr1 || j != _i -> nested[a][j] == \old(nested[a][j])
    function remove(address _addr1, uint256 _i) public {
        delete nested[_addr1][_i];
    }
}
