// SPDX-License-Identifier: GPL-3.0
pragma solidity 0.8.38;
contract AbiIdentity {
    function route_uint() external pure returns (uint256) { return 11; }
    function route_uint256() external pure returns (uint256) { return 22; }
    function route_int() external pure returns (int256) { return 33; }
    function route_int256() external pure returns (int256) { return 44; }
}
