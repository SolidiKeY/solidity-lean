// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;
contract ControlTupleFailureAlias {
    uint[2] values;
    function stableAlias() external returns (uint) {
        (values[0], values[0]) = (1, 2); return values[0];
    }
    function dynamicAlias(uint i) external returns (uint) {
        (values[i], values[i]) = (1, 2); return values[i];
    }
    function discardedFailure(uint n) external pure returns (uint a) {
        (, a) = (8 / n, 2);
    }
}
