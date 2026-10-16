// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract SpecSelf {
    /// @custom:key ensures this == address(this)
    function identity() public pure {}

    /// @custom:key ensures \old(this) == this
    function snapshot() public pure {}

    /// @custom:key ensures net(this) == \old(net(this))
    function unchangedLedger() public pure {}

    /// @custom:key requires account == address(this)
    /// @custom:key ensures account == this
    function parameter(address account) public pure {}

    /// @custom:key ensures result == this
    function returned() public view returns (address result) { return address(this); }

    /// @custom:key ensures this == 0
    function falseAddress() public pure {}

    /// @custom:key ensures net(this) == \old(net(this)) + 1
    function falseLedger() public pure {}
}
