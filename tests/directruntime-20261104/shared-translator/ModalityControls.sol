// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;
contract ModalityControls {
    /// @custom:key box
    function normalBox() public pure { assert(true); }
    function normalDiamond() public pure { assert(true); }
    /// @custom:key box
    function revertBox() public pure { require(false); }
    function revertDiamond() public pure { require(false); }
    /// @custom:key box
    function panicBox() public pure { assert(false); }
    function panicDiamond() public pure { assert(false); }
}
