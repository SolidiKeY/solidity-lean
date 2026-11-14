// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

// Contract tails are clean, but this function has a callback reading.
contract CallbackDiscovery {
    uint storageSlot;
    /// @custom:key box
    function localKept(address target) public {
        uint local = 1;
        (bool ok, ) = payable(target).call{value: 0}("");
        assert(local == 1);
    }
}
