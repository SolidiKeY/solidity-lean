// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract SolcSmtControlFlowOpen {
    uint counter;
    bool flag;

    function gAddr() internal pure returns (address) {
        address a;
        a = address(0);
        return a;
    }

    function readValue() internal view returns (uint) {
        return msg.value;
    }

    // open: a non-payable function does not fix msg.value to 0
    /// solc: smtCheckerTests/bmc_coverage/msg_value_4.sol
    function msgValueZeroWhenNonPayable() public view {
        uint v = readValue();
        assert(v == 0);
    }

    // open: msg.value is not known to be non-negative
    /// solc: smtCheckerTests/bmc_coverage/range_check.sol
    function msgValueNonNegative() public payable {
        uint v = msg.value;
        assert(v >= 0);
    }

}
