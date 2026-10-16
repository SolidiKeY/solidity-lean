// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract NetAssignable {
    uint count;
    uint net;

    /// @custom:key ensures true
    /// @custom:key assignable net(msg.sender)
    function ledgerGap() public pure { assert(false); }

    /// @custom:key ensures true
    /// @custom:key assignable count, net (msg.sender)
    function mixedGap() public { count = 1; assert(false); }

    function callerGap() public pure { ledgerGap(); }

    function unrelated() public pure { assert(true); }
    function falseUnrelated() public pure { assert(false); }

    /// @custom:key ensures net == 1
    /// @custom:key assignable net
    function bareStateName() public { net = 1; }
}

contract ConstantNetAssignable {
    uint constant net = 1;

    /// @custom:key ensures net == 1 && net(msg.sender) == \old(net(msg.sender))
    function builtinLedger() public pure {}

    /// @custom:key ensures net(msg.sender) == \old(net(msg.sender)) + 1
    function falseBuiltinLedger() public pure {}

    /// @custom:key ensures true
    /// @custom:key assignable net(msg.sender)
    function constantLedgerGap() public pure { assert(false); }
}

contract ConstantBuiltinNames {
    uint constant old = 2;
    uint constant result = 3;
    uint count;

    /// @custom:key ensures old == 2 && result == 3 && \old(count) == count && \result == 7
    function builtinEscapes() public pure returns (uint value) { return 7; }
}
