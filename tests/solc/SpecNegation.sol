// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract SpecNegation {
    uint constant FIVE = 5;

    /// @custom:key ensures -net(msg.sender) == 0 - net(msg.sender)
    function ledgerEquation() public pure {}

    /// @custom:key requires net(msg.sender) == amount
    /// @custom:key ensures -net(msg.sender) == -amount
    function unsignedNegation(uint amount) public pure {}

    /// @custom:key requires net(msg.sender) == -amount
    /// @custom:key ensures -amount == net(msg.sender)
    function reversedNegation(uint amount) public pure {}

    /// @custom:key requires net(msg.sender) == -4
    /// @custom:key ensures -net(msg.sender) == 4
    function negativeLiteral() public pure {}

    /// @custom:key requires net(msg.sender) == -amount
    /// @custom:key ensures net(msg.sender) == -\old(amount)
    function oldUnsignedNegation(uint amount) public pure {}

    /// @custom:key requires net(msg.sender) == -FIVE
    /// @custom:key ensures net(msg.sender) == -5
    function typedConstantNegation() public pure {}

    /// @custom:key requires net(msg.sender) < 0
    /// @custom:key ensures -net(msg.sender) > 0
    function negativeLedger() public pure {}

    /// @custom:key requires amount == 115792089237316195423570985008687907853269984665640564039457584007913129639935
    /// @custom:key requires net(msg.sender) == -amount
    /// @custom:key ensures -net(msg.sender) == amount
    function maximumUnsignedNegation(uint amount) public pure {}

    /// @custom:key requires amount > 0 && net(msg.sender) == amount
    /// @custom:key ensures -net(msg.sender) == amount
    function falseNegation(uint amount) public pure {}

    /// @custom:key requires amount == 115792089237316195423570985008687907853269984665640564039457584007913129639935
    /// @custom:key ensures net(msg.sender) == -(amount + 1)
    function checkedInnerArithmetic(uint amount) public pure {}
}
