// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

contract FiniteSets {
    uint value;

    /// @custom:key requires \in uint (x; 1, 2, 2)
    /// @custom:key ensures \in uint (\result; 1, 2)
    function echo(uint x) public pure returns (uint) { return x; }

    /// @custom:key ensures \in int (\result; -1, 0)
    function negative() public pure returns (int) { return -1; }

    /// @custom:key ensures \in bool (\result; false, true)
    function truth() public pure returns (bool) { return true; }

    /// @custom:key requires \in address (account; msg.sender, address(this))
    /// @custom:key ensures \result == account
    function addressChoice(address account) public pure returns (address) { return account; }

    /// @custom:key ensures !\in uint (1;)
    function empty() public pure {}

    /// @custom:key ensures \in uint (\result; \old(value), 7)
    function snapshot() public view returns (uint) { return value; }

    /// @custom:key requires \in uint (x; 1, 2)
    /// @custom:key ensures \in uint (value; 1, 2)
    function store(uint x) public { value = x; }

    /// @custom:key requires \in uint (from; 7, 9)
    /// @custom:key ensures \in uint (\result; 7, 9)
    function renamed(uint from) public pure returns (uint to) { to = from; }

    /// @custom:key requires \in uint ($x; 1, 2)
    /// @custom:key ensures \in uint (\result; 1, 2)
    function dollars(uint $x) public pure returns (uint) { return $x; }

    /// @custom:key ensures \forall uint from; from < 2 -> \in uint (from; 0, 1)
    function quantifiedShadow(uint from) public pure {}

    /// @custom:key ensures \in bool (net(msg.sender) >= 0; false, true)
    function ledgerComparison() public pure {}

    /// @custom:key ensures \in uint (\result; 2, 3)
    function falsePost() public pure returns (uint) { return 1; }

    /// @custom:key ensures \in uint (\result;)
    function falseEmpty() public pure returns (uint) { return 1; }
}

contract InvalidFiniteSets {
    uint[] entries;

    /// @custom:key ensures \in uint (missing;)
    function unknownEmpty() public pure {}

    /// @custom:key requires \in uint (\old(x);)
    function forbiddenOld(uint x) public pure {}

    /// @custom:key ensures \in uint (0; u, s)
    function mixed(uint u, int s) public pure {}

    /// @custom:key ensures \in int (0; uint(1), s)
    function fixedMixed(int s) public pure {}

    /// @custom:key ensures \in uint (net(msg.sender); 0)
    function ledgerKey() public pure {}

    /// @custom:key ensures \in uint (0; net(msg.sender))
    function ledgerItem() public pure {}

    /// @custom:key ensures \in bool (0; true)
    function numericBool() public pure {}

    /// @custom:key ensures \in uint (-1;)
    function negativeUint() public pure {}

    /// @custom:key ensures \in uint (115792089237316195423570985008687907853269984665640564039457584007913129639936;)
    function largeLiteral() public pure {}

    /// @custom:key ensures \in uint (0; missing)
    function unknownItem() public pure {}

    /// @custom:key ensures \in uint (entries;)
    function referenceEmpty() public view {}
}
