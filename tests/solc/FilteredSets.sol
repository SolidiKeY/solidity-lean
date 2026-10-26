// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

contract FilterConstants {
    uint constant N = 99;
}

contract FilteredSets is FilterConstants {
    uint value;

    /// @custom:key requires x \in uint(k; 1, 2, 2; k > 1)
    /// @custom:key ensures \result == 2
    function echo(uint x) public pure returns (uint) { return x; }

    /// @custom:key ensures \result \in int(k; -2, -1, 0; k < 0)
    function negative() public pure returns (int) { return -1; }

    /// @custom:key ensures \result \in bool(k; false, true; k)
    function truth() public pure returns (bool) { return true; }

    /// @custom:key requires account == address(7)
    /// @custom:key ensures account \in address(a; 7, 9; a == 7)
    function addressChoice(address account) public pure {}

    /// @custom:key ensures !(1 \in uint(k; ; k > 0))
    function empty() public pure {}

    /// @custom:key ensures !(1 \in uint(k; 1, 2; false))
    function falseGuard() public pure {}

    /// @custom:key ensures 2 \in uint(k; 1, 2, 2; true)
    function duplicate() public pure {}

    /// @custom:key requires from == 2
    /// @custom:key ensures from \in uint(from; 1, 2; from == 2)
    function outerKey(uint from) public pure {}

    /// @custom:key requires from == 1
    /// @custom:key ensures (from + 1) \in uint(from; 2; from == 2)
    function outerGuard(uint from) public pure {}

    /// @custom:key requires from == 1
    /// @custom:key ensures (from + 1) \in uint(from; 2; from == 1)
    function falseOuterGuard(uint from) public pure {}

    /// @custom:key requires $x == 2
    /// @custom:key ensures $x \in uint($x; 1, 2; $x > 1)
    function dollars(uint $x) public pure {}

    /// @custom:key ensures 2 \in uint(N; 1, 2; N == 2)
    function inheritedConstantShadow() public pure {}

    /// @custom:key ensures 1 \in uint(value; 1; value == 1)
    function stateNameShadow() public pure {}

    /// @custom:key ensures 1 \in uint(k; 1; \result == 2 && k == 1)
    function resultReference() public pure returns (uint) { return 2; }

    /// @custom:key ensures \forall uint x; x < 2 -> x \in uint(x; 0, 1; x < 2)
    function quantifiedShadow() public pure {}

    /// @custom:key ensures 2 \in uint(x; 1, 2; x \in uint(x; 2; x == 2))
    function nested() public pure {}

    /// @custom:key requires value == 1
    /// @custom:key ensures value \in uint(k; 2; \old(value) == k - 1)
    function oldGuard() public { value = 2; }

    /// @custom:key requires value == 1
    /// @custom:key ensures \old(value \in uint(k; 1; k == value))
    function oldWhole() public { value = 2; }

    /// @custom:key requires value == 1
    /// @custom:key ensures \old(value) \in uint(k; 1; k < value)
    function oldKey() public { value = 2; }

    /// @custom:key ensures 1 \in uint(k; 1; \old(net(msg.sender)) == \old(net(msg.sender)) && k == 1)
    function oldLedger() public pure {}

    /// @custom:key ensures !(1 / 0 \in uint(k; 0, 1; true))
    function undefinedKey() public pure {}

    // KeY's existing guard equality equates two undefined expressions.
    /// @custom:key ensures 1 \in uint(k; 1; (1 / 0) == (2 / 0))
    function guardTheoryEquality() public pure {}

    /// @custom:key requires flag \in bool(flag; false, true; flag)
    /// @custom:key ensures false
    function witness(bool flag) public pure {}

    /// @custom:key ensures 1 \in uint(k; 2, 3; true)
    function falsePost() public pure {}
}

contract InvalidFilteredSets {
    uint[] entries;
    mapping(uint => uint) table;
    struct Pair { uint field; }
    Pair pair;

    /// @custom:key ensures missing \in uint(k; ; true)
    function unknownEmptyKey() public pure {}

    /// @custom:key ensures 1 \in uint(k; ; missing == 1)
    function unknownEmptyGuard() public pure {}

    /// @custom:key requires 1 \in uint(k; ; \old(k) == k)
    function forbiddenOld() public pure {}

    /// @custom:key ensures 1 \in uint(k; ; \old(\old(k)) == k)
    function nestedOld() public pure {}

    /// @custom:key ensures 1 \in uint(k; ; k + 1)
    function numericGuard() public pure {}

    /// @custom:key ensures 1 \in uint(k; x; true)
    function dynamicDomain(uint x) public pure {}

    /// @custom:key ensures 1 \in uint(x; x; true)
    function capturedDomain(uint x) public pure {}

    /// @custom:key ensures 1 \in uint(k; 1 + 0; true)
    function arithmeticDomain() public pure {}

    /// @custom:key ensures 0 \in uint(k; net(msg.sender); true)
    function ledgerDomain() public pure {}

    /// @custom:key ensures net(msg.sender) \in uint(k; ; true)
    function ledgerKey() public pure {}

    /// @custom:key ensures 0 \in uint(k; -1; true)
    function negativeUint() public pure {}

    /// @custom:key ensures 0 \in int(k; uint(1); true)
    function fixedMixed() public pure {}

    /// @custom:key ensures 0 \in uint(k; true; true)
    function mixedBool() public pure {}

    /// @custom:key ensures true \in bool(k; 0; true)
    function numericBool() public pure {}

    /// @custom:key ensures 0 \in uint(k; 115792089237316195423570985008687907853269984665640564039457584007913129639936; true)
    function largeDomain() public pure {}

    /// @custom:key ensures 115792089237316195423570985008687907853269984665640564039457584007913129639936 \in uint(k; ; true)
    function largeEmptyKey() public pure {}

    /// @custom:key ensures entries \in uint(k; ; true)
    function referenceKey() public view {}

    /// @custom:key ensures 1 \in uint(k; ; \old(items[0]) == k)
    function oldMemory(uint[] memory items) public pure {}

    /// @custom:key ensures 1 \in uint(entries; 1; entries.length == entries.length)
    function shadowedArrayLength() public view {}

    /// @custom:key ensures 1 \in uint(entries; ; entries.length == entries.length)
    function shadowedEmptyArrayLength() public view {}

    /// @custom:key ensures 1 \in uint(table; 1; table[0] == table[0])
    function shadowedMapping() public view {}

    /// @custom:key ensures 1 \in uint(pair; 1; pair.field == pair.field)
    function shadowedStruct() public view {}

    /// @custom:key ensures 1 \in uint(items; 1; items.length == items.length)
    function shadowedMemory(uint[] memory items) public pure {}

    /// @custom:key ensures 1 \in uint(result; 1; \result == 1)
    function reservedResult() public pure returns (uint) { return 2; }

    /// @custom:key ensures 1 \in uint(old; 1; true)
    function reservedOld() public pure {}

    /// @custom:key ensures 1 \in uint(oldNet; 1; true)
    function reservedOldNet() public pure {}

    /// @custom:key ensures 1 \in uint(result_first; 1; first == 1)
    function reservedNamedReturn() public pure returns (uint first, uint second) { return (2, 3); }

    /// @custom:key ensures 1 \in uint(k; 1; \exists uint result; \result == 1)
    function nestedReservedResult() public pure returns (uint) { return 2; }

    function loopBoundary() public pure {
        uint x;
        /// @custom:key invariant x \in uint(k; 0, 1; k < 2)
        while (x < 1) { x++; }
    }
}
