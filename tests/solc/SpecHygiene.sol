// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

contract SpecHygiene {
    uint value;
    uint[] entries;
    mapping(uint => uint) table;
    struct Pair { uint field; }
    Pair pair;

    /// @custom:key ensures \forall uint value; value == value
    function stateNameShadow() public pure {}

    /// @custom:key ensures \exists uint entries; entries == 1
    function arrayNameShadow() public pure {}

    /// @custom:key ensures \forall uint from; from == from
    function parameterShadow(uint from) public pure {}

    /// @custom:key ensures \exists uint x; x == 1 && \result == 2
    function resultReference() public pure returns (uint) { return 2; }

    /// @custom:key ensures \exists uint first; first == 1 && second == 3
    function namedReturnShadow() public pure returns (uint first, uint second) { return (2, 3); }

    /// @custom:key requires value == 1
    /// @custom:key ensures \exists uint x; x == 1 && \old(value) == x && value == 2
    function snapshotReference() public { value = 2; }

    /// @custom:key ensures \forall uint x; (\exists uint x; x == 1) && \result == 2
    function nestedShadow() public pure returns (uint) { return 2; }

    /// @custom:key ensures \forall uint x; x == x && \result == 1
    function falseResult() public pure returns (uint) { return 2; }

    /// @custom:key ensures \exists uint result; result == 1 && \result == 1
    function captureResult() public pure returns (uint) { return 2; }

    /// @custom:key ensures \exists uint result_first; result_first == 1 && first == 1
    function captureNamedReturn() public pure returns (uint first, uint second) { return (2, 3); }

    /// @custom:key ensures \exists uint old; old == 1 && \old(value) == 1
    function captureOld() public view {}

    /// @custom:key ensures \exists uint oldNet; oldNet == 1 && \old(net(msg.sender)) == 0
    function captureOldNet() public pure {}

    /// @custom:key ensures \forall uint x; \exists uint result; result == 1 && \result == 1
    function captureNestedResult() public pure returns (uint) { return 2; }

    /// @custom:key ensures \exists uint result; false
    function reservedFalseBody() public pure {}

    /// @custom:key ensures \forall uint result; true
    function reservedVacuousBody() public pure {}

    /// @custom:key ensures \forall uint entries; entries.length == entries.length
    function arrayLength() public view {}

    /// @custom:key ensures \exists uint entries; false && entries.length == entries.length
    function arrayFalseGuard() public view {}

    /// @custom:key ensures \forall uint entries; false -> entries.length == entries.length
    function arrayEmptyGuard() public view {}

    /// @custom:key ensures \forall uint entries; entries[0] == entries[0]
    function arrayIndex() public view {}

    /// @custom:key ensures \exists uint table; table[0] == table[0]
    function mappingIndex() public view {}

    /// @custom:key ensures \forall uint table; false -> table[0] == table[0]
    function mappingEmptyGuard() public view {}

    /// @custom:key ensures \forall uint pair; pair.field == pair.field
    function structField() public view {}

    /// @custom:key ensures \exists uint pair; false && pair.field == pair.field
    function structFalseGuard() public view {}

    /// @custom:key ensures \forall uint items; items.length == items.length
    function memoryLength(uint[] memory items) public pure {}

    /// @custom:key ensures \exists uint items; false && items[0] == items[0]
    function memoryFalseGuard(uint[] memory items) public pure {}

    /// @custom:key ensures \forall uint items; false -> items.length == items.length
    function memoryEmptyGuard(uint[] memory items) public pure {}
}
