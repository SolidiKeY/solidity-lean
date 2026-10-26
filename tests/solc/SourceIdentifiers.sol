// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract SourceIdentifiers {
    struct S { address sender; uint timestamp; }
    S msg;
    S block;
    uint by;
    uint $root;
    struct $Record { uint $field; }
    $Record record;
    enum $Mode { scoped, opaque }

    function require(bool) internal pure {}
    function opaque(uint $arg) internal pure returns (uint) { return $arg; }

    function noOpShadow() public pure {
        require(false);
        assert(true);
    }

    function $compute() public returns (uint $result) {
        require(false);
        msg.sender = address(7);
        block.timestamp = 9;
        uint scoped = opaque(3);
        by = scoped;
        $root = by;
        record.$field = $root;
        assert(msg.sender == address(7));
        assert(block.timestamp == 9);
        assert(record.$field == 3);
        return record.$field;
    }

    function localMagic() public pure {
        S memory msg = S(address(11), 0);
        S memory block = S(address(0), 22);
        assert(msg.sender == address(11));
        assert(block.timestamp == 22);
    }

    /// @custom:key requires $arg < 10
    /// @custom:key ensures \result == $arg
    function escapedSpec(uint $arg) public pure returns (uint $result) {
        return $arg;
    }
}

