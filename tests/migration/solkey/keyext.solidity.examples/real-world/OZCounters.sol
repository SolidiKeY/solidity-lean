// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Source: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v4.9.0/contracts/utils/Counters.sol
// Changes: comments and the require message dropped; the library is inlined into a contract that
// holds one Counter, since libraries, using-for and storage-reference struct parameters are not
// supported. unchecked wrap-around is not modelled, so increment requires the value below 2^256 - 1.
/// @custom:key invariant _counter._value >= 0
contract OZCounters {
    struct Counter {
        uint256 _value;
    }

    Counter private _counter;

    /// @custom:key ensures c == _counter._value && _counter._value == \old(_counter._value)
    function current() public view returns (uint256 c) {
        return _counter._value;
    }

    /// @custom:key requires _counter._value < 115792089237316195423570985008687907853269984665640564039457584007913129639935
    /// @custom:key ensures _counter._value == \old(_counter._value) + 1
    function increment() public {
        unchecked {
            _counter._value += 1;
        }
    }

    /// @custom:key ensures \old(_counter._value) > 0 && _counter._value == \old(_counter._value) - 1
    function decrement() public {
        uint256 value = _counter._value;
        require(value > 0);
        unchecked {
            _counter._value = value - 1;
        }
    }

    /// @custom:key ensures _counter._value == 0
    function reset() public {
        _counter._value = 0;
    }
}
