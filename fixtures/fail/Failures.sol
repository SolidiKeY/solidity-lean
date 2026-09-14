// SPDX-License-Identifier: MIT
pragma solidity 0.8.33;

// Scalar-slice adaptation of viper/soldity's Failures.sol: every function panics from some
// type-correct entry state, so every root must FAIL to verify. `signedDivisionOverflow` is kept
// to pin the `unsupported` verdict for signed division.
contract Failures {
    uint8 counter;

    function unsafeAssertion(bool condition) public pure {
        assert(condition);
    }

    function overflow(uint8 value) public pure returns (uint8) {
        return value + 1;
    }

    function underflow(uint8 value) public pure returns (uint8) {
        return value - 1;
    }

    function multiplicationOverflow(uint8 value) public pure returns (uint8) {
        return value * 2;
    }

    function divisionByZero(uint8 value) public pure returns (uint8) {
        return 10 / value;
    }

    function moduloByZero(uint8 value) public pure returns (uint8) {
        return 10 % value;
    }

    function negationOverflow(int8 value) public pure returns (int8) {
        return -value;
    }

    function signedDivisionOverflow(int8 value, int8 divisor) public pure returns (int8) {
        require(divisor != 0);
        return value / divisor;
    }

    function arbitraryStateIsNotConstructorState() public view {
        assert(counter == 0);
    }
}
