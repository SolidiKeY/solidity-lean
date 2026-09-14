// SPDX-License-Identifier: MIT
pragma solidity 0.8.33;

// Scalar-slice adaptation of viper/soldity's ControlFlow.sol: `updates` (++ in expression
// position) and `expressionTermination` (conditional expression) are outside the slice.
contract ControlFlow {
    uint8 counter = 7;

    function increment(uint8 value) private pure returns (uint8) {
        require(value < 255, "bounded");
        return value + 1;
    }

    function callsAndBranches(uint8 value, bool choose) public pure returns (uint8) {
        uint8 result = increment(value);
        if (choose) {
            assert(result > value);
        } else {
            require(result != 0);
        }
        return result;
    }

    function updates(uint8 value) external pure returns (uint8) {
        require(value < 253);
        uint8 old = value;
        value += 1;
        assert(old + 1 == value);
        value += 1;
        return value;
    }

    function terminatingPaths(bool stop) external pure {
        if (stop) {
            revert();
        }
        require(!stop);
        assert(!stop);
    }
}
