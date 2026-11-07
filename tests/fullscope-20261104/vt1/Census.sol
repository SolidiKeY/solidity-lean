// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;
library LinkedMath {
    function twice(uint x) external pure returns (uint) { return x * 2; }
}
contract Census {
    uint public immutable seed;
    uint[] private values;
    constructor(uint initial) payable { seed = initial; values.push(initial); }
    function arithmetic(uint a, uint b) external pure returns (uint, uint) {
        return (a + b, a ** b);
    }
    function signed(int a, int b) external pure returns (int) { return a / b; }
    function push(uint value) external returns (uint) {
        values.push(value); return values[values.length - 1];
    }
    function pop() external { values.pop(); }
    function echo(bytes calldata input) external pure returns (bytes memory) { return input; }
    function linked(uint x) external view returns (uint) { return LinkedMath.twice(x) + seed; }
    function assemblyWord(uint x) external pure returns (uint r) {
        assembly ("memory-safe") { r := clz(x) }
    }
}
