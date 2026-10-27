pragma solidity >=0.8.38;
error E(uint256 a, uint256 b);
error S(int8 a, int16 b);
error D(string a, bytes b, uint256 c);
error Stored(bytes a, uint256 b);
contract NamedErrorControls {
    uint n;
    bytes data = hex"61";
    function size() external view returns(uint) { return data.length; }
    function clear() internal returns(uint) { delete data; return 7; }
    function storageNamed() external { revert Stored({a: data, b: clear()}); }
    function storageReverse() external { revert Stored({b: clear(), a: data}); }
    function get() external view returns (uint) { return n; }
    function mark(uint x) internal returns (uint) { n = n * 10 + x; return n; }
    function named() external { revert E({b: mark(1), a: mark(2)}); }
    function signed() external pure { revert S({b: -257, a: -1}); }
    function dynamicData() external pure { revert D({b: hex"deadbeef", c: 300, a: "abc"}); }
    function badA() internal pure returns (uint) { assert(false); return 0; }
    function badD(uint x) internal pure returns (uint) { return 1 / x; }
    function compete() external pure { revert E({b: badA(), a: badD(0)}); }
    function context() external payable returns (uint) { return uint160(msg.sender) + msg.value; }
    function small(uint8 a, uint8 b) external pure returns(uint8) { return a ** b; }
    function uncheckedPower(uint a, uint b) external pure returns(uint) { unchecked { return a ** b; } }
    function unsignedNot(uint8 a) external pure returns(uint8) { return ~a; }
    function literal1() external pure returns(bytes1) { return ~bytes1(hex"ff"); }
    function literal16() external pure returns(bytes16) { return ~bytes16(hex"00"); }
    function literal32() external pure returns(bytes32) { return ~bytes32(hex"ff"); }
    function nested() external pure returns(bytes32) { return bytes32(~bytes16(bytes25(hex"1234"))); }
    function power(uint a, uint b) external pure returns (uint) { return a ** b; }
    function powerBase() external pure returns (uint) { return badA() ** 0; }
    function powerExponent() external pure returns (uint) { return 1 ** badD(0); }
    function powerCompete() external pure returns (uint) { return badA() ** badD(0); }
    function modular(uint k) external pure returns (uint) { return addmod(badA(), badD(0), k); }
    function complement(bytes25 x) external pure returns (bytes25) { return ~x; }
    function literal25() external pure returns (bytes25) { return ~bytes25(hex"ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff"); }
}
