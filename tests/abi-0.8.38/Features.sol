// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

contract ABIConformance {
    uint constant ROOT = erc7201("openzeppelin.storage.ERC20");
    function f(uint x) public pure returns (uint) { return x; }
    function g(bytes2 x) external pure returns (bytes2) { return x; }
    function constantRoot() external pure returns (uint) { return ROOT; }
    function runtimeRoot(string memory id) external pure returns (uint) { return erc7201(id); }
    function fixedLiteral() external view returns (uint n, uint a, uint b, uint z) {
        bytes memory e = abi.encodeCall(this.g, ("ab"));
        return (e.length, uint8(e[4]), uint8(e[5]), uint8(e[35]));
    }
    function externalValue() external view returns (bool) {
        function(uint) external pure returns(uint) h = this.f;
        bytes memory e = abi.encode(h);
        bytes memory p = abi.encodePacked(h);
        return e.length == 32 && p.length == 24 && e[23] == p[23] &&
            uint8(e[24]) == 0 && uint8(e[31]) == 0;
    }
    function unicodeSelector() external pure returns (uint, uint, uint, uint, bool) {
        string memory s = unicode"é()";
        bytes memory e = abi.encodeWithSignature(unicode"é()", 7);
        bytes memory r = abi.encodeWithSignature(s, 7);
        return (uint8(e[0]), uint8(e[1]), uint8(e[2]), uint8(e[3]),
            e[0] == r[0] && e[1] == r[1] && e[2] == r[2] && e[3] == r[3]);
    }
    function nestedPrefix() external pure returns (uint, uint, uint) {
        uint[][] memory xs = new uint[][](1);
        xs[0] = new uint[](1); xs[0][0] = 7;
        bytes memory e = abi.encodeWithSelector(bytes4(0x12345678), xs, uint(9));
        return (e.length, uint8(e[35]), uint8(e[195]));
    }
    function hugeNestedHead() external pure returns (uint) {
        uint[][] memory xs = abi.decode(abi.encode(uint(32), type(uint).max), (uint[][]));
        return xs.length;
    }
    function unaligned() external pure returns (uint) {
        bytes memory e = new bytes(65); e[31] = bytes1(uint8(33));
        return abi.decode(e, (bytes)).length;
    }
    function overlapping() external pure returns (uint) {
        return abi.decode(abi.encode(uint(0)), (bytes)).length;
    }
    function trueProperty() external pure { assert(ROOT == 0x52c63247e1f47db19d5ce0460030c497f067ca4cebf71ba98eeadabe20bace00); }
    function recovery(bytes32 h, uint8 v, bytes32 r, bytes32 s) external pure returns (address) {
        return ecrecover(h, v, r, s);
    }
    function falseProperty() external pure { assert(ROOT == 0); }
}
