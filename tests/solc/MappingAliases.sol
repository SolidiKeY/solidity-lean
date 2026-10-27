pragma solidity ^0.8.38;
contract MappingAliases {
    mapping(uint8 => uint8) a;
    mapping(uint8 => uint8) b;
    function nested() public returns (uint8, uint8, uint8, uint8) {
        mapping(uint8 => uint8) storage m = a;
        mapping(uint8 => uint8) storage n = b;
        (m = n)[(n = a)[0]] = 7;
        return (a[0], b[0], m[0], n[0]);
    }
    function bare() public returns (uint8, uint8) {
        mapping(uint8 => uint8) storage n = b;
        n[(n = a)[0]] = 7;
        return (a[0], b[0]);
    }
    function once() public returns (uint8, uint8, uint8) {
        mapping(uint8 => uint8) storage m = a;
        uint8 i = 1;
        (m = b)[i++] = 9;
        return (a[1], b[1], i);
    }
    function overflow() public returns (uint) {
        b[0] = 255;
        mapping(uint8 => uint8) storage m = a;
        return (m = b)[0] + 1;
    }
    function value() public view returns (uint8) { return b[0]; }
}
