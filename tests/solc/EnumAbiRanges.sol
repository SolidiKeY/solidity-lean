pragma solidity ^0.8.0;
library EnumAbi { enum E { A, B } }
contract EnumAbiRanges {
    function read(EnumAbi.E value) public pure returns (uint) { return uint(value); }
    function check() public pure { assert(read(EnumAbi.E.B) == 1); }
}
contract EnumAbiCtorRanges {
    uint saved;
    constructor(EnumAbi.E value) { saved = uint(value); }
    function read() public view returns (uint) { return saved; }
}
