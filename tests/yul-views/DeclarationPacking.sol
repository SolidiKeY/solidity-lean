pragma solidity 0.8.38;
contract DeclarationPacking {
    struct PackedDecl { bool flag; uint16 small; bytes3 data; address who; uint256 wide; uint8 one; bytes31 full; uint16 afterValue; }
    struct Inner { bool flag; uint16 small; bytes3 data; address who; }
    struct Composite { uint24[12] values; Inner inner; }
    PackedDecl state;
    Composite composite;
    uint16 marker;
    constructor() {
        assembly ("memory-safe") {
            sstore(0, shl(208, 0xa5a5a5a5a5a5))
            sstore(3, shl(16, 0xdeadbeef))
            sstore(4, shl(240, 0xcccc))
            sstore(5, shl(48, 0xdddddddddddddddddddddddddddddddddddddddddddddddddddd))
            sstore(6, shl(208, 0xbbbbbbbbbbbb))
            sstore(7, 55)
        }
    }
    function readAll() public view returns (uint256[8] memory out) {
        assembly ("memory-safe") {
            mstore(out, sload(0)) mstore(add(out,32), sload(1)) mstore(add(out,64), sload(2)) mstore(add(out,96), sload(3))
            mstore(add(out,128), sload(4)) mstore(add(out,160), sload(5)) mstore(add(out,192), sload(6)) mstore(add(out,224), sload(7))
        }
    }
    function writeForward() external returns (uint256[8] memory) {
        state.flag=true; state.small=0x1234; state.data=0xff00aa; state.who=address(0x1234567890123456789012345678901234567890);
        state.wide=type(uint256).max; state.one=0x7f; state.full=bytes31(type(uint248).max); state.afterValue=0xbeef;
        for(uint i=0;i<12;i++) composite.values[i]=uint24(i+1);
        composite.inner.flag=true; composite.inner.small=0x2222; composite.inner.data=0x123456; composite.inner.who=address(0x42);
        return readAll();
    }
    function writeReverse() external returns (uint256[8] memory) {
        composite.inner.who=address(0x43); composite.inner.data=0xabcdef; composite.inner.small=0x3333; composite.inner.flag=false;
        for(uint i=12;i>0;i--) composite.values[i-1]=uint24(i+100);
        state.afterValue=0xcafe; state.full=bytes31(uint248(1)); state.one=0x80; state.wide=1;
        state.who=address(0xABcdEFABcdEFabcdEfAbCdefabcdeFABcDEFabCD); state.data=0x112233; state.small=0xbeef; state.flag=false;
        return readAll();
    }
    function failAfterWrite() external { state.small=99; composite.values[0]=99; revert("packing"); }
}
