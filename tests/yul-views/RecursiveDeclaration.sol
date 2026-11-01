// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;
contract RecursiveDeclaration {
    struct Inner { bool flag; uint16 small; }
    struct Recursive { Inner[2][2] grid; uint128[3] values; }
    uint256[8] prefix;
    Recursive state;
    uint256 marker;
    constructor() {
        prefix[0] = 777; prefix[7] = 888; marker = 55;
        assembly ("memory-safe") {
            sstore(8, 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb000000)
            sstore(9, 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb000000)
            sstore(10, 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb000000)
            sstore(11, 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb000000)
            sstore(12, 0)
            sstore(13, 0xdddddddddddddddddddddddddddddddd00000000000000000000000000000000)
        }
    }
    function readAll() public view returns (uint256[20] memory out) {
        assembly ("memory-safe") {
            mstore(out, sload(8)) mstore(add(out,32), sload(9))
            mstore(add(out,64), sload(10)) mstore(add(out,96), sload(11))
            mstore(add(out,128), sload(12)) mstore(add(out,160), sload(13))
        }
        out[6]=marker; out[7]=prefix[0]; out[8]=prefix[7];
        for (uint i=0; i<2; i++) for (uint j=0; j<2; j++) {
            Inner storage p=state.grid[i][j]; uint k=9+(2*i+j)*2;
            out[k]=p.flag?1:0; out[k+1]=p.small;
        }
        for(uint i=0;i<3;i++) out[17+i]=state.values[i];
    }
    function writeForward() external returns(uint256[20] memory) { write(false); return readAll(); }
    function writeReverse() external returns(uint256[20] memory) { write(true); return readAll(); }
    function write(bool reverse) internal {
        for(uint z=0;z<4;z++) {
            uint n=reverse?3-z:z;
            Inner storage p=state.grid[n/2][n%2];
            p.flag=!reverse; p.small=uint16((reverse?0x3333:0x2222)+n);
        }
        for(uint z=0;z<3;z++) { uint n=reverse?2-z:z; state.values[n]=uint128((reverse?101:1)+n); }
    }
    function failAfterWrite() external { write(false); revert("recursive"); }
}
