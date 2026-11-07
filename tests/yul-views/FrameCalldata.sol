// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;
contract FrameCalldata {
    function copyThree(uint256 source,bool empty) external pure returns
        (bytes memory b,bytes memory aliasView,bytes32 raw,bytes32 digest,uint256 inputSize,bool freeSame,bool zeroSame)
    {
        b=new bytes(3);aliasView=b;
        assembly ("memory-safe") {
            let data := add(b,32)
            mstore(data,0x112233a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            let freeBefore := mload(64)
            let zeroBefore := mload(96)
            let size := 3
            if empty { size := 0 }
            calldatacopy(add(data,3),source,size)
            raw := mload(data)
            digest := keccak256(add(data,3),size)
            inputSize := calldatasize()
            freeSame := eq(freeBefore,mload(64))
            zeroSame := eq(zeroBefore,mload(96))
        }
    }
}
