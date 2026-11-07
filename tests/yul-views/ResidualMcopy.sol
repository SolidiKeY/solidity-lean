// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

// Finite chronological-copy observations, not whole memory-safe adequacy.
contract ResidualMcopy {
    uint256 private marker;
    function readState() external view returns (uint256) { return marker; }
    function run(uint256 mode, bool fail) external returns
        (bytes memory b, bytes memory aliasView, bytes32 raw, bool freeSame, bool zeroSame)
    {
        marker += 1;
        b = new bytes(3);
        aliasView = b;
        assembly ("memory-safe") {
            let data := add(b,32)
            mstore(data,0x112233a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            let freeBefore := mload(64)
            let zeroBefore := mload(96)
            switch mode
            case 3 {
                mcopy(add(data,3),add(data,4),3)
                mcopy(add(data,4),add(data,3),3)
                mcopy(add(data,3),data,3)
            }
            default {
                mcopy(add(data,3),data,3)
                if gt(mode,0) { mcopy(add(data,4),add(data,3),3) }
                if gt(mode,1) { mcopy(add(data,3),add(data,4),3) }
            }
            mcopy(96,not(0),0)
            raw := mload(data)
            freeSame := eq(freeBefore,mload(64))
            zeroSame := eq(zeroBefore,mload(96))
        }
        require(!fail,"copies");
    }
    function staticProbe() external view returns (bool ok, bytes memory data) {
        return address(this).staticcall(abi.encodeCall(this.run,(2,false)));
    }
}
