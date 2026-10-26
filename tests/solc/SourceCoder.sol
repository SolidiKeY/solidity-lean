// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;
pragma abicoder v1;
contract SourceCoder {
    function decode(bytes memory data) public pure returns (uint8) {
        return abi.decode(data, (uint8));
    }
}
