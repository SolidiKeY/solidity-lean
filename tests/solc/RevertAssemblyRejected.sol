// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

contract RevertAssemblyRejected {
    function wrongOffset(bytes memory data) public pure {
        assembly { revert(add(data, 64), mload(data)) }
    }

    function differentLength(bytes memory data, bytes memory other) public pure {
        assembly { revert(add(data, 32), mload(other)) }
    }

    function extraStatement(bytes memory data) public pure {
        assembly { pop(mload(data)) revert(add(data, 32), mload(data)) }
    }

    function wordArray(uint[] memory data) public pure {
        assembly { revert(add(data, 32), mload(data)) }
    }

    function renamed() public pure {
        bytes memory by = hex"09";
        assembly { revert(add(by, 32), mload(by)) }
    }
}
