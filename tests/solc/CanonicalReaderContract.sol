// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.0;

/// CR canonical-reader contract probes (H68). Each function is one supported
/// shape of the existing `solc_import` route; the control records whether the
/// canonical executable reader admits it from the same JSON.
contract CanonicalReaderContract {
    function wide(uint256 x) public pure returns (uint256) {
        return x + 1;
    }

    function narrowParam(uint8 x) public pure returns (uint8) {
        return x;
    }

    function narrowLocal(uint256 x) public pure returns (uint256) {
        uint8 y = 3;
        return x + y;
    }

    function signedWide(int256 x) public pure returns (int256) {
        return -x;
    }

    function flag(bool b) public pure returns (bool) {
        return !b;
    }

    function memoryArray(uint256 n) public pure returns (uint256) {
        uint256[] memory xs = new uint256[](n);
        return xs.length;
    }
}
