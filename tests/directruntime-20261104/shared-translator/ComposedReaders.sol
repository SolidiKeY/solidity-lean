// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;
contract ComposedReaders {
    uint256[2] stored;
    function memoryAlias() public pure {
        uint256[] memory a = new uint256[](2);
        a[0] = 1;
        uint256[] memory b = a;
        b[0] = 7;
        { uint256[] memory a = new uint256[](1); a[0] = 3; }
        assert(a[0] == 7);
    }
    function storageCopy() public {
        uint256[2] storage s = stored;
        s[0] = 3;
        uint256[2] memory copy = stored;
        copy[0] = 8;
        assert(stored[0] == 3 && copy[0] == 8);
    }
    function tupleOrder() public pure {
        uint256 a = 1; uint256 b = 2;
        (a, b) = (b, a);
        assert(a == 2 && b == 1);
        (uint256 x, , uint256 y) = (3, 4, 5);
        assert(x == 3 && y == 5);
        (a, a) = (6, 7);
        assert(a == 6);
    }
    function executeFirst() public pure {
        uint256 x = 0;
        /// @custom:key unwind 1
        do { x = x + 1; } while (false);
        assert(x == 1);
    }
    function wrongTupleOrder() public pure {
        uint256 a; (a, a) = (6, 7); assert(a == 7);
    }
    function falseControl() public pure {
        uint256[] memory a = new uint256[](1);
        a[0] = 1; assert(a[0] == 2);
    }
    function discardedFailure() public pure {
        uint256 zero = 0; uint256 a;
        (, a) = (1 / zero, 1);
    }
    function pair() internal pure returns (uint256, uint256) { return (1, 2); }
    function unsupportedCallTuple() public pure { (uint256 a, uint256 b) = pair(); }
    function unsupportedReference(uint256[] memory input) public pure { assert(input.length >= 0); }
    function unsupportedInlineArray() public pure { uint256[2] memory a = [uint256(1), 2]; }
    function unsupportedDiscardRead() public pure {
        uint256[] memory a = new uint256[](1); uint256 b;
        (, b) = (a.length, 1);
    }
    function discardedReadFailure() public pure {
        uint256[] memory a = new uint256[](1); uint256 b;
        (, b) = (a[2], 1);
    }
}
