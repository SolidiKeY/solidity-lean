// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;
import "HeapBytes.sol";

// Explicit finite allocation/alias evidence, not frontend or allocator adequacy.
contract ObjectAllocation is HeapBytes {
    struct Box { bool flag; uint number; bytes left; bytes right; bytes[] children; }
    uint public marker = 777;
    function setup() internal pure returns (Box memory x, Box[] memory xs, bytes memory a, string memory b, bytes memory c) {
        assembly ("memory-safe") {
            // Finite fixture lease above the compiler's small default prelude.
            // This guard is not an allocation/profile bound in the Lean model.
            if gt(mload(0x40), 4096) { revert(0, 0) }
            a := 4096
            b := 4224
            c := 4352
            let children := 4480
            x := 4576
            xs := 4736
            mstore(0x40, 4832)
            mstore(a, 3)
            mstore(add(a, 32), 0x112233a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(add(a, 64), 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(b, 33)
            mstore(add(b, 32), 0x6161616161616161616161616161616161616161616161616161616161616161)
            mstore(add(b, 64), 0x61a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(add(b, 96), 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(c, 3)
            mstore(add(c, 32), 0xeeddcca5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(add(c, 64), 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(children, 2)
            mstore(add(children, 32), a)
            mstore(add(children, 64), a)
            mstore(x, 1)
            mstore(add(x, 32), 7)
            mstore(add(x, 64), a)
            mstore(add(x, 96), a)
            mstore(add(x, 128), children)
            mstore(xs, 2)
            mstore(add(xs, 32), x)
            mstore(add(xs, 64), x)
        }
    }
    function snapshot(Box memory x, Box[] memory xs, bytes memory a, string memory b, bytes memory c, uint tag)
        internal view returns (bytes memory) {
        uint viaAlias = uint8(xs[0].left[0]);
        uint typedNumber = xs[1].number;
        uint typedChildren = x.children.length;
        assembly ("memory-safe") {
            let out := mload(0x40)
            mstore(out, 32)
            mstore(add(out, 32), 992)
            let data := add(out, 64)
            mstore(data, tag)
            mstore(add(data, 32), x)
            mstore(add(data, 64), xs)
            mstore(add(data, 96), mload(xs))
            mstore(add(data, 128), mload(add(xs, 32)))
            mstore(add(data, 160), mload(add(xs, 64)))
            mstore(add(data, 192), mload(x))
            mstore(add(data, 224), mload(add(x, 32)))
            mstore(add(data, 256), mload(add(x, 64)))
            mstore(add(data, 288), mload(add(x, 96)))
            let children := mload(add(x, 128))
            mstore(add(data, 320), children)
            mstore(add(data, 352), mload(children))
            mstore(add(data, 384), mload(add(children, 32)))
            mstore(add(data, 416), mload(add(children, 64)))
            mstore(add(data, 448), mload(a))
            mstore(add(data, 480), mload(add(a, 32)))
            mstore(add(data, 512), mload(b))
            mstore(add(data, 544), mload(add(b, 32)))
            mstore(add(data, 576), mload(add(b, 64)))
            mstore(add(data, 608), mload(c))
            mstore(add(data, 640), mload(add(c, 32)))
            mstore(add(data, 672), mload(0x40))
            mstore(add(data, 704), mload(0x60))
            mstore(add(data, 736), mload(add(a, 64)))
            mstore(add(data, 768), mload(add(b, 96)))
            mstore(add(data, 800), mload(add(c, 64)))
            mstore(add(data, 832), viaAlias)
            mstore(add(data, 864), add(add(eq(x, mload(add(xs, 32))), mul(2, eq(x, mload(add(xs, 64))))), mul(4, eq(mload(add(x, 64)), mload(add(x, 96))))))
            mstore(add(data, 896), sload(marker.slot))
            mstore(add(data, 928), typedNumber)
            mstore(add(data, 960), typedChildren)
            return(out, 1056)
        }
    }
    function run(uint mode) internal view returns (bytes memory) {
        (Box memory x, Box[] memory xs, bytes memory a, string memory b, bytes memory c) = setup();
        if (mode == 1) { xs[0].left[0] = 0x99; xs[1].number = 9; x.right[1] = 0x88; }
        if (mode == 2) { x.right[1] = 0x88; xs[1].number = 9; xs[0].left[0] = 0x99; }
        if (mode == 3) { xs[0].number = type(uint).max; }
        return snapshot(x, xs, a, b, c, mode);
    }
    function untouched() external view returns (bytes memory) { return run(0); }
    function forward() external view returns (bytes memory) { return run(1); }
    function reverse() external view returns (bytes memory) { return run(2); }
    function maxed() external view returns (bytes memory) { return run(3); }
    function panicAlias() external pure returns (uint) { (, Box[] memory xs,,,) = setup(); return xs[2].number; }
    function fail() external { marker = 888; (Box memory x, Box[] memory xs,,,) = setup(); xs[0].number = 99; require(x.number != 99, "objects"); }
    function staticProbe() external view returns (bool, uint, uint) {
        (bool ok, bytes memory data) = address(this).staticcall(abi.encodeWithSelector(this.fail.selector));
        return (ok, data.length, marker);
    }
}
