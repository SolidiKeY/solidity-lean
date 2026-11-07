// Source-derived finite dirty-local/physical control; pinned compiler evidence only.
pragma solidity 0.8.38;
import "./PhysicalControls.sol";
contract FunctionPhysicalControls layout at 42 is PhysicalB, PhysicalC {
    uint248 internal e;
    uint16 internal f;
    uint256 internal marker;
    uint16 transient temp;
    function peek() external view returns (bool logical, uint256 raw) {
        logical = c;
        assembly ("memory-safe") { raw := sload(c.slot) }
    }
    function first() external returns (bool logical, uint256 raw) {
        assembly ("memory-safe") { sstore(c.slot, 0xab000002) raw := sload(c.slot) }
        logical = c;
    }
    function child() external {
        assembly ("memory-safe") { sstore(c.slot, 0xcd000003) }
    }
    function outer() external {
        assembly ("memory-safe") { sstore(c.slot, 0xab000002) }
        this.child();
        assembly ("memory-safe") { mstore(0, sload(c.slot)) revert(0,32) }
    }

    function compose() external returns (uint256[9] memory) {
        bool flag = true;
        function(bool) external view returns(uint8) ptr1;
        uint8 small = 1;
        function(bool) external view returns(uint8) ptr2;
        bytes1 byteValue = 0xab;
        bytes memory memoryValue = hex"aabb";
        assembly ("memory-safe") {
            function incrementWord(x) -> result { result := add(x, 256) }
            function nestedWord(x) -> result {
                result := incrementWord(add(x, 256))
                leave
                result := 0
            }
            ptr1.address := 4660
            ptr1.selector := 0x89abcdef
            ptr2.address := 22136
            ptr2.selector := 0x01020304
            sstore(c.slot, 0xab000002)
            flag := 2
            ptr1.address := not(0)
            ptr2.selector := not(0)
            small := add(small, 256)
            for { let i := 0 } lt(i, 3) { i := add(i, 1) } { small := nestedWord(small) }
            let out := mload(0x40)
            mstore(out, flag)
            mstore(add(out, 32), ptr1.address)
            mstore(add(out, 64), ptr1.selector)
            mstore(add(out, 96), small)
            mstore(add(out, 128), ptr2.address)
            mstore(add(out, 160), ptr2.selector)
            mstore(add(out, 192), byteValue)
            mstore(add(out, 224), sload(c.slot))
            mstore(add(out, 256), shr(240, mload(add(memoryValue, 32))))
            return(out, 288)
        }
    }
    function composeWrong() external returns (uint256[9] memory) {
        bool flag = true;
        function(bool) external view returns(uint8) ptr1;
        uint8 small = 1;
        function(bool) external view returns(uint8) ptr2;
        bytes1 byteValue = 0xab;
        bytes memory memoryValue = hex"aabb";
        assembly ("memory-safe") {
            function incrementWord(x) -> result { result := add(x, 256) }
            function nestedWord(x) -> result {
                result := incrementWord(add(x, 256))
                leave
                result := 0
            }
            ptr1.address := 4660
            ptr1.selector := 0x89abcdef
            ptr2.address := 22136
            ptr2.selector := 0x01020304
            sstore(c.slot, 0xab000002)
            flag := 2
            ptr1.address := not(0)
            ptr2.selector := not(0)
            small := add(small, 256)
            for { let i := 0 } lt(i, 3) { i := add(i, 1) } { small := incrementWord(small) }
            let out := mload(0x40)
            mstore(out, flag)
            mstore(add(out, 32), ptr1.address)
            mstore(add(out, 64), ptr1.selector)
            mstore(add(out, 96), small)
            mstore(add(out, 128), ptr2.address)
            mstore(add(out, 160), ptr2.selector)
            mstore(add(out, 192), byteValue)
            mstore(add(out, 224), sload(c.slot))
            mstore(add(out, 256), shr(240, mload(add(memoryValue, 32))))
            return(out, 288)
        }
    }
    function composeNoLeave() external returns (uint256[9] memory) {
        bool flag = true;
        function(bool) external view returns(uint8) ptr1;
        uint8 small = 1;
        function(bool) external view returns(uint8) ptr2;
        bytes1 byteValue = 0xab;
        bytes memory memoryValue = hex"aabb";
        assembly ("memory-safe") {
            function incrementWord(x) -> result { result := add(x, 256) }
            function nestedWord(x) -> result {
                result := incrementWord(add(x, 256))

                result := 0
            }
            ptr1.address := 4660
            ptr1.selector := 0x89abcdef
            ptr2.address := 22136
            ptr2.selector := 0x01020304
            sstore(c.slot, 0xab000002)
            flag := 2
            ptr1.address := not(0)
            ptr2.selector := not(0)
            small := add(small, 256)
            for { let i := 0 } lt(i, 3) { i := add(i, 1) } { small := nestedWord(small) }
            let out := mload(0x40)
            mstore(out, flag)
            mstore(add(out, 32), ptr1.address)
            mstore(add(out, 64), ptr1.selector)
            mstore(add(out, 96), small)
            mstore(add(out, 128), ptr2.address)
            mstore(add(out, 160), ptr2.selector)
            mstore(add(out, 192), byteValue)
            mstore(add(out, 224), sload(c.slot))
            mstore(add(out, 256), shr(240, mload(add(memoryValue, 32))))
            return(out, 288)
        }
    }
}
