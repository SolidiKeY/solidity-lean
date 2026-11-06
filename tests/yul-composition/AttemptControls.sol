// Independent finite try/catch/raw-local/physical control. Prior sources unchanged.
pragma solidity 0.8.38;
import "./PhysicalControls.sol";
contract AttemptControls layout at 42 is PhysicalB, PhysicalC {
    uint248 internal e;
    uint16 internal f;
    uint256 internal marker;
    uint16 transient temp;
    function peek() external view returns (bool logical, uint256 raw) {
        logical = c;
        assembly ("memory-safe") { raw := sload(c.slot) }
    }
    function child() external {
        assembly ("memory-safe") { sstore(c.slot, 0xcd000003) tstore(0, 0x33) mstore(0, 0x77) log0(31, 1) }
    }
    function outer() external {
        assembly ("memory-safe") { sstore(c.slot, 0xab000002) tstore(0, 0x22) mstore(0, 0x66) log0(31, 1) }
        this.child();
        assembly ("memory-safe") { mstore(0, shl(240, 0xdead)) revert(0, 2) }
    }
    function outerEmpty() external {
        assembly ("memory-safe") { sstore(c.slot, 0xab000002) tstore(0, 0x22) mstore(0, 0x66) log0(31, 1) }
        this.child();
        assembly ("memory-safe") { revert(0, 0) }
    }
    function good() external pure { assembly ("memory-safe") { mstore(0, shl(240, 0xbeef)) return(0, 2) } }
    function outerPanic() external {
        assembly ("memory-safe") { sstore(c.slot, 0xab000002) tstore(0, 0x22) mstore(0, 0x66) log0(31, 1) }
        this.child();
        assert(false);
    }
    function caught() external returns (uint256[11] memory) {
        bool flag = true;
        function(bool) external view returns(uint8) ptr1;
        uint8 small = 1;
        function(bool) external view returns(uint8) ptr2;
        bytes1 byteValue = 0xab;
        bytes memory memoryValue = hex"aabb";
        assembly ("memory-safe") {
            ptr1.address := not(0)
            ptr1.selector := 0x89abcdef
            ptr2.address := 22136
            ptr2.selector := not(0)
            flag := 2
            small := add(small, 1792)
            sstore(marker.slot, 7)
            mstore(0, 0x55)
            log0(31, 1)
        }
        try this.outer() { revert(); }
        catch (bytes memory data) {
            assembly ("memory-safe") {
                function incrementWord(x) -> result { result := add(x, 256) }
                function nestedWord(x) -> result { result := incrementWord(add(x, 256)) leave result := 0 }
                small := add(small, mload(data))
                small := nestedWord(small)
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
                mstore(add(out, 288), mload(data))
                mstore(add(out, 320), 0)
                if mload(data) { mstore(add(out, 320), mload(add(data, 32))) }
                return(out, 352)
            }
        }
    }
    function caughtEmpty() external returns (uint256[11] memory) {
        bool flag = true;
        function(bool) external view returns(uint8) ptr1;
        uint8 small = 1;
        function(bool) external view returns(uint8) ptr2;
        bytes1 byteValue = 0xab;
        bytes memory memoryValue = hex"aabb";
        assembly ("memory-safe") {
            ptr1.address := not(0)
            ptr1.selector := 0x89abcdef
            ptr2.address := 22136
            ptr2.selector := not(0)
            flag := 2
            small := add(small, 1792)
            sstore(marker.slot, 7)
            mstore(0, 0x55)
            log0(31, 1)
        }
        try this.outerEmpty() { revert(); }
        catch (bytes memory data) {
            assembly ("memory-safe") {
                function incrementWord(x) -> result { result := add(x, 256) }
                function nestedWord(x) -> result { result := incrementWord(add(x, 256)) leave result := 0 }
                small := add(small, mload(data))
                small := nestedWord(small)
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
                mstore(add(out, 288), mload(data))
                mstore(add(out, 320), 0)
                if mload(data) { mstore(add(out, 320), mload(add(data, 32))) }
                return(out, 352)
            }
        }
    }
    function caughtPanic() external returns (uint256[11] memory) {
        bool flag = true;
        function(bool) external view returns(uint8) ptr1;
        uint8 small = 1;
        function(bool) external view returns(uint8) ptr2;
        bytes1 byteValue = 0xab;
        bytes memory memoryValue = hex"aabb";
        assembly ("memory-safe") {
            ptr1.address := not(0)
            ptr1.selector := 0x89abcdef
            ptr2.address := 22136
            ptr2.selector := not(0)
            flag := 2
            small := add(small, 1792)
            sstore(marker.slot, 7)
            mstore(0, 0x55)
            log0(31, 1)
        }
        try this.outerPanic() { revert(); }
        catch (bytes memory data) {
            assembly ("memory-safe") {
                function incrementWord(x) -> result { result := add(x, 256) }
                function nestedWord(x) -> result { result := incrementWord(add(x, 256)) leave result := 0 }
                small := add(small, mload(data))
                small := nestedWord(small)
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
                mstore(add(out, 288), mload(data))
                mstore(add(out, 320), 0)
                if mload(data) { mstore(add(out, 320), mload(add(data, 32))) }
                return(out, 352)
            }
        }
    }
    function success() external returns (uint256[11] memory) {
        bool flag = true;
        function(bool) external view returns(uint8) ptr1;
        uint8 small = 1;
        function(bool) external view returns(uint8) ptr2;
        bytes1 byteValue = 0xab;
        bytes memory memoryValue = hex"aabb";
        assembly ("memory-safe") {
            ptr1.address := not(0)
            ptr1.selector := 0x89abcdef
            ptr2.address := 22136
            ptr2.selector := not(0)
            flag := 2
            small := add(small, 1792)
            sstore(marker.slot, 7)
            mstore(0, 0x55)
            log0(31, 1)
        }
        try this.good() { assembly ("memory-safe") {
                mstore(0, 0)
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
                mstore(add(out, 288), returndatasize())
                mstore(add(out, 320), 0)
                returndatacopy(0, 0, returndatasize())
                mstore(add(out, 320), mload(0))
                return(out, 352)
        } } catch { revert(); }
    }
}
