object "PushHelpers" {
    code {
        function cleanup_t_uint256(value) -> cleaned {
            cleaned := value
        }

        function panic_error_0x41() {
            mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
            mstore(4, 0x41)
            revert(0, 0x24)
        }

        function panic_error_0x32() {
            mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
            mstore(4, 0x32)
            revert(0, 0x24)
        }

        function array_length_t_array$_t_uint256_$dyn_storage_ptr(value) -> length {

            length := sload(value)

        }

        function array_dataslot_t_array$_t_uint256_$dyn_storage_ptr(ptr) -> data {
            data := ptr

            mstore(0, ptr)
            data := keccak256(0, 0x20)

        }

        function storage_array_index_access_t_array$_t_uint256_$dyn_storage_ptr(array, index) -> slot, offset {
            let arrayLength := array_length_t_array$_t_uint256_$dyn_storage_ptr(array)
            if iszero(lt(index, arrayLength)) { panic_error_0x32() }

            let dataArea := array_dataslot_t_array$_t_uint256_$dyn_storage_ptr(array)
            slot := add(dataArea, mul(index, 1))
            offset := 0

        }

        function shift_left_dynamic(bits, value) -> newValue {
            newValue :=

            shl(bits, value)

        }

        function update_byte_slice_dynamic32(value, shiftBytes, toInsert) -> result {
            let shiftBits := mul(shiftBytes, 8)
            let mask := shift_left_dynamic(shiftBits, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
            toInsert := shift_left_dynamic(shiftBits, toInsert)
            value := and(value, not(mask))
            result := or(value, and(toInsert, mask))
        }

        function identity(value) -> ret {
            ret := value
        }

        function convert_t_uint256_to_t_uint256(value) -> converted {
            converted := cleanup_t_uint256(identity(cleanup_t_uint256(value)))
        }

        function prepare_store_t_uint256(value) -> ret {
            ret := value
        }

        function update_storage_value_t_uint256_to_t_uint256(slot, offset, value_0) {
            let convertedValue_0 := convert_t_uint256_to_t_uint256(value_0)
            sstore(slot, update_byte_slice_dynamic32(sload(slot), offset, prepare_store_t_uint256(convertedValue_0)))
        }

        function array_push_from_t_uint256_to_t_array$_t_uint256_$dyn_storage_ptr(array , value0) {

            let oldLen := sload(array)
            if iszero(lt(oldLen, 18446744073709551616)) { panic_error_0x41() }
            sstore(array, add(oldLen, 1))
            let slot, offset := storage_array_index_access_t_array$_t_uint256_$dyn_storage_ptr(array, oldLen)
            update_storage_value_t_uint256_to_t_uint256(slot, offset , value0)

        }
    }
}
