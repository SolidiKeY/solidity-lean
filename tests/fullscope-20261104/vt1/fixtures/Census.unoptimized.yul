
/// @use-src 0:"Census.sol"
object "Census_134" {
    code {
        /// @src 0:160:996  "contract Census {..."
        mstore(64, memoryguard(160))

        let _1 := copy_arguments_for_constructor_35_object_Census_134()
        constructor_Census_134(_1)

        let _2 := allocate_unbounded()
        codecopy(_2, dataoffset("Census_134_deployed"), datasize("Census_134_deployed"))

        setimmutable(_2, "16", mload(128))

        return(_2, datasize("Census_134_deployed"))

        function allocate_unbounded() -> memPtr {
            memPtr := mload(64)
        }

        function round_up_to_mul_of_32(value) -> result {
            result := and(add(value, 31), not(31))
        }

        function panic_error_0x41() {
            mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
            mstore(4, 0x41)
            revert(0, 0x24)
        }

        function finalize_allocation(memPtr, size) {
            let newFreePtr := add(memPtr, round_up_to_mul_of_32(size))
            // protect against overflow
            if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { panic_error_0x41() }
            mstore(64, newFreePtr)
        }

        function allocate_memory(size) -> memPtr {
            memPtr := allocate_unbounded()
            finalize_allocation(memPtr, size)
        }

        function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() {
            revert(0, 0)
        }

        function revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db() {
            revert(0, 0)
        }

        function cleanup_t_uint256(value) -> cleaned {
            cleaned := value
        }

        function validator_revert_t_uint256(value) {
            if iszero(eq(value, cleanup_t_uint256(value))) { revert(0, 0) }
        }

        function abi_decode_t_uint256_fromMemory(offset, end) -> value {
            value := mload(offset)
            validator_revert_t_uint256(value)
        }

        function abi_decode_tuple_t_uint256_fromMemory(headStart, dataEnd) -> value0 {
            if slt(sub(dataEnd, headStart), 32) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

            {

                let offset := 0

                value0 := abi_decode_t_uint256_fromMemory(add(headStart, offset), dataEnd)
            }

        }

        function copy_arguments_for_constructor_35_object_Census_134() -> ret_param_0 {
            let programSize := datasize("Census_134")
            let argSize := sub(codesize(), programSize)

            let memoryDataOffset := allocate_memory(argSize)
            codecopy(memoryDataOffset, programSize, argSize)

            ret_param_0 := abi_decode_tuple_t_uint256_fromMemory(memoryDataOffset, add(memoryDataOffset, argSize))
        }

        function convert_array_t_array$_t_uint256_$dyn_storage_to_t_array$_t_uint256_$dyn_storage_ptr(value) -> converted  {
            converted := value

        }

        function array_dataslot_t_array$_t_uint256_$dyn_storage_ptr(ptr) -> data {
            data := ptr

            mstore(0, ptr)
            data := keccak256(0, 0x20)

        }

        function panic_error_0x32() {
            mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
            mstore(4, 0x32)
            revert(0, 0x24)
        }

        function array_length_t_array$_t_uint256_$dyn_storage_ptr(value) -> length {

            length := sload(value)

        }

        function array_dataslot_t_bytes_storage_ptr(ptr) -> data {
            data := ptr

            mstore(0, ptr)
            data := keccak256(0, 0x20)

        }

        function long_byte_array_index_access_no_checks(array, index) -> slot, offset {

            offset := sub(31, mod(index, 0x20))
            let dataArea := array_dataslot_t_bytes_storage_ptr(array)
            slot := add(dataArea, div(index, 0x20))

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
        /// @ast-id 35
        /// @src 0:241:316  "constructor(uint initial) payable { seed = initial; values.push(initial); }"
        function constructor_Census_134(var_initial_21) {

            /// @src 0:241:316  "constructor(uint initial) payable { seed = initial; values.push(initial); }"

            /// @src 0:284:291  "initial"
            let _3 := var_initial_21
            let expr_25 := _3
            /// @src 0:277:291  "seed = initial"
            let _4 := expr_25
            mstore(128, _4)
            let expr_26 := expr_25
            /// @src 0:293:299  "values"
            let _5_slot := 0x00
            let expr_28_slot := _5_slot
            /// @src 0:293:304  "values.push"
            let expr_30_self_slot := convert_array_t_array$_t_uint256_$dyn_storage_to_t_array$_t_uint256_$dyn_storage_ptr(expr_28_slot)
            /// @src 0:305:312  "initial"
            let _6 := var_initial_21
            let expr_31 := _6
            /// @src 0:293:313  "values.push(initial)"
            array_push_from_t_uint256_to_t_array$_t_uint256_$dyn_storage_ptr(expr_30_self_slot, expr_31)

        }
        /// @src 0:160:996  "contract Census {..."

    }
    /// @use-src 0:"Census.sol"
    object "Census_134_deployed" {
        code {
            /// @src 0:160:996  "contract Census {..."
            mstore(64, memoryguard(128))

            if gt(calldatasize(), 3)
            {
                let selector := shift_right_224_unsigned(calldataload(0))
                switch selector

                case 0x444aa50e
                {
                    // linked(uint256)

                    external_fun_linked_124()
                }

                case 0x624fbfdc
                {
                    // echo(bytes)

                    external_fun_echo_109()
                }

                case 0x6cbb5ae3
                {
                    // arithmetic(uint256,uint256)

                    external_fun_arithmetic_55()
                }

                case 0x75059c59
                {
                    // assemblyWord(uint256)

                    external_fun_assemblyWord_133()
                }

                case 0x7af91e2e
                {
                    // signed(int256,int256)

                    external_fun_signed_69()
                }

                case 0x7d94792a
                {
                    // seed()

                    external_fun_seed_16()
                }

                case 0x959ac484
                {
                    // push(uint256)

                    external_fun_push_90()
                }

                case 0xa4ece52c
                {
                    // pop()

                    external_fun_pop_99()
                }

                default {}
            }

            revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()

            function shift_right_224_unsigned(value) -> newValue {
                newValue :=

                shr(224, value)

            }

            function allocate_unbounded() -> memPtr {
                memPtr := mload(64)
            }

            function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() {
                revert(0, 0)
            }

            function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() {
                revert(0, 0)
            }

            function revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db() {
                revert(0, 0)
            }

            function cleanup_t_uint256(value) -> cleaned {
                cleaned := value
            }

            function validator_revert_t_uint256(value) {
                if iszero(eq(value, cleanup_t_uint256(value))) { revert(0, 0) }
            }

            function abi_decode_t_uint256(offset, end) -> value {
                value := calldataload(offset)
                validator_revert_t_uint256(value)
            }

            function abi_decode_tuple_t_uint256(headStart, dataEnd) -> value0 {
                if slt(sub(dataEnd, headStart), 32) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

                {

                    let offset := 0

                    value0 := abi_decode_t_uint256(add(headStart, offset), dataEnd)
                }

            }

            function abi_encode_t_uint256_to_t_uint256_fromStack(value, pos) {
                mstore(pos, cleanup_t_uint256(value))
            }

            function abi_encode_tuple_t_uint256__to_t_uint256__fromStack(headStart , value0) -> tail {
                tail := add(headStart, 32)

                abi_encode_t_uint256_to_t_uint256_fromStack(value0,  add(headStart, 0))

            }

            function external_fun_linked_124() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                let param_0 :=  abi_decode_tuple_t_uint256(4, calldatasize())
                let ret_0 :=  fun_linked_124(param_0)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_uint256__to_t_uint256__fromStack(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

            function revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d() {
                revert(0, 0)
            }

            function revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490() {
                revert(0, 0)
            }

            function revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef() {
                revert(0, 0)
            }

            // bytes
            function abi_decode_t_bytes_calldata_ptr(offset, end) -> arrayPos, length {
                if iszero(slt(add(offset, 0x1f), end)) { revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d() }
                length := calldataload(offset)
                if gt(length, 0xffffffffffffffff) { revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490() }
                arrayPos := add(offset, 0x20)
                if gt(add(arrayPos, mul(length, 0x01)), end) { revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef() }
            }

            function abi_decode_tuple_t_bytes_calldata_ptr(headStart, dataEnd) -> value0, value1 {
                if slt(sub(dataEnd, headStart), 32) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

                {

                    let offset := calldataload(add(headStart, 0))
                    if gt(offset, 0xffffffffffffffff) { revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db() }

                    value0, value1 := abi_decode_t_bytes_calldata_ptr(add(headStart, offset), dataEnd)
                }

            }

            function array_length_t_bytes_memory_ptr(value) -> length {

                length := mload(value)

            }

            function array_storeLengthForEncoding_t_bytes_memory_ptr_fromStack(pos, length) -> updated_pos {
                mstore(pos, length)
                updated_pos := add(pos, 0x20)
            }

            function copy_memory_to_memory_with_cleanup(src, dst, length) {

                mcopy(dst, src, length)
                mstore(add(dst, length), 0)

            }

            function round_up_to_mul_of_32(value) -> result {
                result := and(add(value, 31), not(31))
            }

            function abi_encode_t_bytes_memory_ptr_to_t_bytes_memory_ptr_fromStack(value, pos) -> end {
                let length := array_length_t_bytes_memory_ptr(value)
                pos := array_storeLengthForEncoding_t_bytes_memory_ptr_fromStack(pos, length)
                copy_memory_to_memory_with_cleanup(add(value, 0x20), pos, length)
                end := add(pos, round_up_to_mul_of_32(length))
            }

            function abi_encode_tuple_t_bytes_memory_ptr__to_t_bytes_memory_ptr__fromStack(headStart , value0) -> tail {
                tail := add(headStart, 32)

                mstore(add(headStart, 0), sub(tail, headStart))
                tail := abi_encode_t_bytes_memory_ptr_to_t_bytes_memory_ptr_fromStack(value0,  tail)

            }

            function external_fun_echo_109() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                let param_0, param_1 :=  abi_decode_tuple_t_bytes_calldata_ptr(4, calldatasize())
                let ret_0 :=  fun_echo_109(param_0, param_1)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_bytes_memory_ptr__to_t_bytes_memory_ptr__fromStack(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

            function abi_decode_tuple_t_uint256t_uint256(headStart, dataEnd) -> value0, value1 {
                if slt(sub(dataEnd, headStart), 64) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

                {

                    let offset := 0

                    value0 := abi_decode_t_uint256(add(headStart, offset), dataEnd)
                }

                {

                    let offset := 32

                    value1 := abi_decode_t_uint256(add(headStart, offset), dataEnd)
                }

            }

            function abi_encode_tuple_t_uint256_t_uint256__to_t_uint256_t_uint256__fromStack(headStart , value0, value1) -> tail {
                tail := add(headStart, 64)

                abi_encode_t_uint256_to_t_uint256_fromStack(value0,  add(headStart, 0))

                abi_encode_t_uint256_to_t_uint256_fromStack(value1,  add(headStart, 32))

            }

            function external_fun_arithmetic_55() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                let param_0, param_1 :=  abi_decode_tuple_t_uint256t_uint256(4, calldatasize())
                let ret_0, ret_1 :=  fun_arithmetic_55(param_0, param_1)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_uint256_t_uint256__to_t_uint256_t_uint256__fromStack(memPos , ret_0, ret_1)
                return(memPos, sub(memEnd, memPos))

            }

            function external_fun_assemblyWord_133() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                let param_0 :=  abi_decode_tuple_t_uint256(4, calldatasize())
                let ret_0 :=  fun_assemblyWord_133(param_0)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_uint256__to_t_uint256__fromStack(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

            function cleanup_t_int256(value) -> cleaned {
                cleaned := value
            }

            function validator_revert_t_int256(value) {
                if iszero(eq(value, cleanup_t_int256(value))) { revert(0, 0) }
            }

            function abi_decode_t_int256(offset, end) -> value {
                value := calldataload(offset)
                validator_revert_t_int256(value)
            }

            function abi_decode_tuple_t_int256t_int256(headStart, dataEnd) -> value0, value1 {
                if slt(sub(dataEnd, headStart), 64) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

                {

                    let offset := 0

                    value0 := abi_decode_t_int256(add(headStart, offset), dataEnd)
                }

                {

                    let offset := 32

                    value1 := abi_decode_t_int256(add(headStart, offset), dataEnd)
                }

            }

            function abi_encode_t_int256_to_t_int256_fromStack(value, pos) {
                mstore(pos, cleanup_t_int256(value))
            }

            function abi_encode_tuple_t_int256__to_t_int256__fromStack(headStart , value0) -> tail {
                tail := add(headStart, 32)

                abi_encode_t_int256_to_t_int256_fromStack(value0,  add(headStart, 0))

            }

            function external_fun_signed_69() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                let param_0, param_1 :=  abi_decode_tuple_t_int256t_int256(4, calldatasize())
                let ret_0 :=  fun_signed_69(param_0, param_1)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_int256__to_t_int256__fromStack(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

            function abi_decode_tuple_(headStart, dataEnd)   {
                if slt(sub(dataEnd, headStart), 0) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

            }

            /// @ast-id 16
            /// @src 0:182:208  "uint public immutable seed"
            function getter_fun_seed_16() -> rval {
                rval := loadimmutable("16")
            }
            /// @src 0:160:996  "contract Census {..."

            function external_fun_seed_16() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                abi_decode_tuple_(4, calldatasize())
                let ret_0 :=  getter_fun_seed_16()
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_uint256__to_t_uint256__fromStack(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

            function external_fun_push_90() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                let param_0 :=  abi_decode_tuple_t_uint256(4, calldatasize())
                let ret_0 :=  fun_push_90(param_0)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_uint256__to_t_uint256__fromStack(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

            function abi_encode_tuple__to__fromStack(headStart ) -> tail {
                tail := add(headStart, 0)

            }

            function external_fun_pop_99() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                abi_decode_tuple_(4, calldatasize())
                fun_pop_99()
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple__to__fromStack(memPos  )
                return(memPos, sub(memEnd, memPos))

            }

            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74() {
                revert(0, 0)
            }

            function zero_value_for_split_t_uint256() -> ret {
                ret := 0
            }

            function convert_t_type$_t_contract$_LinkedMath_$14_$_to_t_address(value) -> converted {
                converted := value
            }

            function revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20() {
                revert(0, 0)
            }

            function panic_error_0x41() {
                mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                mstore(4, 0x41)
                revert(0, 0x24)
            }

            function finalize_allocation(memPtr, size) {
                let newFreePtr := add(memPtr, round_up_to_mul_of_32(size))
                // protect against overflow
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { panic_error_0x41() }
                mstore(64, newFreePtr)
            }

            function shift_left_224(value) -> newValue {
                newValue :=

                shl(224, value)

            }

            function abi_decode_t_uint256_fromMemory(offset, end) -> value {
                value := mload(offset)
                validator_revert_t_uint256(value)
            }

            function abi_decode_tuple_t_uint256_fromMemory(headStart, dataEnd) -> value0 {
                if slt(sub(dataEnd, headStart), 32) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

                {

                    let offset := 0

                    value0 := abi_decode_t_uint256_fromMemory(add(headStart, offset), dataEnd)
                }

            }

            function abi_encode_t_uint256_to_t_uint256_fromStack_library(value, pos) {
                mstore(pos, cleanup_t_uint256(value))
            }

            function abi_encode_tuple_t_uint256__to_t_uint256__fromStack_library(headStart , value0) -> tail {
                tail := add(headStart, 32)

                abi_encode_t_uint256_to_t_uint256_fromStack_library(value0,  add(headStart, 0))

            }

            function revert_forward_1() {
                let pos := allocate_unbounded()
                returndatacopy(pos, 0, returndatasize())
                revert(pos, returndatasize())
            }

            function panic_error_0x11() {
                mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                mstore(4, 0x11)
                revert(0, 0x24)
            }

            function checked_add_t_uint256(x, y) -> sum {
                x := cleanup_t_uint256(x)
                y := cleanup_t_uint256(y)
                sum := add(x, y)

                if gt(x, sum) { panic_error_0x11() }

            }

            /// @ast-id 124
            /// @src 0:781:872  "function linked(uint x) external view returns (uint) { return LinkedMath.twice(x) + seed; }"
            function fun_linked_124(var_x_111) -> var__114 {
                /// @src 0:828:832  "uint"
                let zero_t_uint256_1 := zero_value_for_split_t_uint256()
                var__114 := zero_t_uint256_1

                /// @src 0:843:853  "LinkedMath"
                let expr_116_address := linkersymbol("Census.sol:LinkedMath")
                /// @src 0:843:859  "LinkedMath.twice"
                let expr_117_address := convert_t_type$_t_contract$_LinkedMath_$14_$_to_t_address(expr_116_address)
                let expr_117_functionSelector := 0x3cf3bbf4
                /// @src 0:860:861  "x"
                let _2 := var_x_111
                let expr_118 := _2
                /// @src 0:843:862  "LinkedMath.twice(x)"

                // storage for arguments and returned data
                let _3 := allocate_unbounded()
                mstore(_3, shift_left_224(expr_117_functionSelector))
                let _4 := abi_encode_tuple_t_uint256__to_t_uint256__fromStack_library(add(_3, 4) , expr_118)

                let _5 := delegatecall(gas(), expr_117_address,  _3, sub(_4, _3), _3, 32)

                if iszero(_5) { revert_forward_1() }

                let expr_119
                if _5 {

                    let _6 := 32

                    if gt(_6, returndatasize()) {
                        _6 := returndatasize()
                    }

                    // update freeMemoryPointer according to dynamic return size
                    finalize_allocation(_3, _6)

                    // decode return parameters from external try-call into retVars
                    expr_119 :=  abi_decode_tuple_t_uint256_fromMemory(_3, add(_3, _6))
                }
                /// @src 0:865:869  "seed"
                let _7 := loadimmutable("16")
                let expr_120 := _7
                /// @src 0:843:869  "LinkedMath.twice(x) + seed"
                let expr_121 := checked_add_t_uint256(expr_119, expr_120)

                /// @src 0:836:869  "return LinkedMath.twice(x) + seed"
                var__114 := expr_121
                leave

            }
            /// @src 0:160:996  "contract Census {..."

            function zero_value_for_split_t_bytes_memory_ptr() -> ret {
                ret := 96
            }

            function revert_error_987264b3b1d58a9c7f8255e93e81c77d86d6299019c33110a076957a3e06e2ae() {
                revert(0, 0)
            }

            function allocate_memory(size) -> memPtr {
                memPtr := allocate_unbounded()
                finalize_allocation(memPtr, size)
            }

            function array_allocation_size_t_bytes_memory_ptr(length) -> size {
                // Make sure we can allocate memory without overflow
                if gt(length, 0xffffffffffffffff) { panic_error_0x41() }

                size := round_up_to_mul_of_32(length)

                // add length slot
                size := add(size, 0x20)

            }

            function copy_calldata_to_memory_with_cleanup(src, dst, length) {

                calldatacopy(dst, src, length)
                mstore(add(dst, length), 0)

            }

            function abi_decode_available_length_t_bytes_memory_ptr(src, length, end) -> array {
                array := allocate_memory(array_allocation_size_t_bytes_memory_ptr(length))
                mstore(array, length)
                let dst := add(array, 0x20)
                if gt(add(src, length), end) { revert_error_987264b3b1d58a9c7f8255e93e81c77d86d6299019c33110a076957a3e06e2ae() }
                copy_calldata_to_memory_with_cleanup(src, dst, length)
            }

            function convert_array_t_bytes_calldata_ptr_to_t_bytes_memory_ptr(value, length) -> converted  {

                // Copy the array to a free position in memory
                converted :=

                abi_decode_available_length_t_bytes_memory_ptr(value, length, calldatasize())

            }

            /// @ast-id 109
            /// @src 0:686:776  "function echo(bytes calldata input) external pure returns (bytes memory) { return input; }"
            function fun_echo_109(var_input_101_offset, var_input_101_length) -> var__104_mpos {
                /// @src 0:745:757  "bytes memory"
                let zero_t_bytes_memory_ptr_8_mpos := zero_value_for_split_t_bytes_memory_ptr()
                var__104_mpos := zero_t_bytes_memory_ptr_8_mpos

                /// @src 0:768:773  "input"
                let _9_offset := var_input_101_offset
                let _9_length := var_input_101_length
                let expr_106_offset := _9_offset
                let expr_106_length := _9_length
                /// @src 0:761:773  "return input"
                var__104_mpos := convert_array_t_bytes_calldata_ptr_to_t_bytes_memory_ptr(expr_106_offset, expr_106_length)
                leave

            }
            /// @src 0:160:996  "contract Census {..."

            function shift_right_1_unsigned(value) -> newValue {
                newValue :=

                shr(1, value)

            }

            function checked_exp_helper(_power, _base, exponent, max) -> power, base {
                power := _power
                base  := _base
                for { } gt(exponent, 1) {}
                {
                    // overflow check for base * base
                    if gt(base, div(max, base)) { panic_error_0x11() }
                    if and(exponent, 1)
                    {
                        // No checks for power := mul(power, base) needed, because the check
                        // for base * base above is sufficient, since:
                        // |power| <= base (proof by induction) and thus:
                        // |power * base| <= base * base <= max <= |min| (for signed)
                        // (this is equally true for signed and unsigned exp)
                        power := mul(power, base)
                    }
                    base := mul(base, base)
                    exponent := shift_right_1_unsigned(exponent)
                }
            }

            function checked_exp_unsigned(base, exponent, max) -> power {
                // This function currently cannot be inlined because of the
                // "leave" statements. We have to improve the optimizer.

                // Note that 0**0 == 1
                if iszero(exponent) { power := 1 leave }
                if iszero(base) { power := 0 leave }

                // Specializations for small bases
                switch base
                // 0 is handled above
                case 1 { power := 1 leave }
                case 2
                {
                    if gt(exponent, 255) { panic_error_0x11() }
                    power := exp(2, exponent)
                    if gt(power, max) { panic_error_0x11() }
                    leave
                }
                if or(
                    and(lt(base, 11), lt(exponent, 78)),
                    and(lt(base, 307), lt(exponent, 32))
                )
                {
                    power := exp(base, exponent)
                    if gt(power, max) { panic_error_0x11() }
                    leave
                }

                power, base := checked_exp_helper(1, base, exponent, max)

                if gt(power, div(max, base)) { panic_error_0x11() }
                power := mul(power, base)
            }

            function checked_exp_t_uint256_t_uint256(base, exponent) -> power {
                base := cleanup_t_uint256(base)
                exponent := cleanup_t_uint256(exponent)

                power := checked_exp_unsigned(base, exponent, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)

            }

            /// @ast-id 55
            /// @src 0:321:431  "function arithmetic(uint a, uint b) external pure returns (uint, uint) {..."
            function fun_arithmetic_55(var_a_37, var_b_39) -> var__42, var__44 {
                /// @src 0:380:384  "uint"
                let zero_t_uint256_10 := zero_value_for_split_t_uint256()
                var__42 := zero_t_uint256_10
                /// @src 0:386:390  "uint"
                let zero_t_uint256_11 := zero_value_for_split_t_uint256()
                var__44 := zero_t_uint256_11

                /// @src 0:410:411  "a"
                let _12 := var_a_37
                let expr_46 := _12
                /// @src 0:414:415  "b"
                let _13 := var_b_39
                let expr_47 := _13
                /// @src 0:410:415  "a + b"
                let expr_48 := checked_add_t_uint256(expr_46, expr_47)

                /// @src 0:409:424  "(a + b, a ** b)"
                let expr_52_component_1 := expr_48
                /// @src 0:417:418  "a"
                let _14 := var_a_37
                let expr_49 := _14
                /// @src 0:422:423  "b"
                let _15 := var_b_39
                let expr_50 := _15
                /// @src 0:417:423  "a ** b"
                let expr_51 := checked_exp_t_uint256_t_uint256(expr_49, expr_50)
                /// @src 0:409:424  "(a + b, a ** b)"
                let expr_52_component_2 := expr_51
                /// @src 0:402:424  "return (a + b, a ** b)"
                var__42 := expr_52_component_1
                var__44 := expr_52_component_2
                leave

            }
            /// @src 0:160:996  "contract Census {..."

            /// @ast-id 133
            /// @src 0:877:994  "function assemblyWord(uint x) external pure returns (uint r) {..."
            function fun_assemblyWord_133(var_x_126) -> var_r_129 {
                /// @src 0:930:936  "uint r"
                let zero_t_uint256_16 := zero_value_for_split_t_uint256()
                var_r_129 := zero_t_uint256_16

                /// @src 0:948:988  "assembly (\"memory-safe\") { r := clz(x) }"
                { var_r_129 := clz(var_x_126) }

            }
            /// @src 0:160:996  "contract Census {..."

            function zero_value_for_split_t_int256() -> ret {
                ret := 0
            }

            function panic_error_0x12() {
                mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                mstore(4, 0x12)
                revert(0, 0x24)
            }

            function checked_div_t_int256(x, y) -> r {
                x := cleanup_t_int256(x)
                y := cleanup_t_int256(y)
                if iszero(y) { panic_error_0x12() }

                // overflow for minVal / -1
                if and(
                    eq(x, 0x8000000000000000000000000000000000000000000000000000000000000000),
                    eq(y, sub(0, 1))
                ) { panic_error_0x11() }

                r := sdiv(x, y)
            }

            /// @ast-id 69
            /// @src 0:436:511  "function signed(int a, int b) external pure returns (int) { return a / b; }"
            function fun_signed_69(var_a_57, var_b_59) -> var__62 {
                /// @src 0:489:492  "int"
                let zero_t_int256_17 := zero_value_for_split_t_int256()
                var__62 := zero_t_int256_17

                /// @src 0:503:504  "a"
                let _18 := var_a_57
                let expr_64 := _18
                /// @src 0:507:508  "b"
                let _19 := var_b_59
                let expr_65 := _19
                /// @src 0:503:508  "a / b"
                let expr_66 := checked_div_t_int256(expr_64, expr_65)

                /// @src 0:496:508  "return a / b"
                var__62 := expr_66
                leave

            }
            /// @src 0:160:996  "contract Census {..."

            function convert_array_t_array$_t_uint256_$dyn_storage_to_t_array$_t_uint256_$dyn_storage_ptr(value) -> converted  {
                converted := value

            }

            function array_dataslot_t_array$_t_uint256_$dyn_storage_ptr(ptr) -> data {
                data := ptr

                mstore(0, ptr)
                data := keccak256(0, 0x20)

            }

            function panic_error_0x32() {
                mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                mstore(4, 0x32)
                revert(0, 0x24)
            }

            function array_length_t_array$_t_uint256_$dyn_storage_ptr(value) -> length {

                length := sload(value)

            }

            function array_dataslot_t_bytes_storage_ptr(ptr) -> data {
                data := ptr

                mstore(0, ptr)
                data := keccak256(0, 0x20)

            }

            function long_byte_array_index_access_no_checks(array, index) -> slot, offset {

                offset := sub(31, mod(index, 0x20))
                let dataArea := array_dataslot_t_bytes_storage_ptr(array)
                slot := add(dataArea, div(index, 0x20))

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
            function array_length_t_array$_t_uint256_$dyn_storage(value) -> length {

                length := sload(value)

            }

            function cleanup_t_rational_1_by_1(value) -> cleaned {
                cleaned := value
            }

            function convert_t_rational_1_by_1_to_t_uint256(value) -> converted {
                converted := cleanup_t_uint256(identity(cleanup_t_rational_1_by_1(value)))
            }

            function checked_sub_t_uint256(x, y) -> diff {
                x := cleanup_t_uint256(x)
                y := cleanup_t_uint256(y)
                diff := sub(x, y)

                if gt(diff, x) { panic_error_0x11() }

            }

            function array_dataslot_t_array$_t_uint256_$dyn_storage(ptr) -> data {
                data := ptr

                mstore(0, ptr)
                data := keccak256(0, 0x20)

            }

            function storage_array_index_access_t_array$_t_uint256_$dyn_storage(array, index) -> slot, offset {
                let arrayLength := array_length_t_array$_t_uint256_$dyn_storage(array)
                if iszero(lt(index, arrayLength)) { panic_error_0x32() }

                let dataArea := array_dataslot_t_array$_t_uint256_$dyn_storage(array)
                slot := add(dataArea, mul(index, 1))
                offset := 0

            }

            function shift_right_unsigned_dynamic(bits, value) -> newValue {
                newValue :=

                shr(bits, value)

            }

            function cleanup_from_storage_t_uint256(value) -> cleaned {
                cleaned := value
            }

            function extract_from_storage_value_dynamict_uint256(slot_value, offset) -> value {
                value := cleanup_from_storage_t_uint256(shift_right_unsigned_dynamic(mul(offset, 8), slot_value))
            }

            function read_from_storage_split_dynamic_t_uint256(slot, offset) -> value {
                value := extract_from_storage_value_dynamict_uint256(sload(slot), offset)

            }

            /// @ast-id 90
            /// @src 0:516:635  "function push(uint value) external returns (uint) {..."
            function fun_push_90(var_value_71) -> var__74 {
                /// @src 0:560:564  "uint"
                let zero_t_uint256_20 := zero_value_for_split_t_uint256()
                var__74 := zero_t_uint256_20

                /// @src 0:576:582  "values"
                let _21_slot := 0x00
                let expr_76_slot := _21_slot
                /// @src 0:576:587  "values.push"
                let expr_78_self_slot := convert_array_t_array$_t_uint256_$dyn_storage_to_t_array$_t_uint256_$dyn_storage_ptr(expr_76_slot)
                /// @src 0:588:593  "value"
                let _22 := var_value_71
                let expr_79 := _22
                /// @src 0:576:594  "values.push(value)"
                array_push_from_t_uint256_to_t_array$_t_uint256_$dyn_storage_ptr(expr_78_self_slot, expr_79)
                /// @src 0:603:609  "values"
                let _23_slot := 0x00
                let expr_82_slot := _23_slot
                /// @src 0:610:616  "values"
                let _24_slot := 0x00
                let expr_83_slot := _24_slot
                /// @src 0:610:623  "values.length"
                let expr_84 := array_length_t_array$_t_uint256_$dyn_storage(expr_83_slot)
                /// @src 0:626:627  "1"
                let expr_85 := 0x01
                /// @src 0:610:627  "values.length - 1"
                let expr_86 := checked_sub_t_uint256(expr_84, convert_t_rational_1_by_1_to_t_uint256(expr_85))

                /// @src 0:603:628  "values[values.length - 1]"

                let _25, _26 := storage_array_index_access_t_array$_t_uint256_$dyn_storage(expr_82_slot, expr_86)
                let _27 := read_from_storage_split_dynamic_t_uint256(_25, _26)
                let expr_87 := _27
                /// @src 0:596:628  "return values[values.length - 1]"
                var__74 := expr_87
                leave

            }
            /// @src 0:160:996  "contract Census {..."

            function panic_error_0x31() {
                mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                mstore(4, 0x31)
                revert(0, 0x24)
            }

            function storage_set_to_zero_t_uint256(slot, offset) {
                let zero_0 := zero_value_for_split_t_uint256()
                update_storage_value_t_uint256_to_t_uint256(slot, offset, zero_0)
            }

            function array_pop_t_array$_t_uint256_$dyn_storage_ptr(array) {
                let oldLen := array_length_t_array$_t_uint256_$dyn_storage_ptr(array)
                if iszero(oldLen) { panic_error_0x31() }
                let newLen := sub(oldLen, 1)
                let slot, offset := storage_array_index_access_t_array$_t_uint256_$dyn_storage_ptr(array, newLen)
                storage_set_to_zero_t_uint256(slot, offset)
                sstore(array, newLen)
            }
            /// @ast-id 99
            /// @src 0:640:681  "function pop() external { values.pop(); }"
            function fun_pop_99() {

                /// @src 0:666:672  "values"
                let _28_slot := 0x00
                let expr_93_slot := _28_slot
                /// @src 0:666:676  "values.pop"
                let expr_95_self_slot := convert_array_t_array$_t_uint256_$dyn_storage_to_t_array$_t_uint256_$dyn_storage_ptr(expr_93_slot)
                array_pop_t_array$_t_uint256_$dyn_storage_ptr(expr_95_self_slot)

            }
            /// @src 0:160:996  "contract Census {..."

        }

        data ".metadata" hex"a264697066735822122084055a07268673dfd7decc59bd158075d11eae5632cded73e165bca61ed58e3f64736f6c63430008260033"
    }

}

