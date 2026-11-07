/// @use-src 0:"Census.sol"
object "Census_134" {
    code {
        {
            /// @src 0:160:996  "contract Census {..."
            mstore(64, memoryguard(160))
            let _1 := copy_arguments_for_constructor_object_Census()
            constructor_Census(_1)
            let _2 := allocate_unbounded()
            codecopy(_2, dataoffset("Census_134_deployed"), datasize("Census_134_deployed"))
            setimmutable(_2, "16", mload(128))
            return(_2, datasize("Census_134_deployed"))
        }
        function allocate_unbounded() -> memPtr
        { memPtr := mload(64) }
        function round_up_to_mul_of(value) -> result
        {
            result := and(add(value, 31), not(31))
        }
        function panic_error_0x41()
        {
            mstore(0, shl(224, 0x4e487b71))
            mstore(4, 0x41)
            revert(0, 0x24)
        }
        function finalize_allocation(memPtr, size)
        {
            let newFreePtr := add(memPtr, round_up_to_mul_of(size))
            if or(gt(newFreePtr, sub(shl(64, 1), 1)), lt(newFreePtr, memPtr)) { panic_error_0x41() }
            mstore(64, newFreePtr)
        }
        function allocate_memory(size) -> memPtr
        {
            memPtr := allocate_unbounded()
            finalize_allocation(memPtr, size)
        }
        function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
        { revert(0, 0) }
        function cleanup_uint256(value) -> cleaned
        { cleaned := value }
        function validator_revert_uint256(value)
        {
            if iszero(eq(value, cleanup_uint256(value))) { revert(0, 0) }
        }
        function abi_decode_t_uint256_fromMemory(offset, end) -> value
        {
            value := mload(offset)
            validator_revert_uint256(value)
        }
        function abi_decode_uint256_fromMemory(headStart, dataEnd) -> value0
        {
            if slt(sub(dataEnd, headStart), 32)
            {
                revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
            }
            let offset := 0
            value0 := abi_decode_t_uint256_fromMemory(add(headStart, offset), dataEnd)
        }
        function copy_arguments_for_constructor_object_Census() -> ret_param
        {
            let programSize := datasize("Census_134")
            let argSize := sub(codesize(), programSize)
            let memoryDataOffset := allocate_memory(argSize)
            codecopy(memoryDataOffset, programSize, argSize)
            ret_param := abi_decode_uint256_fromMemory(memoryDataOffset, add(memoryDataOffset, argSize))
        }
        function convert_array_array_uint256_dyn_storage_to_array_uint256_dyn__ptr(value) -> converted
        { converted := value }
        function array_dataslot_array_uint256_dyn_storage_ptr(ptr) -> data
        {
            data := ptr
            mstore(0, ptr)
            data := keccak256(0, 0x20)
        }
        function panic_error_0x32()
        {
            mstore(0, shl(224, 0x4e487b71))
            mstore(4, 0x32)
            revert(0, 0x24)
        }
        function array_length_array_uint256_dyn_storage_ptr(value) -> length
        { length := sload(value) }
        function storage_array_index_access_uint256_dyn__ptr(array, index) -> slot, offset
        {
            let arrayLength := array_length_array_uint256_dyn_storage_ptr(array)
            if iszero(lt(index, arrayLength)) { panic_error_0x32() }
            let dataArea := array_dataslot_array_uint256_dyn_storage_ptr(array)
            slot := add(dataArea, mul(index, 1))
            offset := 0
        }
        function shift_left_dynamic(bits, value) -> newValue
        { newValue := shl(bits, value) }
        function update_byte_slice_dynamic32(value, shiftBytes, toInsert) -> result
        {
            let shiftBits := mul(shiftBytes, 8)
            let mask := shift_left_dynamic(shiftBits, not(0))
            toInsert := shift_left_dynamic(shiftBits, toInsert)
            value := and(value, not(mask))
            result := or(value, and(toInsert, mask))
        }
        function identity(value) -> ret
        { ret := value }
        function convert_uint256_to_uint256(value) -> converted
        {
            converted := cleanup_uint256(identity(cleanup_uint256(value)))
        }
        function prepare_store_uint256(value) -> ret
        { ret := value }
        function update_storage_value_uint256_to_uint256(slot, offset, value)
        {
            let convertedValue := convert_uint256_to_uint256(value)
            sstore(slot, update_byte_slice_dynamic32(sload(slot), offset, prepare_store_uint256(convertedValue)))
        }
        function array_push_from_uint256_to_array_uint256_dyn_storage_ptr(array, value0)
        {
            let oldLen := sload(array)
            if iszero(lt(oldLen, 18446744073709551616)) { panic_error_0x41() }
            sstore(array, add(oldLen, 1))
            let slot, offset := storage_array_index_access_uint256_dyn__ptr(array, oldLen)
            update_storage_value_uint256_to_uint256(slot, offset, value0)
        }
        /// @ast-id 35 @src 0:241:316  "constructor(uint initial) payable { seed = initial; values.push(initial); }"
        function constructor_Census(var_initial)
        {
            /// @src 0:284:291  "initial"
            let _1 := var_initial
            let expr := _1
            /// @src 0:277:291  "seed = initial"
            let _2 := expr
            mstore(128, _2)
            /// @src 0:293:299  "values"
            let _slot := 0x00
            let expr_slot := _slot
            /// @src 0:293:304  "values.push"
            let expr_self_slot := convert_array_array_uint256_dyn_storage_to_array_uint256_dyn__ptr(expr_slot)
            /// @src 0:305:312  "initial"
            let _3 := var_initial
            let expr_1 := _3
            /// @src 0:293:313  "values.push(initial)"
            array_push_from_uint256_to_array_uint256_dyn_storage_ptr(expr_self_slot, expr_1)
        }
    }
    /// @use-src 0:"Census.sol"
    object "Census_134_deployed" {
        code {
            {
                /// @src 0:160:996  "contract Census {..."
                mstore(64, memoryguard(128))
                if gt(calldatasize(), 3)
                {
                    let selector := shift_right_unsigned(calldataload(0))
                    switch selector
                    case 0x444aa50e { external_fun_linked() }
                    case 0x624fbfdc { external_fun_echo() }
                    case 0x6cbb5ae3 { external_fun_arithmetic() }
                    case 0x75059c59 { external_fun_assemblyWord() }
                    case 0x7af91e2e { external_fun_signed() }
                    case 0x7d94792a { external_fun_seed() }
                    case 0x959ac484 { external_fun_push() }
                    case 0xa4ece52c { external_fun_pop() }
                    default { }
                }
                revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            }
            function shift_right_unsigned(value) -> newValue
            { newValue := shr(224, value) }
            function allocate_unbounded() -> memPtr
            { memPtr := mload(64) }
            function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            { revert(0, 0) }
            function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
            { revert(0, 0) }
            function revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db()
            { revert(0, 0) }
            function cleanup_uint256(value) -> cleaned
            { cleaned := value }
            function validator_revert_uint256(value)
            {
                if iszero(eq(value, cleanup_uint256(value))) { revert(0, 0) }
            }
            function abi_decode_uint256(offset, end) -> value
            {
                value := calldataload(offset)
                validator_revert_uint256(value)
            }
            function abi_decode_tuple_uint256(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                let offset := 0
                value0 := abi_decode_uint256(add(headStart, offset), dataEnd)
            }
            function abi_encode_uint256_to_uint256(value, pos)
            {
                mstore(pos, cleanup_uint256(value))
            }
            function abi_encode_uint256(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                abi_encode_uint256_to_uint256(value0, add(headStart, 0))
            }
            function external_fun_linked()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let param := abi_decode_tuple_uint256(4, calldatasize())
                let ret := fun_linked(param)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_uint256(memPos, ret)
                return(memPos, sub(memEnd, memPos))
            }
            function revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d()
            { revert(0, 0) }
            function revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490()
            { revert(0, 0) }
            function revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef()
            { revert(0, 0) }
            function abi_decode_bytes_calldata_ptr(offset, end) -> arrayPos, length
            {
                if iszero(slt(add(offset, 0x1f), end))
                {
                    revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d()
                }
                length := calldataload(offset)
                if gt(length, 0xffffffffffffffff)
                {
                    revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490()
                }
                arrayPos := add(offset, 0x20)
                if gt(add(arrayPos, mul(length, 0x01)), end)
                {
                    revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef()
                }
            }
            function abi_decode_bytes_calldata(headStart, dataEnd) -> value0, value1
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                let offset := calldataload(add(headStart, 0))
                if gt(offset, 0xffffffffffffffff)
                {
                    revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db()
                }
                value0, value1 := abi_decode_bytes_calldata_ptr(add(headStart, offset), dataEnd)
            }
            function array_length_bytes(value) -> length
            { length := mload(value) }
            function array_storeLengthForEncoding_bytes(pos, length) -> updated_pos
            {
                mstore(pos, length)
                updated_pos := add(pos, 0x20)
            }
            function copy_memory_to_memory_with_cleanup(src, dst, length)
            {
                mcopy(dst, src, length)
                mstore(add(dst, length), 0)
            }
            function round_up_to_mul_of(value) -> result
            {
                result := and(add(value, 31), not(31))
            }
            function abi_encode_bytes_memory_ptr(value, pos) -> end
            {
                let length := array_length_bytes(value)
                pos := array_storeLengthForEncoding_bytes(pos, length)
                copy_memory_to_memory_with_cleanup(add(value, 0x20), pos, length)
                end := add(pos, round_up_to_mul_of(length))
            }
            function abi_encode_bytes(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                mstore(add(headStart, 0), sub(tail, headStart))
                tail := abi_encode_bytes_memory_ptr(value0, tail)
            }
            function external_fun_echo()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let param, param_1 := abi_decode_bytes_calldata(4, calldatasize())
                let ret := fun_echo(param, param_1)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_bytes(memPos, ret)
                return(memPos, sub(memEnd, memPos))
            }
            function abi_decode_uint256t_uint256(headStart, dataEnd) -> value0, value1
            {
                if slt(sub(dataEnd, headStart), 64)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                let offset := 0
                value0 := abi_decode_uint256(add(headStart, offset), dataEnd)
                let offset_1 := 32
                value1 := abi_decode_uint256(add(headStart, offset_1), dataEnd)
            }
            function abi_encode_uint256_uint256(headStart, value0, value1) -> tail
            {
                tail := add(headStart, 64)
                abi_encode_uint256_to_uint256(value0, add(headStart, 0))
                abi_encode_uint256_to_uint256(value1, add(headStart, 32))
            }
            function external_fun_arithmetic()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let param, param_1 := abi_decode_uint256t_uint256(4, calldatasize())
                let ret, ret_1 := fun_arithmetic(param, param_1)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_uint256_uint256(memPos, ret, ret_1)
                return(memPos, sub(memEnd, memPos))
            }
            function external_fun_assemblyWord()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let param := abi_decode_tuple_uint256(4, calldatasize())
                let ret := fun_assemblyWord(param)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_uint256(memPos, ret)
                return(memPos, sub(memEnd, memPos))
            }
            function cleanup_int256(value) -> cleaned
            { cleaned := value }
            function validator_revert_int256(value)
            {
                if iszero(eq(value, cleanup_int256(value))) { revert(0, 0) }
            }
            function abi_decode_int256(offset, end) -> value
            {
                value := calldataload(offset)
                validator_revert_int256(value)
            }
            function abi_decode_int256t_int256(headStart, dataEnd) -> value0, value1
            {
                if slt(sub(dataEnd, headStart), 64)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                let offset := 0
                value0 := abi_decode_int256(add(headStart, offset), dataEnd)
                let offset_1 := 32
                value1 := abi_decode_int256(add(headStart, offset_1), dataEnd)
            }
            function abi_encode_int256(value, pos)
            {
                mstore(pos, cleanup_int256(value))
            }
            function abi_encode_tuple_int256(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                abi_encode_int256(value0, add(headStart, 0))
            }
            function external_fun_signed()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let param, param_1 := abi_decode_int256t_int256(4, calldatasize())
                let ret := fun_signed(param, param_1)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_int256(memPos, ret)
                return(memPos, sub(memEnd, memPos))
            }
            function abi_decode(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            /// @ast-id 16 @src 0:182:208  "uint public immutable seed"
            function getter_fun_seed() -> rval
            { rval := loadimmutable("16") }
            /// @src 0:160:996  "contract Census {..."
            function external_fun_seed()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                let ret := getter_fun_seed()
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_uint256(memPos, ret)
                return(memPos, sub(memEnd, memPos))
            }
            function external_fun_push()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let param := abi_decode_tuple_uint256(4, calldatasize())
                let ret := fun_push(param)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_uint256(memPos, ret)
                return(memPos, sub(memEnd, memPos))
            }
            function abi_encode_tuple(headStart) -> tail
            { tail := add(headStart, 0) }
            function external_fun_pop()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                fun_pop()
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple(memPos)
                return(memPos, sub(memEnd, memPos))
            }
            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
            function zero_value_for_split_uint256() -> ret
            { ret := 0 }
            function convert_type_contract_LinkedMath_to_address(value) -> converted
            { converted := value }
            function panic_error_0x41()
            {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x41)
                revert(0, 0x24)
            }
            function finalize_allocation(memPtr, size)
            {
                let newFreePtr := add(memPtr, round_up_to_mul_of(size))
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { panic_error_0x41() }
                mstore(64, newFreePtr)
            }
            function shift_left(value) -> newValue
            { newValue := shl(224, value) }
            function abi_decode_t_uint256_fromMemory(offset, end) -> value
            {
                value := mload(offset)
                validator_revert_uint256(value)
            }
            function abi_decode_uint256_fromMemory(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                let offset := 0
                value0 := abi_decode_t_uint256_fromMemory(add(headStart, offset), dataEnd)
            }
            function abi_encode_uint256_to_uint256_library(value, pos)
            {
                mstore(pos, cleanup_uint256(value))
            }
            function abi_encode_tuple_uint256(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                abi_encode_uint256_to_uint256_library(value0, add(headStart, 0))
            }
            function revert_forward()
            {
                let pos := allocate_unbounded()
                returndatacopy(pos, 0, returndatasize())
                revert(pos, returndatasize())
            }
            function panic_error_0x11()
            {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x11)
                revert(0, 0x24)
            }
            function checked_add_uint256(x, y) -> sum
            {
                x := cleanup_uint256(x)
                y := cleanup_uint256(y)
                sum := add(x, y)
                if gt(x, sum) { panic_error_0x11() }
            }
            /// @ast-id 124 @src 0:781:872  "function linked(uint x) external view returns (uint) { return LinkedMath.twice(x) + seed; }"
            function fun_linked(var_x) -> var
            {
                /// @src 0:828:832  "uint"
                let zero_uint256 := zero_value_for_split_uint256()
                var := zero_uint256
                /// @src 0:843:853  "LinkedMath"
                let expr_116_address := linkersymbol("Census.sol:LinkedMath")
                /// @src 0:843:859  "LinkedMath.twice"
                let expr_address := convert_type_contract_LinkedMath_to_address(expr_116_address)
                let expr_functionSelector := 0x3cf3bbf4
                /// @src 0:860:861  "x"
                let _1 := var_x
                let expr := _1
                /// @src 0:843:862  "LinkedMath.twice(x)"
                let _2 := allocate_unbounded()
                mstore(_2, shift_left(expr_functionSelector))
                let _3 := abi_encode_tuple_uint256(add(_2, 4), expr)
                let _4 := delegatecall(gas(), expr_address, _2, sub(_3, _2), _2, 32)
                if iszero(_4) { revert_forward() }
                let expr_1
                if _4
                {
                    let _5 := 32
                    if gt(_5, returndatasize()) { _5 := returndatasize() }
                    finalize_allocation(_2, _5)
                    expr_1 := abi_decode_uint256_fromMemory(_2, add(_2, _5))
                }
                /// @src 0:865:869  "seed"
                let _6 := loadimmutable("16")
                let expr_2 := _6
                /// @src 0:843:869  "LinkedMath.twice(x) + seed"
                let expr_3 := checked_add_uint256(expr_1, expr_2)
                /// @src 0:836:869  "return LinkedMath.twice(x) + seed"
                var := expr_3
                leave
            }
            /// @src 0:160:996  "contract Census {..."
            function zero_value_for_split_bytes() -> ret
            { ret := 96 }
            function revert_error_987264b3b1d58a9c7f8255e93e81c77d86d6299019c33110a076957a3e06e2ae()
            { revert(0, 0) }
            function allocate_memory(size) -> memPtr
            {
                memPtr := allocate_unbounded()
                finalize_allocation(memPtr, size)
            }
            function array_allocation_size_bytes(length) -> size
            {
                if gt(length, 0xffffffffffffffff) { panic_error_0x41() }
                size := round_up_to_mul_of(length)
                size := add(size, 0x20)
            }
            function copy_calldata_to_memory_with_cleanup(src, dst, length)
            {
                calldatacopy(dst, src, length)
                mstore(add(dst, length), 0)
            }
            function abi_decode_available_length_bytes(src, length, end) -> array
            {
                array := allocate_memory(array_allocation_size_bytes(length))
                mstore(array, length)
                let dst := add(array, 0x20)
                if gt(add(src, length), end)
                {
                    revert_error_987264b3b1d58a9c7f8255e93e81c77d86d6299019c33110a076957a3e06e2ae()
                }
                copy_calldata_to_memory_with_cleanup(src, dst, length)
            }
            function convert_array_bytes_calldata_to_bytes(value, length) -> converted
            {
                converted := abi_decode_available_length_bytes(value, length, calldatasize())
            }
            /// @ast-id 109 @src 0:686:776  "function echo(bytes calldata input) external pure returns (bytes memory) { return input; }"
            function fun_echo(var_input_offset, var_input_length) -> var_mpos
            {
                /// @src 0:745:757  "bytes memory"
                let zero_bytes_mpos := zero_value_for_split_bytes()
                var_mpos := zero_bytes_mpos
                /// @src 0:768:773  "input"
                let _offset := var_input_offset
                let _length := var_input_length
                let expr_offset := _offset
                let expr_length := _length
                /// @src 0:761:773  "return input"
                var_mpos := convert_array_bytes_calldata_to_bytes(expr_offset, expr_length)
                leave
            }
            /// @src 0:160:996  "contract Census {..."
            function shift_right_1_unsigned(value) -> newValue
            { newValue := shr(1, value) }
            function checked_exp_helper(_power, _base, exponent, max) -> power, base
            {
                power := _power
                base := _base
                for { } gt(exponent, 1) { }
                {
                    if gt(base, div(max, base)) { panic_error_0x11() }
                    if and(exponent, 1) { power := mul(power, base) }
                    base := mul(base, base)
                    exponent := shift_right_1_unsigned(exponent)
                }
            }
            function checked_exp_unsigned(base, exponent, max) -> power
            {
                if iszero(exponent)
                {
                    power := 1
                    leave
                }
                if iszero(base)
                {
                    power := 0
                    leave
                }
                switch base
                case 1 {
                    power := 1
                    leave
                }
                case 2 {
                    if gt(exponent, 255) { panic_error_0x11() }
                    power := exp(2, exponent)
                    if gt(power, max) { panic_error_0x11() }
                    leave
                }
                if or(and(lt(base, 11), lt(exponent, 78)), and(lt(base, 307), lt(exponent, 32)))
                {
                    power := exp(base, exponent)
                    if gt(power, max) { panic_error_0x11() }
                    leave
                }
                power, base := checked_exp_helper(1, base, exponent, max)
                if gt(power, div(max, base)) { panic_error_0x11() }
                power := mul(power, base)
            }
            function checked_exp_uint256_uint256(base, exponent) -> power
            {
                base := cleanup_uint256(base)
                exponent := cleanup_uint256(exponent)
                power := checked_exp_unsigned(base, exponent, not(0))
            }
            /// @ast-id 55 @src 0:321:431  "function arithmetic(uint a, uint b) external pure returns (uint, uint) {..."
            function fun_arithmetic(var_a, var_b) -> var, var_1
            {
                /// @src 0:380:384  "uint"
                let zero_t_uint256 := zero_value_for_split_uint256()
                var := zero_t_uint256
                /// @src 0:386:390  "uint"
                let zero_uint256 := zero_value_for_split_uint256()
                var_1 := zero_uint256
                /// @src 0:410:411  "a"
                let _1 := var_a
                let expr := _1
                /// @src 0:414:415  "b"
                let _2 := var_b
                let expr_1 := _2
                /// @src 0:410:415  "a + b"
                let expr_2 := checked_add_uint256(expr, expr_1)
                /// @src 0:409:424  "(a + b, a ** b)"
                let expr_component := expr_2
                /// @src 0:417:418  "a"
                let _3 := var_a
                let expr_3 := _3
                /// @src 0:422:423  "b"
                let _4 := var_b
                let expr_4 := _4
                /// @src 0:417:423  "a ** b"
                let expr_5 := checked_exp_uint256_uint256(expr_3, expr_4)
                /// @src 0:409:424  "(a + b, a ** b)"
                let expr_component_1 := expr_5
                /// @src 0:402:424  "return (a + b, a ** b)"
                var := expr_component
                var_1 := expr_component_1
                leave
            }
            /// @ast-id 133 @src 0:877:994  "function assemblyWord(uint x) external pure returns (uint r) {..."
            function fun_assemblyWord(var_x) -> var_r
            {
                /// @src 0:930:936  "uint r"
                let zero_uint256 := zero_value_for_split_uint256()
                var_r := zero_uint256
                /// @src 0:948:988  "assembly (\"memory-safe\") { r := clz(x) }"
                var_r := clz(var_x)
            }
            /// @src 0:160:996  "contract Census {..."
            function zero_value_for_split_int256() -> ret
            { ret := 0 }
            function panic_error_0x12()
            {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x12)
                revert(0, 0x24)
            }
            function checked_div_int256(x, y) -> r
            {
                x := cleanup_int256(x)
                y := cleanup_int256(y)
                if iszero(y) { panic_error_0x12() }
                if and(eq(x, shl(255, 1)), eq(y, sub(0, 1))) { panic_error_0x11() }
                r := sdiv(x, y)
            }
            /// @ast-id 69 @src 0:436:511  "function signed(int a, int b) external pure returns (int) { return a / b; }"
            function fun_signed(var_a, var_b) -> var
            {
                /// @src 0:489:492  "int"
                let zero_int256 := zero_value_for_split_int256()
                var := zero_int256
                /// @src 0:503:504  "a"
                let _1 := var_a
                let expr := _1
                /// @src 0:507:508  "b"
                let _2 := var_b
                let expr_1 := _2
                /// @src 0:503:508  "a / b"
                let expr_2 := checked_div_int256(expr, expr_1)
                /// @src 0:496:508  "return a / b"
                var := expr_2
                leave
            }
            /// @src 0:160:996  "contract Census {..."
            function convert_array_array_uint256_dyn_storage_to_array_uint256_dyn__ptr(value) -> converted
            { converted := value }
            function array_dataslot_array_uint256_dyn_storage_ptr(ptr) -> data
            {
                data := ptr
                mstore(0, ptr)
                data := keccak256(0, 0x20)
            }
            function panic_error_0x32()
            {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x32)
                revert(0, 0x24)
            }
            function array_length_array_uint256_dyn_storage_ptr(value) -> length
            { length := sload(value) }
            function storage_array_index_access_uint256_dyn__ptr(array, index) -> slot, offset
            {
                let arrayLength := array_length_array_uint256_dyn_storage_ptr(array)
                if iszero(lt(index, arrayLength)) { panic_error_0x32() }
                let dataArea := array_dataslot_array_uint256_dyn_storage_ptr(array)
                slot := add(dataArea, mul(index, 1))
                offset := 0
            }
            function shift_left_dynamic(bits, value) -> newValue
            { newValue := shl(bits, value) }
            function update_byte_slice_dynamic32(value, shiftBytes, toInsert) -> result
            {
                let shiftBits := mul(shiftBytes, 8)
                let mask := shift_left_dynamic(shiftBits, not(0))
                toInsert := shift_left_dynamic(shiftBits, toInsert)
                value := and(value, not(mask))
                result := or(value, and(toInsert, mask))
            }
            function identity(value) -> ret
            { ret := value }
            function convert_uint256_to_uint256(value) -> converted
            {
                converted := cleanup_uint256(identity(cleanup_uint256(value)))
            }
            function prepare_store_uint256(value) -> ret
            { ret := value }
            function update_storage_value_uint256_to_uint256(slot, offset, value)
            {
                let convertedValue := convert_uint256_to_uint256(value)
                sstore(slot, update_byte_slice_dynamic32(sload(slot), offset, prepare_store_uint256(convertedValue)))
            }
            function array_push_from_uint256_to_array_uint256_dyn_storage_ptr(array, value0)
            {
                let oldLen := sload(array)
                if iszero(lt(oldLen, 18446744073709551616)) { panic_error_0x41() }
                sstore(array, add(oldLen, 1))
                let slot, offset := storage_array_index_access_uint256_dyn__ptr(array, oldLen)
                update_storage_value_uint256_to_uint256(slot, offset, value0)
            }
            function array_length_array_uint256_dyn_storage(value) -> length
            { length := sload(value) }
            function cleanup_rational_by(value) -> cleaned
            { cleaned := value }
            function convert_rational_by_to_uint256(value) -> converted
            {
                converted := cleanup_uint256(identity(cleanup_rational_by(value)))
            }
            function checked_sub_uint256(x, y) -> diff
            {
                x := cleanup_uint256(x)
                y := cleanup_uint256(y)
                diff := sub(x, y)
                if gt(diff, x) { panic_error_0x11() }
            }
            function array_dataslot_array_uint256_dyn_storage(ptr) -> data
            {
                data := ptr
                mstore(0, ptr)
                data := keccak256(0, 0x20)
            }
            function storage_array_index_access_uint256_dyn(array, index) -> slot, offset
            {
                let arrayLength := array_length_array_uint256_dyn_storage(array)
                if iszero(lt(index, arrayLength)) { panic_error_0x32() }
                let dataArea := array_dataslot_array_uint256_dyn_storage(array)
                slot := add(dataArea, mul(index, 1))
                offset := 0
            }
            function shift_right_unsigned_dynamic(bits, value) -> newValue
            { newValue := shr(bits, value) }
            function cleanup_from_storage_uint256(value) -> cleaned
            { cleaned := value }
            function extract_from_storage_value_dynamict_uint256(slot_value, offset) -> value
            {
                value := cleanup_from_storage_uint256(shift_right_unsigned_dynamic(mul(offset, 8), slot_value))
            }
            function read_from_storage_split_dynamic_uint256(slot, offset) -> value
            {
                value := extract_from_storage_value_dynamict_uint256(sload(slot), offset)
            }
            /// @ast-id 90 @src 0:516:635  "function push(uint value) external returns (uint) {..."
            function fun_push(var_value) -> var_
            {
                /// @src 0:560:564  "uint"
                let zero_uint256 := zero_value_for_split_uint256()
                var_ := zero_uint256
                /// @src 0:576:582  "values"
                let _21_slot := 0x00
                let expr_76_slot := _21_slot
                /// @src 0:576:587  "values.push"
                let expr_78_self_slot := convert_array_array_uint256_dyn_storage_to_array_uint256_dyn__ptr(expr_76_slot)
                /// @src 0:588:593  "value"
                let _1 := var_value
                let expr := _1
                /// @src 0:576:594  "values.push(value)"
                array_push_from_uint256_to_array_uint256_dyn_storage_ptr(expr_78_self_slot, expr)
                /// @src 0:603:609  "values"
                let _23_slot := 0x00
                let expr_slot := _23_slot
                /// @src 0:610:616  "values"
                let _slot := 0x00
                let expr_83_slot := _slot
                /// @src 0:610:623  "values.length"
                let expr_1 := array_length_array_uint256_dyn_storage(expr_83_slot)
                /// @src 0:626:627  "1"
                let expr_2 := 0x01
                /// @src 0:610:627  "values.length - 1"
                let expr_3 := checked_sub_uint256(expr_1, convert_rational_by_to_uint256(expr_2))
                /// @src 0:603:628  "values[values.length - 1]"
                let _2, _3 := storage_array_index_access_uint256_dyn(expr_slot, expr_3)
                let _4 := read_from_storage_split_dynamic_uint256(_2, _3)
                let expr_4 := _4
                /// @src 0:596:628  "return values[values.length - 1]"
                var_ := expr_4
                leave
            }
            /// @src 0:160:996  "contract Census {..."
            function panic_error_0x31()
            {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x31)
                revert(0, 0x24)
            }
            function storage_set_to_zero_uint256(slot, offset)
            {
                let zero := zero_value_for_split_uint256()
                update_storage_value_uint256_to_uint256(slot, offset, zero)
            }
            function array_pop_array_uint256_dyn_storage_ptr(array)
            {
                let oldLen := array_length_array_uint256_dyn_storage_ptr(array)
                if iszero(oldLen) { panic_error_0x31() }
                let newLen := sub(oldLen, 1)
                let slot, offset := storage_array_index_access_uint256_dyn__ptr(array, newLen)
                storage_set_to_zero_uint256(slot, offset)
                sstore(array, newLen)
            }
            /// @ast-id 99 @src 0:640:681  "function pop() external { values.pop(); }"
            function fun_pop()
            {
                /// @src 0:666:672  "values"
                let _28_slot := 0x00
                let expr_93_slot := _28_slot
                /// @src 0:666:676  "values.pop"
                let expr_self_slot := convert_array_array_uint256_dyn_storage_to_array_uint256_dyn__ptr(expr_93_slot)
                array_pop_array_uint256_dyn_storage_ptr(expr_self_slot)
            }
        }
        data ".metadata" hex"a264697066735822122084055a07268673dfd7decc59bd158075d11eae5632cded73e165bca61ed58e3f64736f6c63430008260033"
    }
}
