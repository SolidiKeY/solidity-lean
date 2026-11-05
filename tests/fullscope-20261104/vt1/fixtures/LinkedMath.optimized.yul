/// @use-src 0:"Census.sol"
object "LinkedMath_14" {
    code {
        {
            /// @src 0:63:159  "library LinkedMath {..."
            mstore(64, memoryguard(128))
            if callvalue()
            {
                revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            }
            let _1 := allocate_unbounded()
            codecopy(_1, dataoffset("LinkedMath_14_deployed"), datasize("LinkedMath_14_deployed"))
            setimmutable(_1, "library_deploy_address", address())
            return(_1, datasize("LinkedMath_14_deployed"))
        }
        function allocate_unbounded() -> memPtr
        { memPtr := mload(64) }
        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
        { revert(0, 0) }
    }
    /// @use-src 0:"Census.sol"
    object "LinkedMath_14_deployed" {
        code {
            {
                /// @src 0:63:159  "library LinkedMath {..."
                mstore(64, memoryguard(128))
                if gt(calldatasize(), 3)
                {
                    let selector := shift_right_unsigned(calldataload(0))
                    switch selector
                    case 0x3cf3bbf4 { external_fun_twice() }
                    default { }
                }
                revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            }
            function shift_right_unsigned(value) -> newValue
            { newValue := shr(224, value) }
            function allocate_unbounded() -> memPtr
            { memPtr := mload(64) }
            function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
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
            function abi_encode_uint256_to_uint256_library(value, pos)
            {
                mstore(pos, cleanup_uint256(value))
            }
            function abi_encode_uint256(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                abi_encode_uint256_to_uint256_library(value0, add(headStart, 0))
            }
            function external_fun_twice()
            {
                let param := abi_decode_tuple_uint256(4, calldatasize())
                let ret := fun_twice(param)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_uint256(memPos, ret)
                return(memPos, sub(memEnd, memPos))
            }
            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
            function zero_value_for_split_uint256() -> ret
            { ret := 0 }
            function cleanup_rational_by(value) -> cleaned
            { cleaned := value }
            function identity(value) -> ret
            { ret := value }
            function convert_rational_by_to_uint256(value) -> converted
            {
                converted := cleanup_uint256(identity(cleanup_rational_by(value)))
            }
            function panic_error_0x11()
            {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x11)
                revert(0, 0x24)
            }
            function checked_mul_uint256(x, y) -> product
            {
                x := cleanup_uint256(x)
                y := cleanup_uint256(y)
                let product_raw := mul(x, y)
                product := cleanup_uint256(product_raw)
                if iszero(or(iszero(x), eq(y, div(product, x)))) { panic_error_0x11() }
            }
            /// @ast-id 13 @src 0:88:157  "function twice(uint x) external pure returns (uint) { return x * 2; }"
            function fun_twice(var_x) -> var
            {
                /// @src 0:134:138  "uint"
                let zero_uint256 := zero_value_for_split_uint256()
                var := zero_uint256
                /// @src 0:149:150  "x"
                let _1 := var_x
                let expr := _1
                /// @src 0:153:154  "2"
                let expr_1 := 0x02
                /// @src 0:149:154  "x * 2"
                let expr_2 := checked_mul_uint256(expr, convert_rational_by_to_uint256(expr_1))
                /// @src 0:142:154  "return x * 2"
                var := expr_2
                leave
            }
        }
        data ".metadata" hex"a2646970667358221220865b8b5fad68a92f4d65ddbaea0f41331d2f4dd89048d9ea5b7515ff8a58f4b964736f6c63430008260033"
    }
}
