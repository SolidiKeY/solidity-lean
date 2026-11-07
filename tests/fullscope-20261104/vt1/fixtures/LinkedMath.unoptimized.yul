
/// @use-src 0:"Census.sol"
object "LinkedMath_14" {
    code {
        /// @src 0:63:159  "library LinkedMath {..."
        mstore(64, memoryguard(128))
        if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }

        let _1 := allocate_unbounded()
        codecopy(_1, dataoffset("LinkedMath_14_deployed"), datasize("LinkedMath_14_deployed"))

        setimmutable(_1, "library_deploy_address", address())

        return(_1, datasize("LinkedMath_14_deployed"))

        function allocate_unbounded() -> memPtr {
            memPtr := mload(64)
        }

        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() {
            revert(0, 0)
        }

        /// @src 0:63:159  "library LinkedMath {..."
        function constructor_LinkedMath_14() {

            /// @src 0:63:159  "library LinkedMath {..."

        }
        /// @src 0:63:159  "library LinkedMath {..."

    }
    /// @use-src 0:"Census.sol"
    object "LinkedMath_14_deployed" {
        code {
            /// @src 0:63:159  "library LinkedMath {..."
            mstore(64, memoryguard(128))

            let called_via_delegatecall := iszero(eq(loadimmutable("library_deploy_address"), address()))

            if gt(calldatasize(), 3)
            {
                let selector := shift_right_224_unsigned(calldataload(0))
                switch selector

                case 0x3cf3bbf4
                {
                    // twice(uint256)

                    external_fun_twice_13()
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

            function abi_encode_t_uint256_to_t_uint256_fromStack_library(value, pos) {
                mstore(pos, cleanup_t_uint256(value))
            }

            function abi_encode_tuple_t_uint256__to_t_uint256__fromStack_library(headStart , value0) -> tail {
                tail := add(headStart, 32)

                abi_encode_t_uint256_to_t_uint256_fromStack_library(value0,  add(headStart, 0))

            }

            function external_fun_twice_13() {

                let param_0 :=  abi_decode_tuple_t_uint256(4, calldatasize())
                let ret_0 :=  fun_twice_13(param_0)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_uint256__to_t_uint256__fromStack_library(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74() {
                revert(0, 0)
            }

            function zero_value_for_split_t_uint256() -> ret {
                ret := 0
            }

            function cleanup_t_rational_2_by_1(value) -> cleaned {
                cleaned := value
            }

            function identity(value) -> ret {
                ret := value
            }

            function convert_t_rational_2_by_1_to_t_uint256(value) -> converted {
                converted := cleanup_t_uint256(identity(cleanup_t_rational_2_by_1(value)))
            }

            function panic_error_0x11() {
                mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                mstore(4, 0x11)
                revert(0, 0x24)
            }

            function checked_mul_t_uint256(x, y) -> product {
                x := cleanup_t_uint256(x)
                y := cleanup_t_uint256(y)
                let product_raw := mul(x, y)
                product := cleanup_t_uint256(product_raw)

                // overflow, if x != 0 and y != product/x
                if iszero(
                    or(
                        iszero(x),
                        eq(y, div(product, x))
                    )
                ) { panic_error_0x11() }

            }

            /// @ast-id 13
            /// @src 0:88:157  "function twice(uint x) external pure returns (uint) { return x * 2; }"
            function fun_twice_13(var_x_3) -> var__6 {
                /// @src 0:134:138  "uint"
                let zero_t_uint256_1 := zero_value_for_split_t_uint256()
                var__6 := zero_t_uint256_1

                /// @src 0:149:150  "x"
                let _2 := var_x_3
                let expr_8 := _2
                /// @src 0:153:154  "2"
                let expr_9 := 0x02
                /// @src 0:149:154  "x * 2"
                let expr_10 := checked_mul_t_uint256(expr_8, convert_t_rational_2_by_1_to_t_uint256(expr_9))

                /// @src 0:142:154  "return x * 2"
                var__6 := expr_10
                leave

            }
            /// @src 0:63:159  "library LinkedMath {..."

        }

        data ".metadata" hex"a2646970667358221220865b8b5fad68a92f4d65ddbaea0f41331d2f4dd89048d9ea5b7515ff8a58f4b964736f6c63430008260033"
    }

}

