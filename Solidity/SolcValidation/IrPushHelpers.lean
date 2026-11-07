import Solidity.SolcValidation.IrParse
import Solidity.SolcValidation.IrEval

/-!
# solc's storage-array push, as imported

`pushHelpersText` is the verbatim text of the thirteen functions of solc 0.8.38's
`array_push_from_t_uint256_to_t_array$_t_uint256_$dyn_storage_ptr` group, cut from
the saved `--ir` output of `Census` (`tests/fullscope-20261104/vt1/extract-helpers.py`),
and its tree printed from the parser's output (`IrLeanGen.lean`, split by
`gen-helper-modules.py`); `pushHelpers_certified` re-checks it against the text by
kernel evaluation.
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

def pushHelpersText : String :=
  "object \"PushHelpers\" {\n    code {\n        function cleanup_t_uint256(value) -> cleaned {\n            cleaned := value\n        }\n\n        function panic_error_0x41() {\n            mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)\n            mstore(4, 0x41)\n            revert(0, 0x24)\n        }\n\n        function panic_error_0x32() {\n            mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)\n            mstore(4, 0x32)\n            revert(0, 0x24)\n        }\n\n        function array_length_t_array$_t_uint256_$dyn_storage_ptr(value) -> length {\n\n            length := sload(value)\n\n        }\n\n        function array_dataslot_t_array$_t_uint256_$dyn_storage_ptr(ptr) -> data {\n            data := ptr\n\n            mstore(0, ptr)\n            data := keccak256(0, 0x20)\n\n        }\n\n        function storage_array_index_access_t_array$_t_uint256_$dyn_storage_ptr(array, index) -> slot, offset {\n            let arrayLength := array_length_t_array$_t_uint256_$dyn_storage_ptr(array)\n            if iszero(lt(index, arrayLength)) { panic_error_0x32() }\n\n            let dataArea := array_dataslot_t_array$_t_uint256_$dyn_storage_ptr(array)\n            slot := add(dataArea, mul(index, 1))\n            offset := 0\n\n        }\n\n        function shift_left_dynamic(bits, value) -> newValue {\n            newValue :=\n\n            shl(bits, value)\n\n        }\n\n        function update_byte_slice_dynamic32(value, shiftBytes, toInsert) -> result {\n            let shiftBits := mul(shiftBytes, 8)\n            let mask := shift_left_dynamic(shiftBits, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)\n            toInsert := shift_left_dynamic(shiftBits, toInsert)\n            value := and(value, not(mask))\n            result := or(value, and(toInsert, mask))\n        }\n\n        function identity(value) -> ret {\n            ret := value\n        }\n\n        function convert_t_uint256_to_t_uint256(value) -> converted {\n            converted := cleanup_t_uint256(identity(cleanup_t_uint256(value)))\n        }\n\n        function prepare_store_t_uint256(value) -> ret {\n            ret := value\n        }\n\n        function update_storage_value_t_uint256_to_t_uint256(slot, offset, value_0) {\n            let convertedValue_0 := convert_t_uint256_to_t_uint256(value_0)\n            sstore(slot, update_byte_slice_dynamic32(sload(slot), offset, prepare_store_t_uint256(convertedValue_0)))\n        }\n\n        function array_push_from_t_uint256_to_t_array$_t_uint256_$dyn_storage_ptr(array , value0) {\n\n            let oldLen := sload(array)\n            if iszero(lt(oldLen, 18446744073709551616)) { panic_error_0x41() }\n            sstore(array, add(oldLen, 1))\n            let slot, offset := storage_array_index_access_t_array$_t_uint256_$dyn_storage_ptr(array, oldLen)\n            update_storage_value_t_uint256_to_t_uint256(slot, offset , value0)\n\n        }\n    }\n}\n"

def pushSigs : List FnSig :=
  [⟨"cleanup_t_uint256", ["value"], ["cleaned"]⟩, ⟨"panic_error_0x41", [], []⟩, ⟨"panic_error_0x32", [], []⟩, ⟨"array_length_t_array$_t_uint256_$dyn_storage_ptr", ["value"], ["length"]⟩, ⟨"array_dataslot_t_array$_t_uint256_$dyn_storage_ptr", ["ptr"], ["data"]⟩, ⟨"storage_array_index_access_t_array$_t_uint256_$dyn_storage_ptr", ["array", "index"], ["slot", "offset"]⟩, ⟨"shift_left_dynamic", ["bits", "value"], ["newValue"]⟩, ⟨"update_byte_slice_dynamic32", ["value", "shiftBytes", "toInsert"], ["result"]⟩, ⟨"identity", ["value"], ["ret"]⟩, ⟨"convert_t_uint256_to_t_uint256", ["value"], ["converted"]⟩, ⟨"prepare_store_t_uint256", ["value"], ["ret"]⟩, ⟨"update_storage_value_t_uint256_to_t_uint256", ["slot", "offset", "value_0"], []⟩, ⟨"array_push_from_t_uint256_to_t_array$_t_uint256_$dyn_storage_ptr", ["array", "value0"], []⟩]

abbrev PushBody (params rets : List String) :=
  Block (pushSigs ++ []) ⟨true, false⟩ (params ++ rets)

def pushCleanupU : PushBody ["value"] ["cleaned"] :=
  (.mk [] .nil (.stmt (.assign [⟨"cleaned", (.there .here)⟩] (.var "value" .here)) .nil))

def pushPanic41 : PushBody [] [] :=
  (.mk [] .nil (.stmt (.discard (.op (.evm .«mstore») (.cons (.lit ⟨.num 0, 0, rfl⟩) (.cons (.lit ⟨.num 35408467139433450592217433187231851964531694900788300625387963629091585785856, 35408467139433450592217433187231851964531694900788300625387963629091585785856, rfl⟩) .nil)))) (.stmt (.discard (.op (.evm .«mstore») (.cons (.lit ⟨.num 4, 4, rfl⟩) (.cons (.lit ⟨.num 65, 65, rfl⟩) .nil)))) (.stmt (.discard (.op (.evm .«revert») (.cons (.lit ⟨.num 0, 0, rfl⟩) (.cons (.lit ⟨.num 36, 36, rfl⟩) .nil)))) .nil))))

def pushPanic32 : PushBody [] [] :=
  (.mk [] .nil (.stmt (.discard (.op (.evm .«mstore») (.cons (.lit ⟨.num 0, 0, rfl⟩) (.cons (.lit ⟨.num 35408467139433450592217433187231851964531694900788300625387963629091585785856, 35408467139433450592217433187231851964531694900788300625387963629091585785856, rfl⟩) .nil)))) (.stmt (.discard (.op (.evm .«mstore») (.cons (.lit ⟨.num 4, 4, rfl⟩) (.cons (.lit ⟨.num 50, 50, rfl⟩) .nil)))) (.stmt (.discard (.op (.evm .«revert») (.cons (.lit ⟨.num 0, 0, rfl⟩) (.cons (.lit ⟨.num 36, 36, rfl⟩) .nil)))) .nil))))

def pushLength : PushBody ["value"] ["length"] :=
  (.mk [] .nil (.stmt (.assign [⟨"length", (.there .here)⟩] (.op (.evm .«sload») (.cons (.var "value" .here) .nil))) .nil))

def pushDataSlot : PushBody ["ptr"] ["data"] :=
  (.mk [] .nil (.stmt (.assign [⟨"data", (.there .here)⟩] (.var "ptr" .here)) (.stmt (.discard (.op (.evm .«mstore») (.cons (.lit ⟨.num 0, 0, rfl⟩) (.cons (.var "ptr" .here) .nil)))) (.stmt (.assign [⟨"data", (.there .here)⟩] (.op (.evm .«keccak256») (.cons (.lit ⟨.num 0, 0, rfl⟩) (.cons (.lit ⟨.num 32, 32, rfl⟩) .nil)))) .nil))))

def pushIndexAccess : PushBody ["array", "index"] ["slot", "offset"] :=
  (.mk [] .nil (.let_ ["arrayLength"] (some (.call (.there (.there (.there .here))) (.cons (.var "array" .here) .nil))) (.stmt (.if_ (.op (.evm (.pure .«iszero»)) (.cons (.op (.evm (.pure .«lt»)) (.cons (.var "index" (.there (.there .here))) (.cons (.var "arrayLength" .here) .nil))) .nil)) (.mk [] .nil (.stmt (.discard (.call (.there (.there .here)) .nil)) .nil))) (.let_ ["dataArea"] (some (.call (.there (.there (.there (.there .here)))) (.cons (.var "array" (.there .here)) .nil))) (.stmt (.assign [⟨"slot", (.there (.there (.there (.there .here))))⟩] (.op (.evm (.pure .«add»)) (.cons (.var "dataArea" .here) (.cons (.op (.evm (.pure .«mul»)) (.cons (.var "index" (.there (.there (.there .here)))) (.cons (.lit ⟨.num 1, 1, rfl⟩) .nil))) .nil)))) (.stmt (.assign [⟨"offset", (.there (.there (.there (.there (.there .here)))))⟩] (.lit ⟨.num 0, 0, rfl⟩)) .nil))))))

def pushShiftLeft : PushBody ["bits", "value"] ["newValue"] :=
  (.mk [] .nil (.stmt (.assign [⟨"newValue", (.there (.there .here))⟩] (.op (.evm (.pure .«shl»)) (.cons (.var "bits" .here) (.cons (.var "value" (.there .here)) .nil)))) .nil))

def pushUpdateSlice : PushBody ["value", "shiftBytes", "toInsert"] ["result"] :=
  (.mk [] .nil (.let_ ["shiftBits"] (some (.op (.evm (.pure .«mul»)) (.cons (.var "shiftBytes" (.there .here)) (.cons (.lit ⟨.num 8, 8, rfl⟩) .nil)))) (.let_ ["mask"] (some (.call (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.var "shiftBits" .here) (.cons (.lit ⟨.num 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, rfl⟩) .nil)))) (.stmt (.assign [⟨"toInsert", (.there (.there (.there (.there .here))))⟩] (.call (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.var "shiftBits" (.there .here)) (.cons (.var "toInsert" (.there (.there (.there (.there .here))))) .nil)))) (.stmt (.assign [⟨"value", (.there (.there .here))⟩] (.op (.evm (.pure .«and»)) (.cons (.var "value" (.there (.there .here))) (.cons (.op (.evm (.pure .«not»)) (.cons (.var "mask" .here) .nil)) .nil)))) (.stmt (.assign [⟨"result", (.there (.there (.there (.there (.there .here)))))⟩] (.op (.evm (.pure .«or»)) (.cons (.var "value" (.there (.there .here))) (.cons (.op (.evm (.pure .«and»)) (.cons (.var "toInsert" (.there (.there (.there (.there .here))))) (.cons (.var "mask" .here) .nil))) .nil)))) .nil))))))

def pushIdentity : PushBody ["value"] ["ret"] :=
  (.mk [] .nil (.stmt (.assign [⟨"ret", (.there .here)⟩] (.var "value" .here)) .nil))

def pushConvert : PushBody ["value"] ["converted"] :=
  (.mk [] .nil (.stmt (.assign [⟨"converted", (.there .here)⟩] (.call .here (.cons (.call (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.call .here (.cons (.var "value" .here) .nil)) .nil)) .nil))) .nil))

def pushPrepareStore : PushBody ["value"] ["ret"] :=
  (.mk [] .nil (.stmt (.assign [⟨"ret", (.there .here)⟩] (.var "value" .here)) .nil))

def pushUpdateStorage : PushBody ["slot", "offset", "value_0"] [] :=
  (.mk [] .nil (.let_ ["convertedValue_0"] (some (.call (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.var "value_0" (.there (.there .here))) .nil))) (.stmt (.discard (.op (.evm .«sstore») (.cons (.var "slot" (.there .here)) (.cons (.call (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.op (.evm .«sload») (.cons (.var "slot" (.there .here)) .nil)) (.cons (.var "offset" (.there (.there .here))) (.cons (.call (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.var "convertedValue_0" .here) .nil)) .nil)))) .nil)))) .nil)))

def pushPush : PushBody ["array", "value0"] [] :=
  (.mk [] .nil (.let_ ["oldLen"] (some (.op (.evm .«sload») (.cons (.var "array" .here) .nil))) (.stmt (.if_ (.op (.evm (.pure .«iszero»)) (.cons (.op (.evm (.pure .«lt»)) (.cons (.var "oldLen" .here) (.cons (.lit ⟨.num 18446744073709551616, 18446744073709551616, rfl⟩) .nil))) .nil)) (.mk [] .nil (.stmt (.discard (.call (.there .here) .nil)) .nil))) (.stmt (.discard (.op (.evm .«sstore») (.cons (.var "array" (.there .here)) (.cons (.op (.evm (.pure .«add»)) (.cons (.var "oldLen" .here) (.cons (.lit ⟨.num 1, 1, rfl⟩) .nil))) .nil)))) (.let_ ["slot", "offset"] (some (.call (.there (.there (.there (.there (.there .here))))) (.cons (.var "array" (.there .here)) (.cons (.var "oldLen" .here) .nil)))) (.stmt (.discard (.call (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.var "slot" .here) (.cons (.var "offset" (.there .here)) (.cons (.var "value0" (.there (.there (.there (.there .here))))) .nil))))) .nil))))))

def pushBodies : Bodies (pushSigs ++ []) pushSigs :=
  (.cons pushCleanupU (.cons pushPanic41 (.cons pushPanic32 (.cons pushLength (.cons pushDataSlot (.cons pushIndexAccess (.cons pushShiftLeft (.cons pushUpdateSlice (.cons pushIdentity (.cons pushConvert (.cons pushPrepareStore (.cons pushUpdateStorage (.cons pushPush .nil)))))))))))))

def pushItems : Items (pushSigs ++ []) ⟨false, false⟩ [] pushSigs.length :=
  (.fn ⟨0, by decide⟩ (.fn ⟨1, by decide⟩ (.fn ⟨2, by decide⟩ (.fn ⟨3, by decide⟩ (.fn ⟨4, by decide⟩ (.fn ⟨5, by decide⟩ (.fn ⟨6, by decide⟩ (.fn ⟨7, by decide⟩ (.fn ⟨8, by decide⟩ (.fn ⟨9, by decide⟩ (.fn ⟨10, by decide⟩ (.fn ⟨11, by decide⟩ (.fn ⟨12, by decide⟩ .nil)))))))))))))

def pushHelpersCode : Code := .mk pushSigs pushBodies pushItems

def pushHelpersRoot : Object Code := .object "PushHelpers" pushHelpersCode []

/-- The generated tree carries the same certificate as a parse of the text. -/
theorem pushHelpers_certified :
    lex pushHelpersText = some (objectToks pushHelpersRoot) ∧ objectWf pushHelpersRoot = true := by
  decide +kernel

end Solidity.SolcValidation.IrSyntax
