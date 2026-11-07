import Solidity.SolcValidation.IrParse
import Solidity.SolcValidation.IrEval

/-!
# solc's `uint256` calldata decoder, as imported

`abiHelpersText` is the verbatim text of the five functions of solc 0.8.38's
`abi_decode_tuple_t_uint256` group, cut from the saved `--ir` output of `Census`
(`tests/fullscope-20261104/vt1/extract-helpers.py`), and its tree printed from the
parser's output (`IrLeanGen.lean`, split by `gen-helper-modules.py`);
`abiHelpers_certified` re-checks it against the text by kernel evaluation.
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

def abiHelpersText : String :=
  "object \"AbiHelpers\" {\n    code {\n        function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() {\n            revert(0, 0)\n        }\n\n        function cleanup_t_uint256(value) -> cleaned {\n            cleaned := value\n        }\n\n        function validator_revert_t_uint256(value) {\n            if iszero(eq(value, cleanup_t_uint256(value))) { revert(0, 0) }\n        }\n\n            function abi_decode_t_uint256(offset, end) -> value {\n                value := calldataload(offset)\n                validator_revert_t_uint256(value)\n            }\n\n            function abi_decode_tuple_t_uint256(headStart, dataEnd) -> value0 {\n                if slt(sub(dataEnd, headStart), 32) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }\n\n                {\n\n                    let offset := 0\n\n                    value0 := abi_decode_t_uint256(add(headStart, offset), dataEnd)\n                }\n\n            }\n    }\n}\n"

def abiSigs : List FnSig :=
  [⟨"revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b", [], []⟩, ⟨"cleanup_t_uint256", ["value"], ["cleaned"]⟩, ⟨"validator_revert_t_uint256", ["value"], []⟩, ⟨"abi_decode_t_uint256", ["offset", "end"], ["value"]⟩, ⟨"abi_decode_tuple_t_uint256", ["headStart", "dataEnd"], ["value0"]⟩]

abbrev AbiBody (params rets : List String) :=
  Block (abiSigs ++ []) ⟨true, false⟩ (params ++ rets)

def abiRevert : AbiBody [] [] :=
  (.mk [] .nil (.stmt (.discard (.op (.evm .«revert») (.cons (.lit ⟨.num 0, 0, rfl⟩) (.cons (.lit ⟨.num 0, 0, rfl⟩) .nil)))) .nil))

def abiCleanupU : AbiBody ["value"] ["cleaned"] :=
  (.mk [] .nil (.stmt (.assign [⟨"cleaned", (.there .here)⟩] (.var "value" .here)) .nil))

def abiValidator : AbiBody ["value"] [] :=
  (.mk [] .nil (.stmt (.if_ (.op (.evm (.pure .«iszero»)) (.cons (.op (.evm (.pure .«eq»)) (.cons (.var "value" .here) (.cons (.call (.there .here) (.cons (.var "value" .here) .nil)) .nil))) .nil)) (.mk [] .nil (.stmt (.discard (.op (.evm .«revert») (.cons (.lit ⟨.num 0, 0, rfl⟩) (.cons (.lit ⟨.num 0, 0, rfl⟩) .nil)))) .nil))) .nil))

def abiDecodeU256 : AbiBody ["offset", "end"] ["value"] :=
  (.mk [] .nil (.stmt (.assign [⟨"value", (.there (.there .here))⟩] (.op (.evm .«calldataload») (.cons (.var "offset" .here) .nil))) (.stmt (.discard (.call (.there (.there .here)) (.cons (.var "value" (.there (.there .here))) .nil))) .nil)))

def abiDecodeTuple : AbiBody ["headStart", "dataEnd"] ["value0"] :=
  (.mk [] .nil (.stmt (.if_ (.op (.evm (.pure .«slt»)) (.cons (.op (.evm (.pure .«sub»)) (.cons (.var "dataEnd" (.there .here)) (.cons (.var "headStart" .here) .nil))) (.cons (.lit ⟨.num 32, 32, rfl⟩) .nil))) (.mk [] .nil (.stmt (.discard (.call .here .nil)) .nil))) (.stmt (.block (.mk [] .nil (.let_ ["offset"] (some (.lit ⟨.num 0, 0, rfl⟩)) (.stmt (.assign [⟨"value0", (.there (.there (.there .here)))⟩] (.call (.there (.there (.there .here))) (.cons (.op (.evm (.pure .«add»)) (.cons (.var "headStart" (.there .here)) (.cons (.var "offset" .here) .nil))) (.cons (.var "dataEnd" (.there (.there .here))) .nil)))) .nil)))) .nil)))

def abiBodies : Bodies (abiSigs ++ []) abiSigs :=
  (.cons abiRevert (.cons abiCleanupU (.cons abiValidator (.cons abiDecodeU256 (.cons abiDecodeTuple .nil)))))

def abiItems : Items (abiSigs ++ []) ⟨false, false⟩ [] abiSigs.length :=
  (.fn ⟨0, by decide⟩ (.fn ⟨1, by decide⟩ (.fn ⟨2, by decide⟩ (.fn ⟨3, by decide⟩ (.fn ⟨4, by decide⟩ .nil)))))

def abiHelpersCode : Code := .mk abiSigs abiBodies abiItems

def abiHelpersRoot : Object Code := .object "AbiHelpers" abiHelpersCode []

/-- The generated tree carries the same certificate as a parse of the text. -/
theorem abiHelpers_certified :
    lex abiHelpersText = some (objectToks abiHelpersRoot) ∧ objectWf abiHelpersRoot = true := by
  decide +kernel

end Solidity.SolcValidation.IrSyntax
