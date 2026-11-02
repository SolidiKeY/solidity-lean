import Solidity.Frontend.Import

/-! Standalone website imports must retain calldata origins while expanding
local aliases and slices. Synthetic memory parameter declarations must not
shadow the original calldata names. The written-copy refusal stays in force. -/

solc_import "../../tests/solc/CalldataValidation.ast.json" hash 0xbc741802a7ad102c as Calldata testing

#guard (Calldata.report.find? (·.sourceName == "first")).any (·.status == .elaborated)
#guard (Calldata.report.find? (·.sourceName == "localAlias")).any (·.status == .elaborated)
#guard (Calldata.report.find? (·.sourceName == "sliceRead")).any (·.status == .elaborated)
#guard (Calldata.report.find? (·.sourceName == "writesCopy")).any (·.status == .unsupported)
