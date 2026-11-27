import Solidity.Frontend.SolcJson.IrImportControls

/-! Literal JSON channel/path controls. These checks extract text; they do not
authenticate a compiler invocation or parse the selected IR. -/
namespace Solidity.Examples.FrontendValidation.SolcJson.Ir
open Lean Solidity.Frontend.SolcJson.Ir

private def channels : Json := Json.mkObj [
  ("ir", .str "raw"), ("irOptimized", .str "optimized")]

private def output : Json := Json.mkObj [("contracts", Json.mkObj [
  ("a.sol", Json.mkObj [("C", channels)]),
  ("b.sol", Json.mkObj [("C", Json.mkObj [("ir", .str "decoy")])])])]

#guard ((select channels .unoptimized).map Selection.text).toOption == some "raw"
#guard ((select channels .optimized).map Selection.text).toOption == some "optimized"
#guard (select (Json.mkObj [("ir", .bool true)]) .unoptimized).toOption.isNone
#guard (select (Json.mkObj [("ir", .str "raw")]) .optimized).toOption.isNone

#guard ((selectContract output "a.sol" "C" .unoptimized).map
  (fun selected => selected.selection.text)).toOption == some "raw"
#guard (selectContract output "missing.sol" "C" .unoptimized).toOption.isNone
#guard (selectContract output "a.sol" "Missing" .unoptimized).toOption.isNone

#guard (lookup output "a.sol" "C" .optimized).toOption == some "optimized"
#guard (lookup output "a.sol" "C" .unoptimized).toOption == some "raw"
#guard (lookup output "b.sol" "C" .unoptimized).toOption == some "decoy"
#guard (lookup output "b.sol" "C" .optimized).toOption.isNone
#guard (lookup output "missing.sol" "C" .unoptimized).toOption.isNone

#guard (Controls.extracted output "a.sol" "C" .optimized).toOption == some "optimized"
#guard (Controls.extracted output "a.sol" "Missing" .optimized).toOption.isNone

end Solidity.Examples.FrontendValidation.SolcJson.Ir
