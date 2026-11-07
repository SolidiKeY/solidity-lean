import Solidity.Frontend.SolcJson.IrImport

/-! Kernel-checked path/channel and rejected-input controls for the JSON-only
IR extraction boundary. These fixtures do not authenticate solc or parse Yul. -/
namespace Solidity.Frontend.SolcJson.Ir.Controls
open Lean Solidity.SolcValidation

def entry : Json := Json.mkObj [("ir", .str "raw\n\"quoted\""), ("irOptimized", .str "optimized")]
def output : Json := Json.mkObj [("contracts", Json.mkObj [
  ("decoy.sol", Json.mkObj [("C", Json.mkObj [("ir", .str "decoy")])]),
  ("real.sol", Json.mkObj [("Decoy", Json.mkObj [("ir", .str "wrong")]), ("C", entry)])])]

def extracted (j : Json) (source name : String) (mode : IrMode) : Except String String :=
  (selectContract j source name mode).map (fun s => s.selection.text)

def nested (j : Json) : Json := Json.mkObj [("contracts", Json.mkObj [("real.sol", Json.mkObj [("C", j)])])]

theorem raw : extracted output "real.sol" "C" .unoptimized = .ok "raw\n\"quoted\"" := rfl

theorem optimized : extracted output "real.sol" "C" .optimized = .ok "optimized" := rfl

theorem other_source : extracted output "decoy.sol" "C" .unoptimized = .ok "decoy" := rfl

theorem other_contract : extracted output "real.sol" "Decoy" .unoptimized = .ok "wrong" := rfl

theorem empty_string : extracted (nested (Json.mkObj [("ir", .str "")])) "real.sol" "C" .unoptimized = .ok "" := rfl

theorem absent_contracts : (extracted (Json.mkObj []) "real.sol" "C" .unoptimized).isOk = false := rfl

theorem root_null : (extracted (Json.null) "real.sol" "C" .unoptimized).isOk = false := rfl

theorem contracts_null : (extracted (Json.mkObj [("contracts", .null)]) "real.sol" "C" .unoptimized).isOk = false := rfl

theorem source_null : (extracted (Json.mkObj [("contracts", Json.mkObj [("real.sol", .null)])]) "real.sol" "C" .unoptimized).isOk = false := rfl

theorem contract_null : (extracted (nested .null) "real.sol" "C" .unoptimized).isOk = false := rfl

theorem missing_source : (extracted (output) "wrong.sol" "C" .unoptimized).isOk = false := rfl

theorem missing_contract : (extracted (output) "real.sol" "Wrong" .unoptimized).isOk = false := rfl

theorem missing_raw : (extracted (nested (Json.mkObj [("irOptimized", .str "optimized")])) "real.sol" "C" .unoptimized).isOk = false := rfl

theorem missing_optimized : (extracted (nested (Json.mkObj [("ir", .str "raw")])) "real.sol" "C" .optimized).isOk = false := rfl

theorem wrong_channel_spelling : (extracted (nested (Json.mkObj [("ir-optimized", .str "wrong")])) "real.sol" "C" .optimized).isOk = false := rfl

theorem number_channel : (extracted (nested (Json.mkObj [("ir", .num 7)])) "real.sol" "C" .unoptimized).isOk = false := rfl

theorem bool_channel : (extracted (nested (Json.mkObj [("ir", .bool true)])) "real.sol" "C" .unoptimized).isOk = false := rfl

theorem null_channel : (extracted (nested (Json.mkObj [("ir", .null)])) "real.sol" "C" .unoptimized).isOk = false := rfl

theorem object_channel : (extracted (nested (Json.mkObj [("ir", Json.mkObj [])])) "real.sol" "C" .unoptimized).isOk = false := rfl

theorem lookup_witness : lookup output "real.sol" "C" .unoptimized = .ok "raw\n\"quoted\"" := rfl

theorem inhabited_complete : ∃ selection,
    selectContract output "real.sol" "C" .unoptimized = .ok selection ∧
    selection.selection.text = "raw\n\"quoted\"" :=
  ContractSelection.complete lookup_witness

theorem no_fallback : lookup output "wrong.sol" "C" .unoptimized ≠ .ok "decoy" := by
  intro h
  have impossible : false = true := congrArg Except.isOk h
  cases impossible

#print axioms raw
#print axioms optimized
#print axioms other_source
#print axioms other_contract
#print axioms empty_string
#print axioms absent_contracts
#print axioms root_null
#print axioms contracts_null
#print axioms source_null
#print axioms contract_null
#print axioms missing_source
#print axioms missing_contract
#print axioms missing_raw
#print axioms missing_optimized
#print axioms wrong_channel_spelling
#print axioms number_channel
#print axioms bool_channel
#print axioms null_channel
#print axioms object_channel
#print axioms lookup_witness
#print axioms inhabited_complete
#print axioms no_fallback
end Solidity.Frontend.SolcJson.Ir.Controls
