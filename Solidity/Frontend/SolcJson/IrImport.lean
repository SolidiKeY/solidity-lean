import Lean.Data.Json.Parser
import Lean.Data.Json.FromToJson.Basic
import Solidity.SolcValidation.Dialect

/-!
# Exact extraction of solc's IR output channels

This frontend boundary retains a derivation of the selected JSON string. It
neither authenticates compiler execution nor parses the Yul body. Those gates
must precede typed semantic matching; arbitrary JSON is not trusted code.
-/
namespace Solidity.Frontend.SolcJson.Ir
open Lean
open Solidity.SolcValidation

def field : IrMode → String
  | .unoptimized => "ir"
  | .optimized => "irOptimized"

/-- The exact string selected from one standard-JSON contract entry. -/
structure Selection (contract : Json) (mode : IrMode) where
  text : String
  selected : contract.getObjValAs? String (field mode) = .ok text

def select (contract : Json) (mode : IrMode) : Except String (Selection contract mode) :=
  match h : contract.getObjValAs? String (field mode) with
  | .error reason => .error reason
  | .ok text => .ok ⟨text, h⟩

/-- Selection retains the exact JSON lookup equality, preserving the selected String (JSON escapes are already decoded). -/
theorem Selection.sound {contract : Json} {mode : IrMode}
    (selection : Selection contract mode) :
    contract.getObjValAs? String (field mode) = .ok selection.text :=
  selection.selected

/-- Every existing lookup derivation is reproduced by the extractor. -/
theorem Selection.complete {contract : Json} {mode : IrMode}
    (selection : Selection contract mode) :
    select contract mode = .ok selection := by
  cases selection with
  | mk text selected =>
      unfold select
      split
      · next reason h => cases (h.symm.trans selected)
      · next value h =>
          have same : value = text := Except.ok.inj (h.symm.trans selected)
          subst value
          rfl

/-- Retain the source-file/contract path, not a guessed first contract. -/
structure ContractSelection (output : Json) (source name : String) (mode : IrMode) where
  contracts : Json
  sourceContracts : Json
  contract : Json
  contracts_eq : output.getObjVal? "contracts" = .ok contracts
  source_eq : contracts.getObjVal? source = .ok sourceContracts
  contract_eq : sourceContracts.getObjVal? name = .ok contract
  selection : Selection contract mode

def selectContract (output : Json) (source name : String) (mode : IrMode) :
    Except String (ContractSelection output source name mode) := do
  let contracts ← match h : output.getObjVal? "contracts" with
    | .error reason => .error reason
    | .ok value => .ok (⟨value, h⟩ : {value : Json // output.getObjVal? "contracts" = .ok value})
  let sourceContracts ← match h : contracts.val.getObjVal? source with
    | .error reason => .error reason
    | .ok value => .ok (⟨value, h⟩ : {value : Json // contracts.val.getObjVal? source = .ok value})
  let contract ← match h : sourceContracts.val.getObjVal? name with
    | .error reason => .error reason
    | .ok value => .ok (⟨value, h⟩ : {value : Json // sourceContracts.val.getObjVal? name = .ok value})
  let selection ← select contract.val mode
  return ⟨contracts.val, sourceContracts.val, contract.val,
    contracts.property, sourceContracts.property, contract.property, selection⟩

/-- Ordinary lookup used to state the complete source/contract/channel path. -/
def lookup (output : Json) (source name : String) (mode : IrMode) : Except String String := do
  let contracts ← output.getObjVal? "contracts"
  let sourceContracts ← contracts.getObjVal? source
  let contract ← sourceContracts.getObjVal? name
  contract.getObjValAs? String (field mode)

/-- Every returned selection certifies the full JSON path and exact channel. -/
theorem ContractSelection.sound {output : Json} {source name : String} {mode : IrMode}
    (selection : ContractSelection output source name mode) :
    lookup output source name mode = .ok selection.selection.text := by
  simp only [lookup, selection.contracts_eq, selection.source_eq,
    selection.contract_eq, bind, Except.bind, selection.selection.selected]

end Solidity.Frontend.SolcJson.Ir
