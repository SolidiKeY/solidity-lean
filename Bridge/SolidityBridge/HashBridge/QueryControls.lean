import SolidityBridge.HashBridge.QueryUnique
import SolidityBridge.HashBridge.FrameControls

/-! Fixed-run witness-independence controls. These reuse the actual checked
hash-then-error input; they are kernel controls, not source/native fixtures. -/
namespace Solidity.HashBridge.QueryControls
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

abbrev input : EVM.State := ChargedControls.input 32 [.ofNat 0,.ofNat 0]
def observedQuery : List Nat := byteQuery (machineQuery input.toMachineState (.ofNat 0) (.ofNat 0))

/-- Neither an alternative proof nor a different result index permits dropping
the real executed query from this fixed input/fuel. Bytes remain symbolic. -/
theorem recorded_list_for_input (dest : Array UInt256) (queries : List (List Nat))
    (result : Except ExecutionException (ExecutionResult EVM.State))
    (receipt : DriverQueryReceipt 2 dest input queries result) :
    queries = [observedQuery] := by
  obtain ⟨e,actual,_⟩ := FrameControls.error_retains_query dest
  exact query_receipt_unique 2 dest input queries [observedQuery] result (.error e) receipt actual

/-- A favorable empty log cannot be substituted merely because the final
operational result is an error. Empty BYTE contents are not identified here. -/
theorem no_empty_receipt (dest : Array UInt256)
    (result : Except ExecutionException (ExecutionResult EVM.State)) :
    ¬ DriverQueryReceipt 2 dest input [] result := by
  intro receipt
  have h : ([] : List (List Nat)) = [observedQuery] := recorded_list_for_input dest [] result receipt
  cases h

end Solidity.HashBridge.QueryControls
