import SolidityBridge.HashBridge.HashCuts
import SolidityBridge.HashBridge.ChargedControls

/-! A concrete same-run cursor after the checked hash but before its later
error. Raw controls, not source/native fixtures or canonical empty-byte claims. -/
namespace Solidity.HashBridge.CutControls
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

abbrev input : EVM.State := ChargedControls.input 32 [.ofNat 0,.ofNat 0]
def observedQuery : List Nat := byteQuery (machineQuery input.toMachineState (.ofNat 0) (.ofNat 0))

/-- The cursor is produced by the actual checked edge, with real gas/PC.
Public error has no invented poststate; the cursor is internal prefix evidence. -/
theorem actual_error_cut (dest : Array UInt256) :
    ∃ next e, DriverQueryCut 2 dest input [observedQuery] (.error e)
        1 next [observedQuery] [] ∧
      next.gasAvailable = .ofNat 2 ∧ next.pc = .ofNat 1 ∧ X 2 dest input = .error e := by
  obtain ⟨next,edge,hgas,hpc⟩ := ChargedControls.actual_edge dest
  have path : DriverQueryCut 2 dest input [observedQuery] (X 2 dest input)
      1 next [observedQuery] [] :=
    edge.query_cut (ChargedControls.input_fetch 32 [.ofNat 0,.ofNat 0]) rfl
      (driver_one_queries dest next)
  obtain ⟨e,he⟩ := driver_one_error dest next
  have hx : X 2 dest input = .error e := edge.continues.trans he
  rw [hx] at path
  exact ⟨next,e,path,hgas,hpc,hx⟩

end Solidity.HashBridge.CutControls
