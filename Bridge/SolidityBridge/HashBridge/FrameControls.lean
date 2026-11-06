import SolidityBridge.HashBridge.FrameHash
import SolidityBridge.HashBridge.ChargedControls

/-! Kernel controls: raw errors do not erase already executed direct queries.
No empty-padding equality, native fixture or whole-source witness is assumed. -/
namespace Solidity.HashBridge.FrameControls
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

/-- Fuel0 performs no successful edge, even for a KECCAK input state. -/
theorem zero_no_query (dest : Array UInt256) :
    DriverQueryReceipt 0 dest (ChargedControls.input 32 [.ofNat 0,.ofNat 0]) []
      (.error .OutOfFuel) := ⟨.zero dest _,.zero dest _⟩

/-- The SAME raw input executes one real checked hash and later errors at its
fuel1 continuation. The recorded query is retained even though no terminal
success state is publicly returned by the error. Query bytes remain symbolic. -/
theorem error_retains_query (dest : Array UInt256) :
    ∃ e, DriverQueryReceipt 2 dest (ChargedControls.input 32 [.ofNat 0,.ofNat 0])
      [byteQuery (machineQuery (ChargedControls.input 32 [.ofNat 0,.ofNat 0]).toMachineState
        (.ofNat 0) (.ofNat 0))] (.error e) ∧
      X 2 dest (ChargedControls.input 32 [.ofNat 0,.ofNat 0]) = .error e := by
  obtain ⟨next,edge,_,_⟩ := ChargedControls.actual_edge dest
  have hr : DriverQueryReceipt 2 dest (ChargedControls.input 32 [.ofNat 0,.ofNat 0])
      [byteQuery (machineQuery (ChargedControls.input 32 [.ofNat 0,.ofNat 0]).toMachineState
        (.ofNat 0) (.ofNat 0))]
      (X 2 dest (ChargedControls.input 32 [.ofNat 0,.ofNat 0])) :=
    edge.prepend_queries (ChargedControls.input_fetch 32 [.ofNat 0,.ofNat 0]) rfl
      (driver_one_queries dest next)
  obtain ⟨e,he⟩ := driver_one_error dest next
  have hx : X 2 dest (ChargedControls.input 32 [.ofNat 0,.ofNat 0]) = .error e :=
    edge.continues.trans he
  rw [hx] at hr
  exact ⟨e,hr,hx⟩

/-- No per-run collision premise is asserted here: the point is multiplicity
of the genuine query list, independent of the contents of the byte array. -/
theorem one_record_is_not_no_queries (bytes : ByteArray) :
    [byteQuery bytes] ≠ ([] : List (List Nat)) := by
  intro h
  cases h

end Solidity.HashBridge.FrameControls
