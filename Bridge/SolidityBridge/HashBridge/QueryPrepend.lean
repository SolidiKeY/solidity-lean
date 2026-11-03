import SolidityBridge.HashBridge.FrameSound

/-! Receipt transport across one existing checked nonterminal step. This only
composes checked producers; it neither selects their result nor runs a new evaluator. -/
namespace Solidity.HashBridge
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

theorem query_receipt_prepend (fuel cost : Nat) (dest : Array UInt256)
    (s charged next : EVM.State) (queries : List (List Nat))
    (result : Except ExecutionException (ExecutionResult EVM.State))
    (hc : checks dest s = .ok (charged,cost))
    (he : step (fuel+1) cost (some (fetched s)) charged = .ok next)
    (hh : terminalData next (fetched s).1 = none)
    (rest : DriverQueryReceipt (fuel+1) dest next queries result) :
    DriverQueryReceipt (fuel+2) dest s
      (directQueries (fetched s).1 charged ++ queries) result := by
  have actual : DriverQueryReceipt (fuel+1) dest next queries (X (fuel+1) dest next) := by
    rw [rest.sound]
    exact rest
  obtain ⟨cut,hq⟩ := actual
  have joined : DriverQueryReceipt (fuel+2) dest s
      (directQueries (fetched s).1 charged ++ queries) (X (fuel+1) dest next) :=
    ⟨.tail (fuel+1) dest s charged cost next hc he hh,
      .tail (fuel+1) dest s charged cost next hc he hh hq⟩
  rw [rest.sound] at joined
  exact joined
end Solidity.HashBridge
