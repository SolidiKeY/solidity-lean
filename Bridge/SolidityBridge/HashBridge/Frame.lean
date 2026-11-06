import SolidityBridge.HashBridge.Charged

/-! Recursive direct-query observations indexed by EXISTING driver stage
proofs. No evaluator or new stage/fault policy is introduced. Successful
explicit edges record their actual charged input; child/native/adversary
queries are not observed here. Recursion is only over X's existing smaller
fuel. This is proof-only instrumentation, not a source execution judgment. -/
namespace Solidity.HashBridge
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

/-- Refinement of existing Classifies cuts, with actual direct byte queries.
No runtime erasure/match on this indexed Prop is introduced (G0). -/
inductive ClassifiedQueries : {fuel : Nat} → {dest : Array UInt256} → {s : EVM.State} →
    {result : Except ExecutionException (ExecutionResult EVM.State)} →
    Classifies fuel dest s result → List (List Nat) → Prop where
  | zero (dest : Array UInt256) (s : EVM.State) : ClassifiedQueries (.zero dest s) []
  | guard (fuel : Nat) (dest : Array UInt256) (s : EVM.State) (e : ExecutionException)
      (hc : checks dest s = .error e) : ClassifiedQueries (.guard fuel dest s e hc) []
  | evaluator (fuel : Nat) (dest : Array UInt256) (s charged : EVM.State)
      (cost : Nat) (e : ExecutionException) (hc : checks dest s = .ok (charged,cost))
      (he : step fuel cost (some (fetched s)) charged = .error e) :
      ClassifiedQueries (.evaluator fuel dest s charged cost e hc he) []
  | tail (fuel : Nat) (dest : Array UInt256) (s charged : EVM.State)
      (cost : Nat) (next : EVM.State) (hc : checks dest s = .ok (charged,cost))
      (he : step fuel cost (some (fetched s)) charged = .ok next)
      (hh : terminalData next (fetched s).1 = none) {queries : List (List Nat)}
      {restCut : Classifies fuel dest next (X fuel dest next)}
      (rest : ClassifiedQueries restCut queries) :
      ClassifiedQueries (.tail fuel dest s charged cost next hc he hh)
        (directQueries (fetched s).1 charged ++ queries)
  | revert (fuel : Nat) (dest : Array UInt256) (s charged : EVM.State)
      (cost : Nat) (next : EVM.State) (bytes : ByteArray)
      (hc : checks dest s = .ok (charged,cost))
      (he : step fuel cost (some (fetched s)) charged = .ok next)
      (hh : terminalData next (fetched s).1 = some bytes)
      (hr : ((fetched s).1 == .REVERT) = true) :
      ClassifiedQueries (.revert fuel dest s charged cost next bytes hc he hh hr)
        (directQueries (fetched s).1 charged)
  | success (fuel : Nat) (dest : Array UInt256) (s charged : EVM.State)
      (cost : Nat) (next : EVM.State) (bytes : ByteArray)
      (hc : checks dest s = .ok (charged,cost))
      (he : step fuel cost (some (fetched s)) charged = .ok next)
      (hh : terminalData next (fetched s).1 = some bytes)
      (hr : ((fetched s).1 == .REVERT) = false) :
      ClassifiedQueries (.success fuel dest s charged cost next bytes hc he hh hr)
        (directQueries (fetched s).1 charged)

/-- Hide only the proof of the existing stage cut, never a chosen execution.
The result remains an explicit index and is proved equal to actual X below. -/
def DriverQueryReceipt (fuel : Nat) (dest : Array UInt256) (s : EVM.State)
    (queries : List (List Nat)) (result : Except ExecutionException (ExecutionResult EVM.State)) : Prop :=
  ∃ cut : Classifies fuel dest s result, ClassifiedQueries cut queries

end Solidity.HashBridge
