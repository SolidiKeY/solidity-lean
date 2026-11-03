import SolidityBridge.HashBridge.FrameSound

/-! A one-cut Prop view of query receipts, not an execution function. The
matches reference the existing checks/step/terminalData exactly. This view
supports uniqueness without comparing or reducing whole classifier proofs. -/
namespace Solidity.HashBridge
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

def DriverQueryShape (fuel : Nat) (dest : Array UInt256) (s : EVM.State)
    (queries : List (List Nat)) : Prop :=
  match fuel with
  | 0 => queries = []
  | f+1 => match checks dest s with
    | .error _ => queries = []
    | .ok (charged,cost) => match step f cost (some (fetched s)) charged with
      | .error _ => queries = []
      | .ok next => match terminalData next (fetched s).1 with
        | some _ => queries = directQueries (fetched s).1 charged
        | none => ∃ rest, queries = directQueries (fetched s).1 charged ++ rest ∧
            DriverQueryReceipt f dest next rest (X f dest next)

/-- Every existing classified receipt obeys the same actual one-cut shape.
This is proof-only case elimination, never a hot match on an indexed value. -/
theorem ClassifiedQueries.shape {fuel : Nat} {dest : Array UInt256} {s : EVM.State}
    {result : Except ExecutionException (ExecutionResult EVM.State)}
    {cut : Classifies fuel dest s result} {queries : List (List Nat)}
    (h : ClassifiedQueries cut queries) : DriverQueryShape fuel dest s queries := by
  cases h with
  | zero dest s => rfl
  | guard fuel dest s e hc => simp only [DriverQueryShape,hc]
  | evaluator fuel dest s charged cost e hc he => simp only [DriverQueryShape,hc,he]
  | @tail fuel dest s charged cost next hc he hh queries restCut rest =>
    simp only [DriverQueryShape,hc,he,hh]
    exact ⟨queries,rfl,restCut,rest⟩
  | revert fuel dest s charged cost next bytes hc he hh hr =>
    simp only [DriverQueryShape,hc,he,hh]
  | success fuel dest s charged cost next bytes hc he hh hr =>
    simp only [DriverQueryShape,hc,he,hh]

theorem DriverQueryReceipt.shape {fuel : Nat} {dest : Array UInt256} {s : EVM.State}
    {queries : List (List Nat)} {result : Except ExecutionException (ExecutionResult EVM.State)}
    (h : DriverQueryReceipt fuel dest s queries result) : DriverQueryShape fuel dest s queries := by
  obtain ⟨cut,hq⟩ := h
  exact hq.shape

end Solidity.HashBridge
