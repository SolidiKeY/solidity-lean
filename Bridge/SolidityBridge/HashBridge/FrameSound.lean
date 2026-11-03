import SolidityBridge.HashBridge.Frame

/-! Existence and erasure soundness of direct-frame query receipts. Every
stage comes from the existing Classifies proof; no result/byte oracle, new
evaluator, fuel extension or native completeness assumption is introduced. -/
namespace Solidity.HashBridge
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

/-- Recursive direct-query instrumentation is supplied for every existing cut.
The continuation case consumes the original strictly smaller X fuel. -/
theorem classified_queries_exists (fuel : Nat) (dest : Array UInt256) (s : EVM.State)
    (result : Except ExecutionException (ExecutionResult EVM.State))
    (cut : Classifies fuel dest s result) : ∃ queries, ClassifiedQueries cut queries := by
  induction fuel using Nat.strong_induction_on generalizing dest s result with
  | h parent ih =>
    cases cut with
    | zero dest s => exact ⟨[],.zero dest s⟩
    | guard fuel dest s e hc => exact ⟨[],.guard fuel dest s e hc⟩
    | evaluator fuel dest s charged cost e hc he =>
      exact ⟨[],.evaluator fuel dest s charged cost e hc he⟩
    | tail fuel dest s charged cost next hc he hh =>
      obtain ⟨queries,hq⟩ := ih fuel (Nat.lt_succ_self fuel) dest next (X fuel dest next)
        (classifies fuel dest next)
      exact ⟨directQueries (fetched s).1 charged ++ queries,
        .tail fuel dest s charged cost next hc he hh hq⟩
    | revert fuel dest s charged cost next bytes hc he hh hr =>
      exact ⟨directQueries (fetched s).1 charged,
        .revert fuel dest s charged cost next bytes hc he hh hr⟩
    | success fuel dest s charged cost next bytes hc he hh hr =>
      exact ⟨directQueries (fetched s).1 charged,
        .success fuel dest s charged cost next bytes hc he hh hr⟩

/-- No receipt can select an operational result different from the original X. -/
theorem DriverQueryReceipt.sound {fuel : Nat} {dest : Array UInt256} {s : EVM.State}
    {queries : List (List Nat)} {result : Except ExecutionException (ExecutionResult EVM.State)}
    (receipt : DriverQueryReceipt fuel dest s queries result) : X fuel dest s = result := by
  obtain ⟨cut,_⟩ := receipt
  exact cut.sound

/-- Every actual raw frame result has a query receipt, including actual error
and raw REVERT arms. No reached state, successful check, result or bytes premise. -/
theorem driver_queries (fuel : Nat) (dest : Array UInt256) (s : EVM.State) :
    ∃ queries, DriverQueryReceipt fuel dest s queries (X fuel dest s) := by
  obtain ⟨queries,hq⟩ := classified_queries_exists fuel dest s (X fuel dest s)
    (classifies fuel dest s)
  exact ⟨queries,classifies fuel dest s,hq⟩

/-- At fuel1 checks may fail, or evaluator fuel0 fails: neither executes a
successful direct hash step. This is not a uniform OutOfFuel claim. -/
theorem driver_one_queries (dest : Array UInt256) (s : EVM.State) :
    DriverQueryReceipt 1 dest s [] (X 1 dest s) := by
  cases hc : checks dest s with
  | error e =>
    rw [check_failure 0 dest s e hc]
    exact ⟨.guard 0 dest s e hc,.guard 0 dest s e hc⟩
  | ok pair =>
    rcases pair with ⟨charged,cost⟩
    have he : step 0 cost (some (fetched s)) charged = .error .OutOfFuel := rfl
    rw [evaluator_failure 0 dest s charged cost .OutOfFuel hc he]
    exact ⟨.evaluator 0 dest s charged cost .OutOfFuel hc he,
      .evaluator 0 dest s charged cost .OutOfFuel hc he⟩

/-- With one driver fuel the result is an actual error, although the error
need not be OutOfFuel if an earlier check rejects. -/
theorem driver_one_error (dest : Array UInt256) (s : EVM.State) :
    ∃ e, X 1 dest s = .error e := by
  cases hc : checks dest s with
  | error e => exact ⟨e,check_failure 0 dest s e hc⟩
  | ok pair =>
    rcases pair with ⟨charged,cost⟩
    exact ⟨.OutOfFuel,evaluator_zero dest s charged cost hc⟩

end Solidity.HashBridge
