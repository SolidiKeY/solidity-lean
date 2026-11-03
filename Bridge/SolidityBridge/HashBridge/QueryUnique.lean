import SolidityBridge.HashBridge.QueryShape

/-! Uniqueness of direct-frame query lists for the SAME original state and
fuel. No cross-fuel monotonicity, native determinism or global/nested-query
completeness is asserted. This is uniqueness inside the existing logical X. -/
namespace Solidity.HashBridge
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

/-- Different receipt proofs or result indices cannot select different query
lists: actual checks/step choose one next state, and the tail fuel decreases. -/
theorem query_receipt_unique (fuel : Nat) (dest : Array UInt256) (s : EVM.State)
    (queries₁ queries₂ : List (List Nat))
    (result₁ result₂ : Except ExecutionException (ExecutionResult EVM.State))
    (h₁ : DriverQueryReceipt fuel dest s queries₁ result₁)
    (h₂ : DriverQueryReceipt fuel dest s queries₂ result₂) : queries₁ = queries₂ := by
  induction fuel using Nat.strong_induction_on generalizing dest s queries₁ queries₂ result₁ result₂ with
  | h parent ih =>
    have hs₁ : DriverQueryShape parent dest s queries₁ := h₁.shape
    have hs₂ : DriverQueryShape parent dest s queries₂ := h₂.shape
    cases parent with
    | zero => exact hs₁.trans hs₂.symm
    | succ fuel =>
      cases hc : checks dest s with
      | error e =>
        simp only [DriverQueryShape,hc] at hs₁ hs₂
        exact hs₁.trans hs₂.symm
      | ok pair =>
        rcases pair with ⟨charged,cost⟩
        cases he : step fuel cost (some (fetched s)) charged with
        | error e =>
          simp only [DriverQueryShape,hc,he] at hs₁ hs₂
          exact hs₁.trans hs₂.symm
        | ok next =>
          cases ht : terminalData next (fetched s).1 with
          | some bytes =>
            simp only [DriverQueryShape,hc,he,ht] at hs₁ hs₂
            exact hs₁.trans hs₂.symm
          | none =>
            simp only [DriverQueryShape,hc,he,ht] at hs₁ hs₂
            obtain ⟨rest₁,hq₁,hr₁⟩ := hs₁
            obtain ⟨rest₂,hq₂,hr₂⟩ := hs₂
            have hr : rest₁ = rest₂ := ih fuel (Nat.lt_succ_self fuel) dest next rest₁ rest₂
              (X fuel dest next) (X fuel dest next) hr₁ hr₂
            rw [hq₁,hq₂,hr]

/-- Existence no longer permits favorable witness selection for this fixed
bounded frame. This does not define a source/default observation function. -/
theorem driver_queries_unique (fuel : Nat) (dest : Array UInt256) (s : EVM.State) :
    ∃! queries, DriverQueryReceipt fuel dest s queries (X fuel dest s) := by
  obtain ⟨queries,hq⟩ := driver_queries fuel dest s
  refine ⟨queries,hq,?_⟩
  intro other ho
  exact query_receipt_unique fuel dest s other queries (X fuel dest s) (X fuel dest s) ho hq

end Solidity.HashBridge
