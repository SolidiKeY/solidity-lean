import SolidityBridge.HashBridge.QueryUnique

/-! Direct query receipts for the existing PUBLIC Xi invocation. The initial
record and projection below are the pinned definition's actual constructor and
fields. No source judgment, new evaluator, chosen reply, native hash equality
or nested-call completeness is introduced. All receipts stay proof-only (G0). -/
namespace Solidity.HashBridge
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

def XiQueryReceipt (fuel : Nat) (created : Batteries.RBSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (world snapshot : AccountMap .EVM)
    (gas : UInt256) (accrued : Substate) (env : ExecutionEnv .EVM)
    (queries : List (List Nat))
    (result : Except ExecutionException
      (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate))) : Prop :=
  match fuel with
  | 0 => queries = [] ∧ result = .error .OutOfFuel
  | n+1 =>
    let initial : EVM.State := {(default : EVM.State) with
      accountMap := world
      σ₀ := snapshot
      executionEnv := env
      substate := accrued
      createdAccounts := created
      gasAvailable := gas
      blocks := blocks
      genesisBlockHeader := genesis}
    ∃ out, DriverQueryReceipt n (D_J env.code (.ofNat 0)) initial queries out ∧
      result = (do
        let value ← out
        match value with
        | .success s bytes => .ok (.success (s.createdAccounts,s.accountMap,s.gasAvailable,s.substate) bytes)
        | .revert g bytes => .ok (.revert g bytes))
theorem XiQueryReceipt.sound (fuel : Nat) (created : Batteries.RBSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (world snapshot : AccountMap .EVM)
    (gas : UInt256) (accrued : Substate) (env : ExecutionEnv .EVM)
    (queries : List (List Nat)) (result : Except ExecutionException
      (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate)))
    (h : XiQueryReceipt fuel created genesis blocks world snapshot gas accrued env queries result) :
    Ξ fuel created genesis blocks world snapshot gas accrued env = result := by
  cases fuel with
  | zero => exact h.2.symm
  | succ n =>
    obtain ⟨out,receipt,project⟩ := h
    rw [← receipt.sound] at project
    exact project.symm

/-- All public fuel/error/revert/success cases derive their query receipt from
this SAME initialized invocation. No desired X result is a premise. -/
theorem xi_queries (fuel : Nat) (created : Batteries.RBSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (world snapshot : AccountMap .EVM)
    (gas : UInt256) (accrued : Substate) (env : ExecutionEnv .EVM) :
    ∃ queries, XiQueryReceipt fuel created genesis blocks world snapshot gas accrued env queries
      (Ξ fuel created genesis blocks world snapshot gas accrued env) := by
  cases fuel with
  | zero => exact ⟨[],rfl,rfl⟩
  | succ n =>
    let initial : EVM.State := {(default : EVM.State) with
      accountMap := world
      σ₀ := snapshot
      executionEnv := env
      substate := accrued
      createdAccounts := created
      gasAvailable := gas
      blocks := blocks
      genesisBlockHeader := genesis}
    obtain ⟨queries,receipt⟩ := driver_queries n (D_J env.code (.ofNat 0)) initial
    exact ⟨queries,X n (D_J env.code (.ofNat 0)) initial,receipt,rfl⟩

/-- Fixed public invocation: neither the hidden X result nor the receipt proof
can choose a different direct query list. This does not compare different fuel. -/
theorem xi_query_receipt_unique (fuel : Nat) (created : Batteries.RBSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (world snapshot : AccountMap .EVM)
    (gas : UInt256) (accrued : Substate) (env : ExecutionEnv .EVM)
    (queries queries' : List (List Nat))
    (result result' : Except ExecutionException
      (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate)))
    (h : XiQueryReceipt fuel created genesis blocks world snapshot gas accrued env queries result)
    (h' : XiQueryReceipt fuel created genesis blocks world snapshot gas accrued env queries' result') :
    queries = queries' := by
  cases fuel with
  | zero => exact h.1.trans h'.1.symm
  | succ n =>
    obtain ⟨out,receipt,_⟩ := h
    obtain ⟨out',receipt',_⟩ := h'
    exact query_receipt_unique n (D_J env.code (.ofNat 0)) _ queries queries' out out' receipt receipt'

end Solidity.HashBridge
