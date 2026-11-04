import SolidityBridge.HashBridge.QueryPrepend
import SolidityBridge.HashBridge.StopQueries
import SolidityBridge.HashBridge.PairControls
import SolidityBridge.HashBridge.XiQueries
import SolidityBridge.ExternalEvm.RequireLocalState

/-! Exact public Xi inputs for the one-query program. This record aggregates
existing invocation arguments only; it contains no result or reached state.
World, snapshot, accrued effects and all environment fields remain arbitrary. -/
namespace Solidity.HashBridge.XiContext
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof Solidity.Evm.External

structure Inputs where
  created : Batteries.RBSet AccountAddress compare
  genesis : BlockHeader
  blocks : ProcessedBlocks
  world : AccountMap .EVM
  snapshot : AccountMap .EVM
  accrued : Substate
  environment : ExecutionEnv .EVM

def program : ByteArray := ⟨#[0x5f,0x5f,0x20]⟩
def initial (i : Inputs) : EVM.State :=
  {(default : EVM.State) with
    accountMap := i.world
    σ₀ := i.snapshot
    executionEnv := i.environment
    substate := i.accrued
    createdAccounts := i.created
    blocks := i.blocks
    genesisBlockHeader := i.genesis
    gasAvailable := .ofNat 34}
def pushed (i : Inputs) : EVM.State :=
  {initial i with
    gasAvailable := .ofNat 32
    pc := .ofNat 1
    execLength := 1
    stack := [.ofNat 0]}
def ready (i : Inputs) : EVM.State :=
  {pushed i with
    gasAvailable := .ofNat 30
    pc := .ofNat 2
    execLength := 2
    stack := [.ofNat 0,.ofNat 0]}

theorem fetches (i : Inputs) (code : i.environment.code = program) :
    fetched (initial i) = (.Push .PUSH0,none) ∧
      fetched (pushed i) = (.Push .PUSH0,none) ∧ fetched (ready i) = (.KECCAK256,none) := by
  constructor
  · change (decode i.environment.code (.ofNat 0)).getD (.STOP,none) = _
    rw [code]
    rfl
  · constructor
    · change (decode i.environment.code (.ofNat 1)).getD (.STOP,none) = _
      rw [code]
      rfl
    · change (decode i.environment.code (.ofNat 2)).getD (.STOP,none) = _
      rw [code]
      rfl

theorem push_checks (dest : Array UInt256) (i : Inputs) (code : i.environment.code = program) :
    checks dest (initial i) = .ok (initial i,2) ∧ checks dest (pushed i) = .ok (pushed i,2) := by
  constructor
  · have hm : memoryExpansionCost (initial i) (.Push .PUSH0) = 0 := by
      simp only [memoryExpansionCost,memoryExpansionCost.μᵢ',Nat.sub_self]
    simp only [checks,(fetches i code).1,hm,word_sub_zero]
    cases hp : i.environment.perm <;> simp only [initial,hp] <;> rfl
  · have hm : memoryExpansionCost (pushed i) (.Push .PUSH0) = 0 := by
      simp only [memoryExpansionCost,memoryExpansionCost.μᵢ',Nat.sub_self]
    simp only [checks,(fetches i code).2.1,hm,word_sub_zero]
    cases hp : i.environment.perm <;> simp only [pushed,initial,hp] <;> rfl

theorem push_steps (fuel : Nat) (i : Inputs) (code : i.environment.code = program) :
    step (fuel+1) 2 (some (fetched (initial i))) (initial i) = .ok (pushed i) ∧
      step (fuel+1) 2 (some (fetched (pushed i))) (pushed i) = .ok (ready i) := by
  have firstGas : UInt256.ofNat 34 - UInt256.ofNat 2 = UInt256.ofNat 32 := by decide
  have secondGas : UInt256.ofNat 32 - UInt256.ofNat 2 = UInt256.ofNat 30 := by decide
  constructor
  · rw [(fetches i code).1,local_push0]
    simp only [localAfter,initial,pushed,firstGas]
    rfl
  · rw [(fetches i code).2.1,local_push0]
    simp only [localAfter,initial,pushed,ready,secondGas]
    rfl

theorem hash_ready (i : Inputs) : hashGuard (ready i) = .ok () := by
  obtain ⟨hm,hc⟩ := PairControls.zero_size_costs (ready i) (.ofNat 0) rfl rfl
  simp only [hashGuard,hm,hc,hashMemoryCharged,word_sub_zero]
  rfl
end Solidity.HashBridge.XiContext
