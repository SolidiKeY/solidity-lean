import SolidityBridge.ExternalEvm.OutcomeDriver
import SolidityBridge.HashBridge.Prefix

/-! KECCAK-specific observations of the existing fetched X checks. No decoder,
scanner, padding or gas policy is replaced. Candidate charging is not a proof
that checks pass; the guard retains expansion-before-base-before-stack order. -/
namespace Solidity.HashBridge
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

def hashMemoryCharged (s : EVM.State) : EVM.State :=
  {s with gasAvailable := s.gasAvailable - .ofNat (memoryExpansionCost s .KECCAK256)}

def hashOpcodeCost (s : EVM.State) : Nat := C' (hashMemoryCharged s) .KECCAK256

def hashGuard (s : EVM.State) : Except ExecutionException Unit :=
  if s.gasAvailable.toNat < memoryExpansionCost s .KECCAK256 then .error .OutOfGass
  else if (hashMemoryCharged s).gasAvailable.toNat < hashOpcodeCost s then .error .OutOfGass
  else if s.stack.length < 2 then .error .StackUnderflow
  else if s.stack.length - 2 + 1 > 1024 then .error .StackOverflow
  else .ok ()

/-- Exact specialisation of the existing X checks, including original
memory-before-opcode-before-stack precedence. Jump tables are irrelevant here. -/
theorem hash_checks (dest : Array UInt256) (s : EVM.State)
    (hf : fetched s = (.KECCAK256,none)) :
    checks dest s = (do let _ ← hashGuard s; pure (hashMemoryCharged s,hashOpcodeCost s)) := by
  have hj : (Operation.KECCAK256 : Operation .EVM) ≠ .JUMP := by decide
  have hji : (Operation.KECCAK256 : Operation .EVM) ≠ .JUMPI := by decide
  have hr : (Operation.KECCAK256 : Operation .EVM) ≠ .RETURNDATACOPY := by decide
  have hstore : (Operation.KECCAK256 : Operation .EVM) ≠ .SSTORE := by decide
  simp only [checks, hf, δ, α, Option.getD_some, Operation.isCreate,
    reduceCtorEq, false_and, Bool.false_eq_true, if_false, Bind.bind,
    Except.bind, Pure.pure, Except.pure, hj, hji, hr, hstore]
  unfold hashGuard hashOpcodeCost hashMemoryCharged
  split_ifs <;> try rfl
  rename_i hmemory hbase hstack hcap hwrite
  have hbad : (false : Bool) = true := hwrite.2
  cases hbad

/-- The real byte input does not change when X debits memory expansion. -/
theorem hash_charged_input (s : EVM.State) (offset size : UInt256) :
    machineQuery (hashMemoryCharged s).toMachineState offset size =
      machineQuery s.toMachineState offset size := rfl

/-- Actual KECCAK opcode gas expression; no substituted size or affordability. -/
theorem hash_opcode_cost (s : EVM.State) :
    hashOpcodeCost s = 30 + 6 * ((s.stack[1]!.toNat + 31) / 32) := rfl

end Solidity.HashBridge
