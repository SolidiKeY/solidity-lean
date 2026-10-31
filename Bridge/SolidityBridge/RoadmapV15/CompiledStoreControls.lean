import SolidityBridge.RoadmapV15.CompiledStoreCheckpoint

/-! Both published full runtime inputs retain the actual checkpoint result.
Only the stated checkpoint resources are adequate; entry reachability, physical
padding/returned bytes, full execution and compiler/source agreement are open. -/
namespace SolidityBridge.RoadmapV15.CompiledStoreControls
open Solidity.Evm.TryByteImage EvmYul Solidity.Evm.External
private def seed : EVM.State :=
  { (default : EVM.State) with
    pc := .ofNat 71, stack := [.ofNat 258, .ofNat 513]
    executionEnv := { (default : ExecutionEnv .EVM) with
      codeOwner := .ofNat 7
      source := .ofNat 11, weiValue := .ofNat 13 }
    execLength := 19 }

example (p : Pipeline) : (compiledStoreInput p seed).accountMap = seed.accountMap := rfl
example (p : Pipeline) : (compiledStoreInput p seed).executionEnv.codeOwner = .ofNat 7 := rfl
example (p : Pipeline) : (compiledStoreInput p seed).executionEnv.source = .ofNat 11 := rfl
example (p : Pipeline) : (compiledStoreInput p seed).stack = [.ofNat 64, .ofNat 128] := rfl
example (p : Pipeline) :
    ((compiledStoreNext p seed).pc.toNat, (compiledStoreNext p seed).gasAvailable.toNat,
      (compiledStoreNext p seed).activeWords.toNat, (compiledStoreNext p seed).execLength,
      (compiledStoreNext p seed).stack.map UInt256.toNat) = (5, 0, 3, 20, []) := by
  change ((UInt256.ofNat 4 + UInt256.ofNat 1).toNat, 0, 3, 20, ([] : List Nat)) = _
  decide +kernel
example (p : Pipeline) :
    (Assembly.driverGate #[] (compiledStoreInput p seed) .MSTORE).isOk = true := by
  rw [compiled_store_gate]; rfl
example (p : Pipeline) :
    (Assembly.driverGate #[] {compiledStoreInput p seed with gasAvailable := .ofNat 11} .MSTORE).isOk = false := by
  have expansion : EVM.memoryExpansionCost
      {compiledStoreInput p seed with gasAvailable := .ofNat 11} .MSTORE = 9 :=
    TryMemory.prologue_expansion (compiledStoreInput p seed)
  simp only [Assembly.driverGate]
  rw [expansion]
  dsimp only [compiledStoreInput]
  have charge : UInt256.ofNat 11 - UInt256.ofNat 9 = UInt256.ofNat 2 := by decide +kernel
  rw [charge]
  rfl
example (p : Pipeline) :
    (Assembly.driverGate #[] {compiledStoreInput p seed with gasAvailable := .ofNat 8} .MSTORE).isOk = false := by
  have expansion : EVM.memoryExpansionCost
      {compiledStoreInput p seed with gasAvailable := .ofNat 8} .MSTORE = 9 :=
    TryMemory.prologue_expansion (compiledStoreInput p seed)
  simp only [Assembly.driverGate]
  rw [expansion]
  rfl
example (p : Pipeline) : EVM.step 1 0 (some (.MSTORE, none))
    {compiledStoreInput p seed with stack := []} = .error .StackUnderflow := rfl
/-- MSTORE is legal in static context too: this fixture adds no profile exclusion. -/
example (p : Pipeline) :
    (Assembly.driverGate #[] {compiledStoreInput p seed with
      executionEnv := {(compiledStoreInput p seed).executionEnv with perm := false}} .MSTORE).isOk = true := by
  have expansion : EVM.memoryExpansionCost
      {compiledStoreInput p seed with executionEnv :=
        {(compiledStoreInput p seed).executionEnv with perm := false}} .MSTORE = 9 :=
    TryMemory.prologue_expansion (compiledStoreInput p seed)
  simp only [Assembly.driverGate]
  rw [expansion]
  dsimp only [compiledStoreInput]
  have charge : UInt256.ofNat 12 - UInt256.ofNat 9 = UInt256.ofNat 3 := by decide +kernel
  rw [charge]
  rfl
example (p : Pipeline) : EVM.X 0 #[] (compiledStoreInput p seed) = .error .OutOfFuel := rfl
example : EVM.parseInstr 0x53 ≠ some .MSTORE := TryMemory.wrong_opcode
example : compiledStoreInput .legacy seed ≠ compiledStoreInput .viaIR seed := by
  intro h
  have he := congrArg (fun s => s.executionEnv.code.size) h
  have hn : (compiledStoreInput .legacy seed).executionEnv.code.size ≠
      (compiledStoreInput .viaIR seed).executionEnv.code.size := by
    change TryMemoryCode.legacyRuntime.size ≠ TryMemoryCode.viaIRRuntime.size
    rw [TryMemoryCode.legacy_size, TryMemoryCode.viaIR_size]
    decide
  exact hn he
example (p : Pipeline) (fuel : Nat) :
    EVM.X (fuel + 2) #[] (compiledStoreInput p seed) =
      EVM.X (fuel + 1) #[] (compiledStoreNext p seed) := compiled_store_driver p seed fuel
#print axioms compiled_store_decode
#print axioms compiled_store_gate
#print axioms compiled_store_supplied
#print axioms compiled_store_fetched
#print axioms compiled_store_driver
end SolidityBridge.RoadmapV15.CompiledStoreControls
