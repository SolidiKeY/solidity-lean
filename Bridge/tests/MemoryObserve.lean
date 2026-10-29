import SolidityBridge.ExternalEvm.MemoryRefinement

/-! Native observations against the exact pinned upstream zero allocator.
Run through scripts/check-external-memory.sh. This is separate from the kernel
proofs and does not discharge PaddingCorrect. No source assembly is admitted. -/
open Solidity.Evm Solidity.Evm.External.Memory

private def require (b : Bool) (label : String) : IO Unit :=
  unless b do throw (IO.userError label)

private def one (dynamic : Bool) (i : Nat) (v : EvmYul.UInt256) : IO Unit := do
  let idx := EvmYul.UInt256.ofNat i
  let input := if dynamic then [idx, v] else [v]
  let cm : Machine := {Machine.init with stack := words input}
  let es : EvmYul.EVM.State := {controlState with stack := input}
  let ci := if dynamic then Instr.mstoreAt else Instr.mstore i
  let ops := if dynamic then storeAtMacro else storeMacro i
  match ci.step cm, run ops es with
  | .ok cm₁ 0, .ok es₁ =>
    require (cm₁.stack == words es₁.stack) "store stack mismatch"
    require (es₁.memory.size == 64 && es₁.activeWords.toNat == 2) "store extent mismatch"
    require (es₁.memory.readWithPadding (32 * i) 32 == encoding v) "physical encoding mismatch"
    let readCore := if dynamic then Instr.mloadAt else Instr.mload i
    let cmRead := if dynamic then {cm₁ with stack := .val (wmod idx.toNat) :: cm₁.stack} else cm₁
    let esRead := if dynamic then {es₁ with stack := idx :: es₁.stack} else es₁
    let readOps := if dynamic then loadAtMacro else loadMacro i
    match readCore.step cmRead, run readOps esRead with
    | .ok cm₂ 0, .ok es₂ =>
      require (cm₂.stack == [.val (wmod v.toNat)] && cm₂.stack == words es₂.stack) "readback mismatch"
      require (es₂.toMachineState.lookupMemory (address (1 - i)) == .ofNat 0) "other-cell frame mismatch"
      require (es₂.memory.size == 64 && es₂.activeWords.toNat == 2) "load extent mismatch"
      IO.println s!"mode={if dynamic then "dynamic" else "fixed"} cell={i} value={v.toNat} core={cm₂.stack} upstream={es₂.stack} size=64 active=2 frame=0"
    | _, _ => throw (IO.userError "unexpected load outcome")
  | _, _ => throw (IO.userError "unexpected store outcome")

def main : IO Unit := do
  for n in List.range 33 do
    let bytes := ffi.ByteArray.zeroes (USize.ofNat n)
    require (bytes.size == n && bytes.data.toList.all (· == 0)) "allocator sample mismatch"
  let values := [0, 1, 255, 256, 2^248, 2^255, EvmYul.UInt256.size - 1]
  for dynamic in [false, true] do
    for i in [0, 1] do
      for value in values do one dynamic i (.ofNat value)
  let unaligned := controlState.toMachineState.mstore (.ofNat 1) (.ofNat 1)
  require (unaligned.memory.data[32]! == 1 &&
    unaligned.lookupMemory (address 1) == .ofNat (2^248)) "unaligned counterexample mismatch"
  let past := (controlState.toMachineState.mload (address 2)).2
  require (past.activeWords.toNat == 3 && past.memory.size == 64) "capacity counterexample mismatch"
  require (address (EvmYul.UInt256.size / 32) == address 0) "address wrap mismatch"
  let wrap : EvmYul.MachineState := {unaligned with activeWords := .ofNat (EvmYul.UInt256.size / 32)}
  require (wrap.lookupMemory (address 1) == .ofNat 0) "active wrap mismatch"
  match run loadAtMacro {controlState with stack := []}, run storeAtMacro {controlState with stack := [.ofNat 0]} with
  | .error .StackUnderflow, .error .StackUnderflow => pure ()
  | _, _ => throw (IO.userError "underflow mismatch")
  IO.println "memory observations: 28 core/upstream store-load pairs, 33 allocator samples, 6 boundary/negative observations passed; PaddingCorrect remains an explicit unproved contract"
