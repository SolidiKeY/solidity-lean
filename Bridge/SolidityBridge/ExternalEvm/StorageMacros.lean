import SolidityBridge.ExternalEvm.StorageOpcode

/-! Bounded storage macros, composed from small proofs about the
actual upstream dispatcher. Scratch preparation remains an explicit interface. -/
namespace Solidity.Evm.StorageSlots

abbrev Opcode := EvmYul.Operation .EVM × Option (EvmYul.UInt256 × Nat)

/-- A bounded supplied-opcode macro; fetching, gas checks and assembly are
outside this interface, exactly as in the existing dispatcher bridge. -/
def runMacro : List Opcode → EvmYul.EVM.State →
    Except EvmYul.EVM.ExecutionException EvmYul.EVM.State
  | [], s => .ok s
  | op :: ops, s => do
    let s' ← EvmYul.EVM.step 1 0 (some op) s
    runMacro ops s'

/-- Actual preparation prefixes followed by the offset/length/hash steps. -/
def mapMacro : List Opcode :=
  [(.Push .PUSH32, some (.ofNat 0, 32)), (.MSTORE, none),
    (.Push .PUSH32, some (.ofNat 32, 32)), (.MSTORE, none),
    (.Push .PUSH32, some (.ofNat 64, 32)), (.Push .PUSH32, some (.ofNat 0, 32)),
    (.KECCAK256, none)]

def arrayMacro : List Opcode :=
  [(.Push .PUSH32, some (.ofNat 0, 32)), (.MSTORE, none),
    (.Push .PUSH32, some (.ofNat 32, 32)), (.Push .PUSH32, some (.ofNat 0, 32)),
    (.KECCAK256, none)]

/-- Optional partial lowering, with a named refusal for every instruction
outside this storage macro interface. Accepted stack shapes and scratch setup
remain premises of the refinement theorems. -/
def lowerInstr : Instr → Except String (List Opcode)
  | .push (.val v) => .ok [(.Push .PUSH32, some (encode v, 32))]
  | .push (.slot a) => .ok [(.Push .PUSH32, some (address a, 32))]
  | .sload => .ok [(.SLOAD, none)]
  | .sstore => .ok [(.SSTORE, none)]
  | .keccakMap => .ok mapMacro
  | .keccakArr => .ok arrayMacro
  | _ => .error "evm-storage-slots: unsupported instruction"

def lowerProgram : List Instr → Except String (List Opcode)
  | [] => .ok []
  | i :: is => do
    let first ← lowerInstr i
    let rest ← lowerProgram is
    pure (first ++ rest)

theorem lowering_refuses_call : lowerInstr .call =
    .error "evm-storage-slots: unsupported instruction" := rfl

theorem lowering_write_read :
    lowerProgram [.push (.val (wmod 7)), .push (.slot (.root 0)), .sstore,
      .push (.slot (.root 0)), .sload] =
    .ok [(.Push .PUSH32, some (.ofNat 7, 32)),
      (.Push .PUSH32, some (.ofNat 0, 32)), (.SSTORE, none),
      (.Push .PUSH32, some (.ofNat 0, 32)), (.SLOAD, none)] := rfl


theorem runMacro_cons_of_step {op : Opcode} {ops : List Opcode}
    {s out : EvmYul.EVM.State}
    (h : EvmYul.EVM.step 1 0 (some op) s = .ok out) :
    runMacro (op :: ops) s = runMacro ops out := by
  change (EvmYul.EVM.step 1 0 (some op) s).bind (fun s' => runMacro ops s') = _
  rw [h]
  rfl

theorem runMacro_append (first rest : List Opcode) (s : EvmYul.EVM.State) :
    runMacro (first ++ rest) s = (runMacro first s).bind (fun out => runMacro rest out) := by
  induction first generalizing s with
  | nil => rfl
  | cons op ops ih =>
    cases h : EvmYul.EVM.step 1 0 (some op) s with
    | error e =>
      simp only [List.cons_append, runMacro, h, Except.bind]
      rfl
    | ok next => simpa only [List.cons_append, runMacro, h, Except.bind] using ih next

/-- Setup is inhabited for arbitrary operands, using an initially empty
machine memory. No hash equation or canonical FFI-padding law is required. -/
theorem array_setup_inhabited (parent : EvmYul.UInt256) :
    ArraySetup (default : EvmYul.MachineState) parent :=
  array_setup_empty _ _ rfl

theorem map_setup_inhabited (key parent : EvmYul.UInt256) :
    MapSetup (default : EvmYul.MachineState) key parent :=
  map_setup_empty _ _ _ rfl

/-- Array macro including the actual MSTORE preparation prefix. The assumption
concerns only the written region read by the hash, not the rest of memory. -/
theorem array_macro (s : EvmYul.EVM.State) (a : Slot)
    (tail : List EvmYul.UInt256)
    (hm : ArraySetup s.toMachineState (address a)) :
    ∃ out, runMacro arrayMacro {s with stack := address a :: tail} = .ok out ∧
      out.stack = address (.data a 0) :: tail ∧ out.toState = s.toState ∧
      out.memory = (s.toMachineState.mstore (.ofNat 0) (address a)).memory := by
  obtain ⟨s1, h1, hs1, hf1, hm1⟩ := push_step {s with stack := address a :: tail} (.ofNat 0)
  have hstack1 : s1.stack = .ofNat 0 :: address a :: tail := by rw [hs1]
  obtain ⟨s2, h2, hs2, hf2, hm2⟩ := mstore_step s1 (.ofNat 0) (address a) tail hstack1
  have hw2 : s2.memory = (s.toMachineState.mstore (.ofNat 0) (address a)).memory := by
    rw [hm2]
    exact mstore_memory_congr s1.toMachineState s.toMachineState hm1 (.ofNat 0) (address a)
  obtain ⟨s3, h3, hs3, hf3, hm3⟩ := push_step s2 (.ofNat 32)
  obtain ⟨s4, h4, hs4, hf4, hm4⟩ := push_step s3 (.ofNat 0)
  have hstack4 : s4.stack = .ofNat 0 :: .ofNat 32 :: tail := by rw [hs4, hs3, hs2]
  obtain ⟨s5, h5, hs5, hf5, hm5⟩ := keccak_step s4 (.ofNat 0) (.ofNat 32) tail hstack4
  have hw4 : s4.memory = (s.toMachineState.mstore (.ofNat 0) (address a)).memory :=
    hm4.trans (hm3.trans hw2)
  have hbytes : s4.memory.readWithPadding 0 32 = (arrayScratch (address a)).memory.readWithPadding 0 32 :=
    (congrArg (fun mem : ByteArray => mem.readWithPadding 0 32) hw4).trans hm
  refine ⟨s5, ?_, ?_, hf5.trans (hf4.trans (hf3.trans (hf2.trans hf1))), hm5.trans hw4⟩
  · change runMacro [(.Push .PUSH32, some (.ofNat 0, 32)), (.MSTORE, none),
      (.Push .PUSH32, some (.ofNat 32, 32)), (.Push .PUSH32, some (.ofNat 0, 32)),
      (.KECCAK256, none)] _ = _
    rw [runMacro_cons_of_step h1, runMacro_cons_of_step h2, runMacro_cons_of_step h3,
      runMacro_cons_of_step h4, runMacro_cons_of_step h5]
    rfl
  · rw [hs5, array_hash_read_setup s4.toMachineState (address a) hbytes]
    rfl

/-- Mapping macro including both actual MSTORE preparation steps. The key is
written at zero and the represented parent at 32 before KECCAK256 reads 64. -/
theorem map_macro (s : EvmYul.EVM.State) (key : Fin W) (a : Slot)
    (tail : List EvmYul.UInt256)
    (hm : MapSetup s.toMachineState (encode key) (address a)) :
    ∃ out, runMacro mapMacro {s with stack := encode key :: address a :: tail} = .ok out ∧
      out.stack = address (.hash key a 0) :: tail ∧ out.toState = s.toState ∧
      out.memory = ((s.toMachineState.mstore (.ofNat 0) (encode key)).mstore (.ofNat 32) (address a)).memory := by
  obtain ⟨s1, h1, hs1, hf1, hm1⟩ := push_step
    {s with stack := encode key :: address a :: tail} (.ofNat 0)
  have hstack1 : s1.stack = .ofNat 0 :: encode key :: address a :: tail := by rw [hs1]
  obtain ⟨s2, h2, hs2, hf2, hm2⟩ := mstore_step s1 (.ofNat 0) (encode key) (address a :: tail) hstack1
  have hw2 : s2.memory = (s.toMachineState.mstore (.ofNat 0) (encode key)).memory := by
    rw [hm2]
    exact mstore_memory_congr s1.toMachineState s.toMachineState hm1 (.ofNat 0) (encode key)
  obtain ⟨s3, h3, hs3, hf3, hm3⟩ := push_step s2 (.ofNat 32)
  have hstack3 : s3.stack = .ofNat 32 :: address a :: tail := by rw [hs3, hs2]
  obtain ⟨s4, h4, hs4, hf4, hm4⟩ := mstore_step s3 (.ofNat 32) (address a) tail hstack3
  have hw4 : s4.memory =
      ((s.toMachineState.mstore (.ofNat 0) (encode key)).mstore (.ofNat 32) (address a)).memory := by
    rw [hm4]
    exact mstore_memory_congr s3.toMachineState (s.toMachineState.mstore (.ofNat 0) (encode key))
      (hm3.trans hw2) (.ofNat 32) (address a)
  obtain ⟨s5, h5, hs5, hf5, hm5⟩ := push_step s4 (.ofNat 64)
  obtain ⟨s6, h6, hs6, hf6, hm6⟩ := push_step s5 (.ofNat 0)
  have hstack6 : s6.stack = .ofNat 0 :: .ofNat 64 :: tail := by rw [hs6, hs5, hs4]
  obtain ⟨s7, h7, hs7, hf7, hm7⟩ := keccak_step s6 (.ofNat 0) (.ofNat 64) tail hstack6
  have hw6 : s6.memory =
      ((s.toMachineState.mstore (.ofNat 0) (encode key)).mstore (.ofNat 32) (address a)).memory :=
    hm6.trans (hm5.trans hw4)
  have hbytes : s6.memory.readWithPadding 0 64 =
      (mapScratch (encode key) (address a)).memory.readWithPadding 0 64 :=
    (congrArg (fun mem : ByteArray => mem.readWithPadding 0 64) hw6).trans hm
  refine ⟨s7, ?_, ?_, hf7.trans (hf6.trans (hf5.trans (hf4.trans (hf3.trans (hf2.trans hf1))))),
    hm7.trans hw6⟩
  · change runMacro [(.Push .PUSH32, some (.ofNat 0, 32)), (.MSTORE, none),
      (.Push .PUSH32, some (.ofNat 32, 32)), (.MSTORE, none),
      (.Push .PUSH32, some (.ofNat 64, 32)), (.Push .PUSH32, some (.ofNat 0, 32)),
      (.KECCAK256, none)] _ = _
    rw [runMacro_cons_of_step h1, runMacro_cons_of_step h2, runMacro_cons_of_step h3,
      runMacro_cons_of_step h4, runMacro_cons_of_step h5, runMacro_cons_of_step h6,
      runMacro_cons_of_step h7]
    rfl
  · rw [hs7, map_hash_read_setup s6.toMachineState (encode key) (address a) hbytes]
    rfl

end Solidity.Evm.StorageSlots
