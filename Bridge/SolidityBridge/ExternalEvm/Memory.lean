import Solidity.Evm.Machine
import EvmYul.EVM.Semantics

/-!
Actual upstream memory dispatch and fixed/stack-addressed macro lowering. This module
is a checkpoint, not a persistent word-cell/byte-memory simulation: the latter
still needs serialization, readback and frame laws under an explicit contract
for the upstream opaque zero-padding primitive. No source assembly is admitted.
-/
namespace Solidity.Evm.External.Memory

/-- A core cell occupies 32 consecutive bytes. -/
def address (cell : Nat) : EvmYul.UInt256 := .ofNat (32 * cell)

/-- Capacity bound only. A persistent relation must separately bound the
state's activeWords: lookupMemory multiplies it by 32 in UInt256. -/
def Bounded (cells : Nat) : Prop :=
  32 * cells < EvmYul.UInt256.size ∧ 32 * cells < 2 ^ 64

theorem address_toNat (cell : Nat) (h : 32 * cell < EvmYul.UInt256.size) :
    (address cell).toNat = 32 * cell := Nat.mod_eq_of_lt h

theorem aligned_disjoint (i j : Nat) (h : i ≠ j) :
    32 * i + 32 ≤ 32 * j ∨ 32 * j + 32 ≤ 32 * i := by omega

/-- The external primitive's missing specification, kept as a predicate rather
than installed as an axiom. There is no claimed inhabitant of this predicate. -/
def PaddingCorrect (bound : Nat) : Prop :=
  bound < 2 ^ 64 ∧
  ∀ n : Nat, n ≤ bound → ffi.ByteArray.zeroes (USize.ofNat n) =
    ⟨Array.replicate n (0 : UInt8)⟩

def prepare (s : EvmYul.EVM.State) : EvmYul.EVM.State :=
  {s with execLength := s.execLength + 1, gasAvailable := s.gasAvailable - .ofNat 0}

def loaded (s : EvmYul.EVM.State) (a : EvmYul.UInt256)
    (st : List EvmYul.UInt256) : EvmYul.EVM.State :=
  let p := prepare s
  let (v, mem) := p.toMachineState.mload a
  {p with toMachineState := mem}.replaceStackAndIncrPC (v :: st)

def stored (s : EvmYul.EVM.State) (a v : EvmYul.UInt256)
    (st : List EvmYul.UInt256) : EvmYul.EVM.State :=
  let p := prepare s
  {p with toMachineState := p.toMachineState.mstore a v}.replaceStackAndIncrPC st

/-- Actual evaluator, including PC, active memory, execution length and gas
preparation. Positive fuel and zero charged gas match the existing opcode bridge. -/
theorem load_dispatch (s : EvmYul.EVM.State) (a : EvmYul.UInt256)
    (st : List EvmYul.UInt256) (fuel : Nat) :
    EvmYul.EVM.step (fuel + 1) 0 (some (.MLOAD, none)) {s with stack := a :: st} =
      .ok (loaded {s with stack := a :: st} a st) := by rfl

theorem store_dispatch (s : EvmYul.EVM.State) (a v : EvmYul.UInt256)
    (st : List EvmYul.UInt256) (fuel : Nat) :
    EvmYul.EVM.step (fuel + 1) 0 (some (.MSTORE, none)) {s with stack := a :: v :: st} =
      .ok (stored {s with stack := a :: v :: st} a v st) := by rfl

abbrev Opcode := EvmYul.Operation .EVM × Option (EvmYul.UInt256 × Nat)

/-- Evaluates supplied opcodes, not fetched bytecode or the gas-checking driver. -/
def run : List Opcode → EvmYul.EVM.State → Except EvmYul.EVM.ExecutionException EvmYul.EVM.State
  | [], s => .ok s
  | op :: ops, s => (EvmYul.EVM.step 1 0 (some op) s).bind (run ops)

def pushAddress (cell : Nat) : Opcode := (.Push .PUSH32, some (address cell, 32))
def loadMacro (cell : Nat) : List Opcode := [pushAddress cell, (.MLOAD, none)]
def storeMacro (cell : Nat) : List Opcode := [pushAddress cell, (.MSTORE, none)]

def pushed (s : EvmYul.EVM.State) (cell : Nat) : EvmYul.EVM.State :=
  (prepare s).replaceStackAndIncrPC (address cell :: s.stack) (pcΔ := 33)

/-- The fixed-cell core load requires a PUSH32 before MLOAD. -/
theorem load_macro (s : EvmYul.EVM.State) (cell : Nat) :
    run (loadMacro cell) s = .ok (loaded (pushed s cell) (address cell) s.stack) := by rfl

/-- The fixed-cell core store requires a PUSH32 before MSTORE. -/
theorem store_macro (s : EvmYul.EVM.State) (cell : Nat) (v : EvmYul.UInt256)
    (st : List EvmYul.UInt256) :
    run (storeMacro cell) {s with stack := v :: st} =
      .ok (stored (pushed {s with stack := v :: st} cell) (address cell) v st) := by rfl

/-- Exact upstream byte update. This deliberately does not assert the missing
readback/frame theorem for ByteArray.write or for ffi.ByteArray.zeroes. -/
theorem stored_bytes (s : EvmYul.EVM.State) (a v : EvmYul.UInt256)
    (st : List EvmYul.UInt256) :
    (stored s a v st).memory =
      ByteArray.write v.toByteArray 0 s.memory a.toNat 32 := by rfl

/-- Zero memory loads do not depend on the opaque padding primitive. -/
theorem empty_lookup (s : EvmYul.MachineState) (h : s.memory = .empty)
    (a : EvmYul.UInt256) : s.lookupMemory a = .ofNat 0 := by
  have guard : a.toNat ≥ s.memory.size := by rw [h]; exact Nat.zero_le _
  simp only [EvmYul.MachineState.lookupMemory, guard, true_or, ↓reduceIte]
  rfl

theorem load_underflow (s : EvmYul.EVM.State) :
    EvmYul.EVM.step 1 0 (some (.MLOAD, none)) {s with stack := []} =
      .error .StackUnderflow := by rfl

theorem store_underflow (s : EvmYul.EVM.State) (v : EvmYul.UInt256) :
    EvmYul.EVM.step 1 0 (some (.MSTORE, none)) {s with stack := [v]} =
      .error .StackUnderflow := by rfl

/-- The first modulus-scaling alias is cell zero; the physical capacity
bound excludes earlier addresses as well. -/
theorem address_wrap : address (EvmYul.UInt256.size / 32) = address 0 := by decide

/-- Nonaligned windows can overlap even when their starting addresses differ. -/
theorem unaligned_overlap : 1 < 0 + 32 ∧ 0 < 1 + 32 := by decide

/-- A single-access representation premise on the actual upstream read.
This is not a byte encoding or a persistent memory invariant. -/
def ReadAgrees (m : Machine) (s : EvmYul.EVM.State) (cell : Nat) : Prop :=
  m.mem cell = .val (wmod (s.toMachineState.lookupMemory (address cell)).toNat)

def words (st : List EvmYul.UInt256) : List Word :=
  st.map (fun a => .val (wmod a.toNat))

/-- Connect the actual core fixed-cell step to the actual macro's stack
observation. The initial read relation is explicit and is not derived here. -/
theorem load_core_macro (m : Machine) (s : EvmYul.EVM.State) (cell : Nat)
    (hs : m.stack = words s.stack) (hr : ReadAgrees m s cell) :
    ∃ m' s', (Instr.mload cell).step m = .ok m' 0 ∧
      run (loadMacro cell) s = .ok s' ∧ m'.stack = words s'.stack := by
  refine ⟨{m with stack := m.mem cell :: m.stack},
    loaded (pushed s cell) (address cell) s.stack, rfl, load_macro s cell, ?_⟩
  change m.mem cell :: m.stack =
    .val (wmod (s.toMachineState.lookupMemory (address cell)).toNat) :: words s.stack
  rw [hr, hs]

/-- Both actual stores, with their exact word/byte updates and unchanged
numeric stack tail. No post-store read agreement is assumed or concluded. -/
theorem store_core_macro (m : Machine) (s : EvmYul.EVM.State) (cell : Nat)
    (v : EvmYul.UInt256) (st : List EvmYul.UInt256)
    (hs : m.stack = .val (wmod v.toNat) :: words st) :
    ∃ m' s', (Instr.mstore cell).step m = .ok m' 0 ∧
      run (storeMacro cell) {s with stack := v :: st} = .ok s' ∧
      m'.stack = words s'.stack ∧
      m'.mem cell = .val (wmod v.toNat) ∧
      (∀ k, k ≠ cell → m'.mem k = m.mem k) ∧
      s'.memory = ByteArray.write v.toByteArray 0 s.memory (address cell).toNat 32 := by
  let m' : Machine :=
    {m with stack := words st, mem := upd m.mem cell (.val (wmod v.toNat))}
  let s' : EvmYul.EVM.State :=
    stored (pushed {s with stack := v :: st} cell) (address cell) v st
  refine ⟨m', s', ?_, store_macro s cell v st, ?_, ?_, ?_, ?_⟩
  · change (match m.stack with
      | w :: tail => Out.ok {m with stack := tail, mem := upd m.mem cell w} 0
      | [] => Out.fault) = .ok m' 0
    rw [hs]
  · change words st = words st
    rfl
  · change upd m.mem cell (.val (wmod v.toNat)) cell = .val (wmod v.toNat)
    exact upd_same m.mem cell (.val (wmod v.toNat))
  · intro k hk
    change upd m.mem cell (.val (wmod v.toNat)) k = m.mem k
    exact upd_other m.mem (.val (wmod v.toNat)) hk
  · exact stored_bytes (pushed {s with stack := v :: st} cell) (address cell) v st

/-- Stack-addressed accesses need multiplication by 32 before the memory
opcode; the input address is a word-cell index. -/
def loadAtMacro : List Opcode :=
  [(.Push .PUSH32, some (.ofNat 32, 32)), (.MUL, none), (.MLOAD, none)]

def storeAtMacro : List Opcode :=
  [(.Push .PUSH32, some (.ofNat 32, 32)), (.MUL, none), (.MSTORE, none)]

def scaled (s : EvmYul.EVM.State) (a : EvmYul.UInt256)
    (st : List EvmYul.UInt256) : EvmYul.EVM.State :=
  let p := (prepare s).replaceStackAndIncrPC (.ofNat 32 :: a :: st) (pcΔ := 33)
  (prepare p).replaceStackAndIncrPC (address a.toNat :: st)

theorem loadAt_macro (s : EvmYul.EVM.State) (a : EvmYul.UInt256)
    (st : List EvmYul.UInt256) :
    run loadAtMacro {s with stack := a :: st} =
      .ok (loaded (scaled {s with stack := a :: st} a st) (address a.toNat) st) := by rfl

theorem storeAt_macro (s : EvmYul.EVM.State) (a v : EvmYul.UInt256)
    (st : List EvmYul.UInt256) :
    run storeAtMacro {s with stack := a :: v :: st} =
      .ok (stored (scaled {s with stack := a :: v :: st} a (v :: st))
        (address a.toNat) v st) := by rfl

theorem word_index (a : EvmYul.UInt256) : (wmod a.toNat).val = a.toNat := by
  apply Nat.mod_eq_of_lt
  change a.toNat < EvmYul.UInt256.size
  exact a.val.isLt

/-- The dynamic core read and actual scaled macro, under the same explicit
single-read premise as the fixed-cell theorem. -/
theorem loadAt_core_macro (m : Machine) (s : EvmYul.EVM.State)
    (a : EvmYul.UInt256) (st : List EvmYul.UInt256)
    (hs : m.stack = .val (wmod a.toNat) :: words st)
    (hr : ReadAgrees m s a.toNat) :
    ∃ m' s', Instr.mloadAt.step m = .ok m' 0 ∧
      run loadAtMacro {s with stack := a :: st} = .ok s' ∧
      m'.stack = words s'.stack := by
  let m' : Machine := {m with stack := m.mem a.toNat :: words st}
  let s' : EvmYul.EVM.State :=
    loaded (scaled {s with stack := a :: st} a st) (address a.toNat) st
  refine ⟨m', s', ?_, loadAt_macro s a st, ?_⟩
  · change (match m.stack with
      | .val x :: tail => m.next (m.mem x.val :: tail)
      | _ => Out.fault) = .ok m' 0
    rw [hs]
    change m.next (m.mem (wmod a.toNat).val :: words st) = .ok m' 0
    rw [word_index]
    rfl
  · change m.mem a.toNat :: words st =
      .val (wmod (s.toMachineState.lookupMemory (address a.toNat)).toNat) :: words st
    rw [hr]

/-- Dynamic paired stores and their exact word/byte updates. As with the
fixed-cell theorem, no byte-memory postrelation is assumed or concluded. -/
theorem storeAt_core_macro (m : Machine) (s : EvmYul.EVM.State)
    (a v : EvmYul.UInt256) (st : List EvmYul.UInt256)
    (hs : m.stack = .val (wmod a.toNat) :: .val (wmod v.toNat) :: words st) :
    ∃ m' s', Instr.mstoreAt.step m = .ok m' 0 ∧
      run storeAtMacro {s with stack := a :: v :: st} = .ok s' ∧
      m'.stack = words s'.stack ∧
      m'.mem a.toNat = .val (wmod v.toNat) ∧
      (∀ k, k ≠ a.toNat → m'.mem k = m.mem k) ∧
      s'.memory = ByteArray.write v.toByteArray 0 s.memory (address a.toNat).toNat 32 := by
  let m' : Machine :=
    {m with stack := words st, mem := upd m.mem a.toNat (.val (wmod v.toNat))}
  let s' : EvmYul.EVM.State :=
    stored (scaled {s with stack := a :: v :: st} a (v :: st)) (address a.toNat) v st
  refine ⟨m', s', ?_, storeAt_macro s a v st, ?_, ?_, ?_, ?_⟩
  · change (match m.stack with
      | .val x :: w :: tail => Out.ok {m with stack := tail, mem := upd m.mem x.val w} 0
      | _ => Out.fault) = .ok m' 0
    rw [hs]
    change Out.ok {m with
      stack := words st
      mem := upd m.mem (wmod a.toNat).val (.val (wmod v.toNat))} 0 = .ok m' 0
    rw [word_index]
  · change words st = words st
    rfl
  · change upd m.mem a.toNat (.val (wmod v.toNat)) a.toNat = .val (wmod v.toNat)
    exact upd_same m.mem a.toNat (.val (wmod v.toNat))
  · intro k hk
    change upd m.mem a.toNat (.val (wmod v.toNat)) k = m.mem k
    exact upd_other m.mem (.val (wmod v.toNat)) hk
  · exact stored_bytes (scaled {s with stack := a :: v :: st} a (v :: st))
      (address a.toNat) v st

theorem loadAt_underflow (s : EvmYul.EVM.State) :
    Instr.mloadAt.step Machine.init = .fault ∧
      run loadAtMacro {s with stack := []} = .error .StackUnderflow := by
  exact ⟨rfl, rfl⟩

theorem storeAt_underflow (s : EvmYul.EVM.State) (a : EvmYul.UInt256) :
    Instr.mstoreAt.step {Machine.init with stack := [.val (wmod a.toNat)]} = .fault ∧
      run storeAtMacro {s with stack := [a]} = .error .StackUnderflow := by
  exact ⟨rfl, rfl⟩

/-- A positive, inhabited access case avoids the FFI entirely. An arbitrary
upstream environment is retained; the input stack and physical memory are empty. -/
theorem empty_load_control (s : EvmYul.EVM.State) :
    ∃ m' s', (Instr.mload 0).step Machine.init = .ok m' 0 ∧
      run (loadMacro 0) {s with memory := .empty, stack := []} = .ok s' ∧
      m'.stack = words s'.stack := by
  apply load_core_macro Machine.init {s with memory := .empty, stack := []} 0 rfl
  unfold ReadAgrees
  rw [empty_lookup _ rfl]
  rfl

/-- An inhabited stack-addressed load at the lower alignment boundary. -/
theorem empty_loadAt_control (s : EvmYul.EVM.State) :
    ∃ m' s', Instr.mloadAt.step
        {Machine.init with stack := [.val (wmod (EvmYul.UInt256.ofNat 0).toNat)]} = .ok m' 0 ∧
      run loadAtMacro {s with memory := .empty, stack := [.ofNat 0]} = .ok s' ∧
      m'.stack = words s'.stack := by
  apply loadAt_core_macro
    {Machine.init with stack := [.val (wmod (EvmYul.UInt256.ofNat 0).toNat)]}
    {s with memory := .empty} (.ofNat 0) [] rfl
  unfold ReadAgrees
  rw [empty_lookup _ rfl]
  rfl

/-- A separate upper-bound obstruction: the active byte extent can wrap
although the accessed address itself is a valid UInt256. -/
theorem active_extent_wrap (s : EvmYul.MachineState) (a : EvmYul.UInt256)
    (h : s.activeWords = .ofNat (EvmYul.UInt256.size / 32)) :
    s.lookupMemory a = .ofNat 0 := by
  have hz : EvmYul.UInt256.ofNat (EvmYul.UInt256.size / 32) *
      (⟨32⟩ : EvmYul.UInt256) = (⟨0⟩ : EvmYul.UInt256) := by decide
  have ha : a ≥ (⟨0⟩ : EvmYul.UInt256) := Nat.zero_le a.toNat
  simp only [EvmYul.MachineState.lookupMemory, h, hz, ha, or_true, ↓reduceIte]
  rfl

/-- A concrete 32-byte big-endian encoding of one is nevertheless read as
zero at the excluded active-extent boundary. No FFI operation is evaluated. -/
theorem active_wrap_counterexample :
    let s : EvmYul.MachineState :=
      {(default : EvmYul.MachineState) with
        memory := ⟨Array.replicate 31 (0 : UInt8) ++ #[1]⟩
        activeWords := .ofNat (EvmYul.UInt256.size / 32)}
    s.memory.size = 32 ∧ EvmYul.fromByteArrayBigEndian s.memory = 1 ∧
      s.lookupMemory (address 0) = .ofNat 0 := by
  refine ⟨by decide, ?_, active_extent_wrap _ _ rfl⟩
  change EvmYul.fromByteArrayBigEndian ⟨Array.replicate 31 (0 : UInt8) ++ #[1]⟩ = 1
  unfold EvmYul.fromByteArrayBigEndian ByteArray.toList
  iterate 32
    unfold ByteArray.toList.loop
    rw [if_pos (by decide)]
  unfold ByteArray.toList.loop
  rw [if_neg (by decide)]
  decide +kernel

end Solidity.Evm.External.Memory

/-- info: 'Solidity.Evm.External.Memory.load_core_macro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.load_core_macro
/-- info: 'Solidity.Evm.External.Memory.loadAt_macro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.loadAt_macro
/-- info: 'Solidity.Evm.External.Memory.storeAt_macro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.storeAt_macro
/-- info: 'Solidity.Evm.External.Memory.stored_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.stored_bytes
/-- info: 'Solidity.Evm.External.Memory.store_core_macro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.store_core_macro
/-- info: 'Solidity.Evm.External.Memory.empty_load_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.empty_load_control
/-- info: 'Solidity.Evm.External.Memory.active_extent_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.active_extent_wrap

/-- info: 'Solidity.Evm.External.Memory.active_wrap_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.active_wrap_counterexample

/-- info: 'Solidity.Evm.External.Memory.loadAt_core_macro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.loadAt_core_macro
/-- info: 'Solidity.Evm.External.Memory.storeAt_core_macro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.storeAt_core_macro

/-- info: 'Solidity.Evm.External.Memory.empty_loadAt_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.empty_loadAt_control
