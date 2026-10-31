import SolidityBridge.ExternalEvm.MemoryRefinement

/-! Populated, FFI-independent initial representations and composed memory
controls. Supplied-opcode evaluation and the external padding contract retain
the same scope as MemoryRefinement. -/
namespace Solidity.Evm.External.Memory

private theorem append_left_byte (a b : ByteArray) (j : Nat) (hj : j < a.size) :
    (a ++ b).data[j]! = a.data[j]! := by
  rw [ByteArray.data_append]
  rw [getElem!_pos _ _ (by rw [Array.size_append]; change j < a.size + b.size; omega),
    Array.getElem_append_left hj, getElem!_pos a.data j hj]

private theorem append_right_byte (a b : ByteArray) (j : Nat) (hj : j < b.size) :
    (a ++ b).data[a.size + j]! = b.data[j]! := by
  rw [ByteArray.data_append]
  rw [getElem!_pos _ _ (by rw [Array.size_append]; change a.size + j < a.size + b.size; omega),
    Array.getElem_append_right (by change a.size ≤ a.size + j; omega)]
  simp only [show a.data.size = a.size from rfl, Nat.add_sub_cancel_left]
  exact (getElem!_pos b.data j hj).symm

/-- Two arbitrary numeric cells, with the core's zero default outside capacity. -/
def populatedCore (lo hi : EvmYul.UInt256) : Machine :=
  {Machine.init with mem := fun i =>
    if i = 0 then .val (wmod lo.toNat)
    else if i = 1 then .val (wmod hi.toNat)
    else Machine.init.mem i}

/-- Physical initialization is pure encoding, independent of ffi.zeroes. -/
def populatedState (lo hi : EvmYul.UInt256) : EvmYul.EVM.State :=
  {(default : EvmYul.EVM.State) with
    memory := encoding lo ++ encoding hi, activeWords := .ofNat 2, stack := []}

/-- Inhabited initial relation for every pair of words, including distinct
nonzero words. No allocator contract is assumed. -/
theorem populated_represents (lo hi : EvmYul.UInt256) :
    Represents 2 (populatedCore lo hi) (populatedState lo hi).toMachineState := by
  have hlo := (encoding_spec lo).1
  have hhi := (encoding_spec hi).1
  refine ⟨by constructor <;> decide, rfl, ?_, ?_⟩
  · change (encoding lo ++ encoding hi).size = 64
    rw [ByteArray.size_append, hlo, hhi]
  · intro i hbound
    have hc : i = 0 ∨ i = 1 := by omega
    rcases hc with h | h
    · subst i
      refine ⟨lo, rfl, ?_⟩
      intro j hj
      rw [show (populatedState lo hi).memory = encoding lo ++ encoding hi from rfl]
      simp only [Nat.mul_zero, Nat.zero_add]
      exact append_left_byte (encoding lo) (encoding hi) j (by rw [hlo]; exact hj)
    · subst i
      refine ⟨hi, rfl, ?_⟩
      intro j hj
      rw [show (populatedState lo hi).memory = encoding lo ++ encoding hi from rfl]
      simp only [Nat.mul_one]
      have h := append_right_byte (encoding lo) (encoding hi) j (by rw [hhi]; exact hj)
      rw [hlo] at h
      exact h

def cellIndex (i : Fin 2) : EvmYul.UInt256 := .ofNat i.val

theorem cellIndex_nat (i : Fin 2) : (cellIndex i).toNat = i.val :=
  Nat.mod_eq_of_lt (Nat.lt_trans i.isLt (by decide : 2 < EvmYul.UInt256.size))

def storeInput (dynamic : Bool) (i : Fin 2) (v : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) : List EvmYul.UInt256 :=
  if dynamic then cellIndex i :: v :: tail else v :: tail

def storeInstruction (dynamic : Bool) (i : Fin 2) : Instr :=
  if dynamic then .mstoreAt else .mstore i.val

def storeOperations (dynamic : Bool) (i : Fin 2) : List Opcode :=
  if dynamic then storeAtMacro else storeMacro i.val

def storedCore (m : Machine) (i : Fin 2) (v : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) : Machine :=
  {m with stack := words tail, mem := upd m.mem i.val (.val (wmod v.toNat))}

def storedReference (dynamic : Bool) (s : EvmYul.EVM.State) (i : Fin 2)
    (v : EvmYul.UInt256) (tail : List EvmYul.UInt256) : EvmYul.EVM.State :=
  if dynamic then
    stored (scaled {s with stack := cellIndex i :: v :: tail} (cellIndex i) (v :: tail))
      (address (cellIndex i).toNat) v tail
  else stored (pushed {s with stack := v :: tail} i.val) (address i.val) v tail

theorem store_core_exec (dynamic : Bool) (m : Machine) (i : Fin 2)
    (v : EvmYul.UInt256) (tail : List EvmYul.UInt256) :
    (storeInstruction dynamic i).step {m with stack := words (storeInput dynamic i v tail)} =
      .ok (storedCore m i v tail) 0 := by
  cases dynamic with
  | false => rfl
  | true =>
    change Out.ok {m with stack := words tail, mem := upd m.mem (wmod (cellIndex i).toNat).val (.val (wmod v.toNat))} 0 = _
    rw [word_index, cellIndex_nat]
    rfl

theorem store_reference_exec (dynamic : Bool) (s : EvmYul.EVM.State) (i : Fin 2)
    (v : EvmYul.UInt256) (tail : List EvmYul.UInt256) :
    run (storeOperations dynamic i) {s with stack := storeInput dynamic i v tail} =
      .ok (storedReference dynamic s i v tail) := by
  cases dynamic <;> rfl

theorem stored_reference_stack (dynamic : Bool) (s : EvmYul.EVM.State) (i : Fin 2)
    (v : EvmYul.UInt256) (tail : List EvmYul.UInt256) :
    (storedReference dynamic s i v tail).stack = tail := by
  cases dynamic <;> rfl

theorem stored_represents (bound : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound)
    (dynamic : Bool) (m : Machine) (s : EvmYul.EVM.State)
    (h : Represents 2 m s.toMachineState) (i : Fin 2)
    (v : EvmYul.UInt256) (tail : List EvmYul.UInt256) :
    Represents 2 (storedCore m i v tail) (storedReference dynamic s i v tail).toMachineState := by
  have hs := store_preserves bound 2 hp hb m s.toMachineState h i.val i.isLt v
  cases dynamic with
  | false => exact hs.transport _ _ rfl rfl rfl
  | true =>
    dsimp only [storedReference]
    rw [cellIndex_nat]
    exact hs.transport _ _ rfl rfl rfl

/-- Dynamic reads use an actual PUSH of the word index before their scaling macro. -/
def loadInstructions (dynamic : Bool) (i : Fin 2) : List Instr :=
  if dynamic then [.push (.val (wmod (cellIndex i).toNat)), .mloadAt] else [.mload i.val]

def indexPush (i : Fin 2) : Opcode := (.Push .PUSH32, some (cellIndex i, 32))

def loadOperations (dynamic : Bool) (i : Fin 2) : List Opcode :=
  if dynamic then indexPush i :: loadAtMacro else loadMacro i.val

def indexedReference (s : EvmYul.EVM.State) (i : Fin 2) : EvmYul.EVM.State :=
  (prepare s).replaceStackAndIncrPC (cellIndex i :: s.stack) (pcΔ := 33)

def loadedReference (dynamic : Bool) (s : EvmYul.EVM.State) (i : Fin 2) : EvmYul.EVM.State :=
  if dynamic then
    loaded (scaled (indexedReference s i) (cellIndex i) s.stack)
      (address (cellIndex i).toNat) s.stack
  else loaded (pushed s i.val) (address i.val) s.stack

theorem load_core_exec (dynamic : Bool) (m : Machine) (i : Fin 2) :
    Solidity.Evm.run (loadInstructions dynamic i) m =
      .ok {m with stack := m.mem i.val :: m.stack} 0 := by
  cases dynamic with
  | false => rfl
  | true =>
    change Out.ok {m with stack := m.mem (wmod (cellIndex i).toNat).val :: m.stack} 0 = _
    rw [word_index, cellIndex_nat]

theorem load_reference_exec (dynamic : Bool) (s : EvmYul.EVM.State) (i : Fin 2) :
    run (loadOperations dynamic i) s = .ok (loadedReference dynamic s i) := by
  cases dynamic <;> rfl

theorem loaded_reference_stack (dynamic : Bool) (s : EvmYul.EVM.State) (i : Fin 2) :
    (loadedReference dynamic s i).stack = s.toMachineState.lookupMemory (address i.val) :: s.stack := by
  cases dynamic with
  | false => rfl
  | true =>
    dsimp only [loadedReference]
    rw [cellIndex_nat]
    rfl

theorem loaded_represents (dynamic : Bool) (m : Machine) (s : EvmYul.EVM.State)
    (h : Represents 2 m s.toMachineState) (i : Fin 2) :
    Represents 2 {m with stack := m.mem i.val :: m.stack}
      (loadedReference dynamic s i).toMachineState := by
  apply h.transport {m with stack := m.mem i.val :: m.stack} (loadedReference dynamic s i).toMachineState rfl
  · cases dynamic with
    | false => exact stable_active 2 m s.toMachineState h i.val i.isLt
    | true =>
      dsimp only [loadedReference]
      rw [cellIndex_nat]
      exact stable_active 2 m s.toMachineState h i.val i.isLt
  · cases dynamic <;> rfl

/-- Supplied-opcode execution composes without discarding any intermediate state. -/
theorem run_operations_append (xs ys : List Opcode) (s : EvmYul.EVM.State) :
    run (xs ++ ys) s = (run xs s).bind (run ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons op xs ih =>
    cases hs : EvmYul.EVM.step 1 0 (some op) s with
    | error e => simp only [List.cons_append, run, hs, Except.bind]
    | ok next =>
      simp only [List.cons_append, run, hs, Except.bind]
      exact ih next

def memoryInstructions (storeDynamic loadDynamic : Bool) (i : Fin 2) : List Instr :=
  storeInstruction storeDynamic i :: loadInstructions loadDynamic i

def memoryOperations (storeDynamic loadDynamic : Bool) (i : Fin 2) : List Opcode :=
  storeOperations storeDynamic i ++ loadOperations loadDynamic i

private theorem word_observation_injective (a b : EvmYul.UInt256)
    (h : Word.val (wmod a.toNat) = Word.val (wmod b.toNat)) : a = b := by
  have hv := congrArg Fin.val (Word.val.inj h)
  rw [word_index, word_index] at hv
  cases a with
  | mk a => cases b with
    | mk b => exact congrArg EvmYul.UInt256.mk (Fin.ext hv)

/-- All four fixed/dynamic store/load combinations execute their real source
instructions and upstream opcode lists. Dynamic reads execute PUSH-index;
no record update injects an operand between the two runs. The full postrelation,
nonempty tails when supplied, and arbitrary initial neighbor reads are retained. -/
theorem composed_memory (bound : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound)
    (storeDynamic loadDynamic : Bool) (m : Machine) (s : EvmYul.EVM.State)
    (h : Represents 2 m s.toMachineState) (i : Fin 2) (v : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) :
    ∃ m' s',
      Solidity.Evm.run (memoryInstructions storeDynamic loadDynamic i)
        {m with stack := words (storeInput storeDynamic i v tail)} = .ok m' 0 ∧
      run (memoryOperations storeDynamic loadDynamic i)
        {s with stack := storeInput storeDynamic i v tail} = .ok s' ∧
      m'.stack = .val (wmod v.toNat) :: words tail ∧
      m'.stack = words s'.stack ∧ Represents 2 m' s'.toMachineState ∧
      ∀ k : Fin 2, k ≠ i →
        s'.toMachineState.lookupMemory (address k.val) = s.toMachineState.lookupMemory (address k.val) := by
  let m₁ := storedCore m i v tail
  let s₁ := storedReference storeDynamic s i v tail
  let m₂ : Machine := {m₁ with stack := m₁.mem i.val :: m₁.stack}
  let s₂ := loadedReference loadDynamic s₁ i
  have hpost : Represents 2 m₁ s₁.toMachineState :=
    stored_represents bound hp hb storeDynamic m s h i v tail
  have hfinal : Represents 2 m₂ s₂.toMachineState :=
    loaded_represents loadDynamic m₁ s₁ hpost i
  refine ⟨m₂, s₂, ?_, ?_, ?_, ?_, hfinal, ?_⟩
  · unfold memoryInstructions Solidity.Evm.run
    rw [exec_cons_zero, store_core_exec]
    change Solidity.Evm.run (loadInstructions loadDynamic i) m₁ = .ok m₂ 0
    exact load_core_exec loadDynamic m₁ i
  · unfold memoryOperations
    rw [run_operations_append, store_reference_exec]
    change run (loadOperations loadDynamic i) s₁ = .ok s₂
    exact load_reference_exec loadDynamic s₁ i
  · change upd m.mem i.val (.val (wmod v.toNat)) i.val :: words tail = _
    rw [upd_same]
  · change m₁.mem i.val :: m₁.stack = words (loadedReference loadDynamic s₁ i).stack
    rw [loaded_reference_stack]
    change m₁.mem i.val :: m₁.stack =
      .val (wmod (s₁.toMachineState.lookupMemory (address i.val)).toNat) :: words s₁.stack
    rw [lookup_represents bound 2 hp hb m₁ s₁.toMachineState hpost i.val i.isLt,
      stored_reference_stack]
    rfl
  · intro k hne
    have hval : k.val ≠ i.val := fun hk => hne (Fin.ext hk)
    have hframe : m₂.mem k.val = m.mem k.val :=
      upd_other m.mem (.val (wmod v.toNat)) hval
    have hafter := lookup_represents bound 2 hp hb m₂ s₂.toMachineState hfinal k.val k.isLt
    have hbefore := lookup_represents bound 2 hp hb m s.toMachineState h k.val k.isLt
    rw [hframe, hbefore] at hafter
    exact (word_observation_injective _ _ hafter).symm

/-- The composed witness applies to independently inhabited, arbitrary populated
initial memory, not just zero cells. The padding hypothesis is still explicit. -/
theorem populated_composition (bound : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound)
    (storeDynamic loadDynamic : Bool) (lo hi : EvmYul.UInt256) (i : Fin 2)
    (v : EvmYul.UInt256) (tail : List EvmYul.UInt256) :
    ∃ m' s',
      Solidity.Evm.run (memoryInstructions storeDynamic loadDynamic i)
        {(populatedCore lo hi) with stack := words (storeInput storeDynamic i v tail)} = .ok m' 0 ∧
      run (memoryOperations storeDynamic loadDynamic i)
        {(populatedState lo hi) with stack := storeInput storeDynamic i v tail} = .ok s' ∧
      m'.stack = .val (wmod v.toNat) :: words tail ∧
      m'.stack = words s'.stack ∧ Represents 2 m' s'.toMachineState ∧
      ∀ k : Fin 2, k ≠ i →
        s'.toMachineState.lookupMemory (address k.val) =
          (populatedState lo hi).toMachineState.lookupMemory (address k.val) :=
  composed_memory bound hp hb storeDynamic loadDynamic (populatedCore lo hi)
    (populatedState lo hi) (populated_represents lo hi) i v tail

/-- Actual reads of the pure populated initializer return its specified words;
this is proved conditionally from bytes, rather than assumed as a read premise. -/
theorem populated_lookup (bound : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound)
    (lo hi : EvmYul.UInt256) (k : Fin 2) :
    (populatedState lo hi).toMachineState.lookupMemory (address k.val) =
      if k.val = 0 then lo else hi := by
  have hr := lookup_represents bound 2 hp hb (populatedCore lo hi)
    (populatedState lo hi).toMachineState (populated_represents lo hi) k.val k.isLt
  by_cases hk : k.val = 0
  · have hm : (populatedCore lo hi).mem k.val = .val (wmod lo.toNat) := by rw [hk]; rfl
    rw [hm] at hr
    rw [if_pos hk]
    exact (word_observation_injective _ _ hr).symm
  · have hk1 : k.val = 1 := by have := k.isLt; omega
    have hm : (populatedCore lo hi).mem k.val = .val (wmod hi.toNat) := by rw [hk1]; rfl
    rw [hm] at hr
    rw [if_neg hk]
    exact (word_observation_injective _ _ hr).symm

/-- Populated composition with the neighbor's specified initial numeric value,
so a nonzero frame is available directly to controls. -/
theorem populated_composition_values (bound : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound)
    (storeDynamic loadDynamic : Bool) (lo hi : EvmYul.UInt256) (i : Fin 2)
    (v : EvmYul.UInt256) (tail : List EvmYul.UInt256) :
    ∃ m' s',
      Solidity.Evm.run (memoryInstructions storeDynamic loadDynamic i)
        {(populatedCore lo hi) with stack := words (storeInput storeDynamic i v tail)} = .ok m' 0 ∧
      run (memoryOperations storeDynamic loadDynamic i)
        {(populatedState lo hi) with stack := storeInput storeDynamic i v tail} = .ok s' ∧
      m'.stack = .val (wmod v.toNat) :: words tail ∧
      m'.stack = words s'.stack ∧ Represents 2 m' s'.toMachineState ∧
      ∀ k : Fin 2, k ≠ i →
        s'.toMachineState.lookupMemory (address k.val) = if k.val = 0 then lo else hi := by
  obtain ⟨m', s', hc, he, hs, hstack, hrep, hframe⟩ :=
    populated_composition bound hp hb storeDynamic loadDynamic lo hi i v tail
  refine ⟨m', s', hc, he, hs, hstack, hrep, ?_⟩
  intro k hne
  rw [hframe k hne, populated_lookup bound hp hb lo hi k]

end Solidity.Evm.External.Memory

/-- info: 'Solidity.Evm.External.Memory.populated_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.populated_represents

/-- info: 'Solidity.Evm.External.Memory.composed_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.composed_memory

/-- info: 'Solidity.Evm.External.Memory.populated_composition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.populated_composition

/-- info: 'Solidity.Evm.External.Memory.populated_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.populated_lookup

/-- info: 'Solidity.Evm.External.Memory.populated_composition_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.populated_composition_values
