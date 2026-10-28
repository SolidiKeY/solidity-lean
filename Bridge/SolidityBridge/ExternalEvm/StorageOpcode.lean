import SolidityBridge.ExternalEvm.StorageAddresses
import EvmYul.EVM.Semantics

/-! Small actual-dispatcher execution lemmas. Opaque proof boundaries prevent
whole-macro normalization from duplicating large upstream state records. -/
namespace Solidity.Evm.StorageSlots

def prepare (s : EvmYul.EVM.State) : EvmYul.EVM.State :=
  {s with execLength := s.execLength + 1, gasAvailable := s.gasAvailable - .ofNat 0}

theorem push_step (s : EvmYul.EVM.State) (value : EvmYul.UInt256) :
    ∃ out, EvmYul.EVM.step 1 0 (some (.Push .PUSH32, some (value, 32))) s = .ok out ∧
      out.stack = value :: s.stack ∧ out.toState = s.toState ∧ out.memory = s.memory :=
  ⟨_, rfl, rfl, rfl, rfl⟩

theorem pop_step (s : EvmYul.EVM.State) (value : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) (hs : s.stack = value :: tail) :
    ∃ out, EvmYul.EVM.step 1 0 (some (.POP, none)) s = .ok out ∧
      out.stack = tail ∧ out.toState = s.toState ∧ out.memory = s.memory := by
  let out := (prepare s).replaceStackAndIncrPC tail
  refine ⟨out, ?_, rfl, rfl, rfl⟩
  have he : EvmYul.EVM.step 1 0 (some (.POP, none))
      {s with stack := value :: tail} = .ok out := rfl
  rw [← hs] at he
  exact he

theorem keccak_step (s : EvmYul.EVM.State) (start size : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) (hs : s.stack = start :: size :: tail) :
    ∃ out, EvmYul.EVM.step 1 0 (some (.KECCAK256, none)) s = .ok out ∧
      out.stack = (s.toMachineState.keccak256 start size).1 :: tail ∧
      out.toState = s.toState ∧ out.memory = s.memory := by
  let pair := (prepare s).toMachineState.keccak256 start size
  let out := ({prepare s with toMachineState := pair.2}).replaceStackAndIncrPC (pair.1 :: tail)
  refine ⟨out, ?_, rfl, rfl, rfl⟩
  have he : EvmYul.EVM.step 1 0 (some (.KECCAK256, none))
      {s with stack := start :: size :: tail} = .ok out := rfl
  rw [← hs] at he
  exact he

theorem mstore_step (s : EvmYul.EVM.State) (pos value : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) (hs : s.stack = pos :: value :: tail) :
    ∃ out, EvmYul.EVM.step 1 0 (some (.MSTORE, none)) s = .ok out ∧
      out.stack = tail ∧ out.toState = s.toState ∧
      out.memory = (s.toMachineState.mstore pos value).memory := by
  let machine := (prepare s).toMachineState.mstore pos value
  let out := ({prepare s with toMachineState := machine}).replaceStackAndIncrPC tail
  refine ⟨out, ?_, rfl, rfl, rfl⟩
  have he : EvmYul.EVM.step 1 0 (some (.MSTORE, none))
      {s with stack := pos :: value :: tail} = .ok out := rfl
  rw [← hs] at he
  exact he

theorem sload_step (s : EvmYul.EVM.State) (key : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) (hs : s.stack = key :: tail) :
    ∃ out, EvmYul.EVM.step 1 0 (some (.SLOAD, none)) s = .ok out ∧
      out.stack = (EvmYul.State.sload s.toState key).2 :: tail ∧
      out.toState = (EvmYul.State.sload s.toState key).1 := by
  let out := ({prepare s with toState := (EvmYul.State.sload s.toState key).1}).replaceStackAndIncrPC
    ((EvmYul.State.sload s.toState key).2 :: tail)
  refine ⟨out, ?_, rfl, rfl⟩
  have he : EvmYul.EVM.step 1 0 (some (.SLOAD, none))
      {s with stack := key :: tail} = .ok out := rfl
  rw [← hs] at he
  exact he

theorem sstore_step (s : EvmYul.EVM.State) (key value : EvmYul.UInt256)
    (tail : List EvmYul.UInt256) (hs : s.stack = key :: value :: tail) :
    ∃ out, EvmYul.EVM.step 1 0 (some (.SSTORE, none)) s = .ok out ∧
      out.stack = tail ∧ out.toState = EvmYul.State.sstore s.toState key value := by
  let out := ({prepare s with toState := EvmYul.State.sstore s.toState key value}).replaceStackAndIncrPC tail
  refine ⟨out, ?_, rfl, rfl⟩
  have he : EvmYul.EVM.step 1 0 (some (.SSTORE, none))
      {s with stack := key :: value :: tail} = .ok out := rfl
  rw [← hs] at he
  exact he

theorem sload_preserves (s : EvmYul.State .EVM) (a : EvmYul.UInt256) :
    storageRead (EvmYul.State.sload s a).1 = storageRead s := rfl

theorem sload_account (s : EvmYul.State .EVM) (a : EvmYul.UInt256) :
    (EvmYul.State.sload s a).1.lookupAccount (EvmYul.State.sload s a).1.executionEnv.codeOwner =
      s.lookupAccount s.executionEnv.codeOwner := rfl

def freshAccount : EvmYul.EVM.State :=
  { (default : EvmYul.EVM.State) with
    accountMap := (∅ : EvmYul.AccountMap .EVM).insert (EvmYul.AccountAddress.ofNat 0) default }

/-- Actual underflow controls are retained outside the admitted stack shapes. -/
theorem sload_underflow (m : Machine) (s : EvmYul.EVM.State) :
    Instr.sload.step {m with stack := []} = .fault ∧
    EvmYul.EVM.step 1 0 (some (.SLOAD, none)) {s with stack := []} =
      .error .StackUnderflow := ⟨rfl, rfl⟩

theorem sstore_underflow (m : Machine) (s : EvmYul.EVM.State) :
    Instr.sstore.step {m with stack := []} = .fault ∧
    EvmYul.EVM.step 1 0 (some (.SSTORE, none)) {s with stack := []} =
      .error .StackUnderflow := ⟨rfl, rfl⟩

theorem array_same_stack_refused (m : Machine) (s : EvmYul.EVM.State) (a : Slot) :
    (∃ m', Instr.keccakArr.step {m with stack := [.slot a]} = .ok m' 0) ∧
    EvmYul.EVM.step 1 0 (some (.KECCAK256, none)) {s with stack := [address a]} =
      .error .StackUnderflow := ⟨⟨_, rfl⟩, rfl⟩

end Solidity.Evm.StorageSlots
