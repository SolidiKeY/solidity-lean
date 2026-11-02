import SolidityBridge.RoadmapV15.P10.BalanceEnvironmentConsumer
import SolidityBridge.RoadmapV15.P10.ExponentConsumer

/-! BALANCE's populated typed/native, address-alias and resource controls.
The funded World witness is only a ledger observation, not installed-code
or transaction correspondence. Complete native State remains observed. -/
namespace SolidityBridge.RoadmapV15.P10.BalanceEnvironmentControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
private def u (n : Nat) : UInt256 := .ofNat n
private def spill : List UInt256 := [u 258,u 513]
private def high : UInt256 := u (2^160+13)
private def frame : Backend.Environment.Frame :=
  {self := Backend.Environment.account (slotWord (u 7))
   sender := Backend.Environment.account (slotWord (u 19))
   value := slotWord (u 3),time := slotWord (u 5),funds := fun _ => slotWord (u 0)}
private def seed (gas : Nat) (warm perm : Bool) : EVM.State :=
  {(default : EVM.State) with
    execLength := 41,gasAvailable := u gas,activeWords := u 1
    memory := ⟨#[0xaa,0xbb]⟩,returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7,source := .ofNat 11,sender := .ofNat 19,weiValue := u 3,perm := perm
      calldata := ⟨#[0x11,0x22,0x33]⟩
      header := {(default : EVM.State).executionEnv.header with timestamp := 5}}
    substate := {(default : Substate) with
      accessedAccounts := if warm then (default : Substate).accessedAccounts.insert (.ofNat 13)
        else (default : Substate).accessedAccounts
      accessedStorageKeys := (default : Substate).accessedStorageKeys.insert (.ofNat 7,u 13)
      refundBalance := u 17
      logSeries := #[⟨.ofNat 7,#[u 5,u 7],⟨#[0x44,0x55]⟩⟩]}
    accountMap := ((((∅ : AccountMap .EVM).insert (.ofNat 7)
      {(default : Account .EVM) with nonce := u 3,balance := u 29}).insert (.ofNat 11)
      {(default : Account .EVM) with nonce := u 5,balance := u 41}).insert (.ofNat 13)
      {(default : Account .EVM) with
        nonce := u 9,balance := u 73
        storage := (∅ : EvmYul.Storage).insert (u 14) (u 4097)
        tstorage := (∅ : EvmYul.Storage).insert (u 14) (u 8193)}).insert (.ofNat 14)
      {(default : Account .EVM) with nonce := u 11,balance := u (2^256-1)}}
private def base (gas : Nat) (warm perm : Bool) : Site .BALANCE :=
  ⟨seed gas warm perm,[.push ⟨1,by decide⟩ #v[0x31],.op .POP],[.op .STOP],by decide⟩
private def image (gas : Nat) (warm perm : Bool) (key : UInt256) (tail : List UInt256) : Site .BALANCE :=
  slotReadSite (base gas warm perm) key tail
private def expected (input : Site .BALANCE) (key value : UInt256) (tail : List UInt256) : EVM.State :=
  {input.state with
    pc := u 4,gasAvailable := u 0,execLength := 42,stack := value::tail
    substate := input.state.substate.addAccessedAccount (AccountAddress.ofUInt256 key)}
private theorem seed_gas (budget : Nat) (warm perm : Bool) :
    (seed budget warm perm).gasAvailable = u budget := rfl
private theorem seed_length (budget : Nat) (warm perm : Bool) :
    (seed budget warm perm).execLength = 41 := rfl

private theorem execute (budget : Nat) (warm perm : Bool) (key value : UInt256) (tail : List UInt256)
    (fits : budget < UInt256.size) (room : tail.length+1 ≤ 1024)
    (cost : EVM.C' (image budget warm perm key tail).state .BALANCE = budget)
    (read : (EvmYul.State.balance (image budget warm perm key tail).state.toState key).2 = value) :
    Backend.Environment.step (balanceFrame frame (image budget warm perm key tail).state.toState) (.op .BALANCE)
      (slotWord key::tail.map slotWord) = some (slotWord value::tail.map slotWord) ∧
    Assembly.driverSteps 1 2 #[] (image budget warm perm key tail).state =
      .ok (expected (image budget warm perm key tail) key value tail) := by
  have charge : EVM.C' (slotReadSite (base budget warm perm) key tail).state .BALANCE = budget := cost
  have gas : EVM.C' (slotReadSite (base budget warm perm) key tail).state .BALANCE ≤
      (base budget warm perm).seed.gasAvailable.toNat := by
    rw [charge]
    change budget ≤ budget % UInt256.size
    rw [Nat.mod_eq_of_lt fits]
  have h := balance_agreement frame (base budget warm perm) key tail room gas 0
  dsimp only at h
  change (EvmYul.State.balance (slotReadSite (base budget warm perm) key tail).state.toState key).2 = value at read
  have source := h.1
  rw [read] at source
  refine ⟨source,?_⟩
  have native := h.2.1
  rw [charge,balance_read_shape,read] at native
  have zero : UInt256.ofNat budget-UInt256.ofNat budget = UInt256.ofNat 0 := by
    change UInt256.mk ((UInt256.ofNat budget).val-(UInt256.ofNat budget).val) = _
    rw [sub_self]
    rfl
  simpa only [image,expected,slotReadSite,Site.state,base,seed_gas,seed_length,u,zero] using native

theorem cold_positive :
    Backend.Environment.step (balanceFrame frame (image 2600 false false (u 13) spill).state.toState) (.op .BALANCE)
      (slotWord (u 13)::spill.map slotWord) = some (slotWord (u 73)::spill.map slotWord) ∧
    Assembly.driverSteps 1 2 #[] (image 2600 false false (u 13) spill).state =
      .ok (expected (image 2600 false false (u 13) spill) (u 13) (u 73) spill) := by
  exact execute _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem warm_positive :
    Backend.Environment.step (balanceFrame frame (image 100 true false (u 13) spill).state.toState) (.op .BALANCE)
      (slotWord (u 13)::spill.map slotWord) = some (slotWord (u 73)::spill.map slotWord) ∧
    Assembly.driverSteps 1 2 #[] (image 100 true false (u 13) spill).state =
      .ok (expected (image 100 true false (u 13) spill) (u 13) (u 73) spill) := by
  exact execute _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem high_alias :
    Backend.Environment.step (balanceFrame frame (image 100 true false (high) spill).state.toState) (.op .BALANCE)
      (slotWord (high)::spill.map slotWord) = some (slotWord (u 73)::spill.map slotWord) ∧
    Assembly.driverSteps 1 2 #[] (image 100 true false (high) spill).state =
      .ok (expected (image 100 true false (high) spill) (high) (u 73) spill) := by
  exact execute _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem owner_balance :
    Backend.Environment.step (balanceFrame frame (image 2600 false false (u 7) spill).state.toState) (.op .BALANCE)
      (slotWord (u 7)::spill.map slotWord) = some (slotWord (u 29)::spill.map slotWord) ∧
    Assembly.driverSteps 1 2 #[] (image 2600 false false (u 7) spill).state =
      .ok (expected (image 2600 false false (u 7) spill) (u 7) (u 29) spill) := by
  exact execute _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem source_balance :
    Backend.Environment.step (balanceFrame frame (image 2600 false false (u 11) spill).state.toState) (.op .BALANCE)
      (slotWord (u 11)::spill.map slotWord) = some (slotWord (u 41)::spill.map slotWord) ∧
    Assembly.driverSteps 1 2 #[] (image 2600 false false (u 11) spill).state =
      .ok (expected (image 2600 false false (u 11) spill) (u 11) (u 41) spill) := by
  exact execute _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem missing_account :
    Backend.Environment.step (balanceFrame frame (image 2600 false false (u 99) spill).state.toState) (.op .BALANCE)
      (slotWord (u 99)::spill.map slotWord) = some (slotWord (u 0)::spill.map slotWord) ∧
    Assembly.driverSteps 1 2 #[] (image 2600 false false (u 99) spill).state =
      .ok (expected (image 2600 false false (u 99) spill) (u 99) (u 0) spill) := by
  exact execute _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem maximum_balance :
    Backend.Environment.step (balanceFrame frame (image 2600 false false (u 14) spill).state.toState) (.op .BALANCE)
      (slotWord (u 14)::spill.map slotWord) = some (slotWord (u (2^256-1))::spill.map slotWord) ∧
    Assembly.driverSteps 1 2 #[] (image 2600 false false (u 14) spill).state =
      .ok (expected (image 2600 false false (u 14) spill) (u 14) (u (2^256-1)) spill) := by
  exact execute _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem writable_read :
    Backend.Environment.step (balanceFrame frame (image 2600 false true (u 13) spill).state.toState) (.op .BALANCE)
      (slotWord (u 13)::spill.map slotWord) = some (slotWord (u 73)::spill.map slotWord) ∧
    Assembly.driverSteps 1 2 #[] (image 2600 false true (u 13) spill).state =
      .ok (expected (image 2600 false true (u 13) spill) (u 13) (u 73) spill) := by
  exact execute _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem stack_boundary :
    Assembly.driverSteps 1 2 #[] (image 2600 false false (u 13) (List.replicate 1023 (u 513))).state =
      .ok (expected (image 2600 false false (u 13) (List.replicate 1023 (u 513)))
        (u 13) (u 73) (List.replicate 1023 (u 513))) := by
  exact (execute _ _ _ _ _ _ (by decide +kernel) (by simp only [List.length_replicate];decide) rfl rfl).2

private def sequence (budget : Nat) (warm : Bool) : Site .BALANCE :=
  slotReadSite ⟨seed budget warm false,[.push ⟨1,by decide⟩ #v[0x31],.op .POP],
    [.push ⟨1,by decide⟩ #v[0x0d],.op .BALANCE,.op .STOP],by decide⟩ (u 13) spill
private def sequenceExpected (budget : Nat) (warm : Bool) : EVM.State :=
  {(sequence budget warm).state with
    pc := u 7,gasAvailable := u 0,execLength := 44,stack := u 73::u 73::spill
    substate := ((sequence budget warm).state.substate.addAccessedAccount (.ofNat 13)).addAccessedAccount (.ofNat 13)}
private def firstExpected (budget : Nat) (warm : Bool) : EVM.State :=
  {(sequence budget warm).state with
    pc := u 4,gasAvailable := u 103,execLength := 42,stack := u 73::spill
    substate := (sequence budget warm).state.substate.addAccessedAccount (.ofNat 13)}
private theorem first_sequence (budget : Nat) (warm : Bool) (cost : Nat)
    (fits : budget < UInt256.size) (adequate : cost ≤ budget)
    (charge : EVM.C' (sequence budget warm).state .BALANCE = cost)
    (remaining : UInt256.ofNat budget-UInt256.ofNat cost = UInt256.ofNat 103) :
    Assembly.driverSteps 1 4 #[] (sequence budget warm).state = .ok (firstExpected budget warm) := by
  let entry : Site .BALANCE := ⟨seed budget warm false,[.push ⟨1,by decide⟩ #v[0x31],.op .POP],
    [.push ⟨1,by decide⟩ #v[0x0d],.op .BALANCE,.op .STOP],by decide⟩
  have actualCost : EVM.C' (slotReadSite entry (u 13) spill).state .BALANCE = cost := charge
  have gas : EVM.C' (slotReadSite entry (u 13) spill).state .BALANCE ≤ entry.seed.gasAvailable.toNat := by
    rw [actualCost]
    change cost ≤ budget % UInt256.size
    rw [Nat.mod_eq_of_lt fits]
    exact adequate
  have h := (balance_agreement frame entry (u 13) spill (by decide +kernel) gas 2).2.1
  dsimp only at h
  have point : (EvmYul.State.balance (slotReadSite entry (u 13) spill).state.toState (u 13)).2 = u 73 := rfl
  rw [actualCost,balance_read_shape,point] at h
  simpa only [entry,sequence,firstExpected,slotReadSite,Site.state,seed_gas,seed_length,u,remaining] using h

theorem cold_repeat :
    Assembly.driverSteps 3 4 #[] (sequence 2703 false).state = .ok (sequenceExpected 2703 false) := by
  have first := first_sequence 2703 false 2600 (by decide +kernel) (by decide) rfl (by decide +kernel)
  rw [fetched_steps_cons 2 2 #[] (sequence 2703 false).state,first]
  rfl

theorem warm_repeat :
    Assembly.driverSteps 3 4 #[] (sequence 203 true).state = .ok (sequenceExpected 203 true) := by
  have first := first_sequence 203 true 100 (by decide +kernel) (by decide) rfl (by decide +kernel)
  rw [fetched_steps_cons 2 2 #[] (sequence 203 true).state,first]
  rfl

theorem source_encoded :
    let word := slotWord high
    let key := UInt256.mk (Scalar.encodeValue .uint word).toFin
    Backend.Environment.step (balanceFrame frame (image 100 true false key spill).state.toState) (.op .BALANCE)
      (word::spill.map slotWord) = some (slotWord (u 73)::spill.map slotWord) ∧
    Assembly.driverSteps 1 2 #[] (image 100 true false key spill).state =
      .ok (expected (image 100 true false key spill) key (u 73) spill) := by
  dsimp only
  have key : UInt256.mk (Scalar.encodeValue .uint (slotWord high)).toFin = high := slotWord_scalar _ _ rfl
  rw [key]
  exact high_alias

/-- Nonzero funding inhabits G31's exact ledger premise. No deployed source
instances or source/native code correspondence is asserted by World.empty. -/
theorem world_funded_observation (contracts : Unit → Contract) :
    (ContractWorld.World.empty contracts (balanceFrame frame (seed 2600 false false).toState).funds).balance (Backend.Environment.account (slotWord (u 13))) = slotWord (u 73) := by
  have h := balance_world_observation
    (ContractWorld.World.empty contracts (balanceFrame frame (seed 2600 false false).toState).funds)
    frame (seed 2600 false false).toState rfl (u 13)
  exact h

theorem unrealized_ledger_negative :
    Backend.Environment.step frame (.op .BALANCE) [slotWord (u 13)] ≠ some [slotWord (u 73)] := by decide +kernel

theorem wrong_owner : (EvmYul.State.balance (seed 2600 false false).toState (u 13)).2 ≠ u 29 := by decide +kernel

theorem wrong_source : (EvmYul.State.balance (seed 2600 false false).toState (u 13)).2 ≠ u 41 := by decide +kernel

theorem source_address_alias :
    Backend.Environment.account (slotWord high) = Backend.Environment.account (slotWord (u 13)) := by decide +kernel

theorem gas_before_arity :
    Assembly.driverSteps 1 2 #[] (base 2599 false false).state = .error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (base 2600 false false).state = .error .StackUnderflow := by
  constructor <;> rfl

theorem fuel_refusal :
    Assembly.driverSteps 1 1 #[] (image 2600 false false (u 13) spill).state = .error .OutOfFuel ∧
    Assembly.driverSteps 1 1 #[] (image 0 false false (u 13) spill).state = .error .OutOfFuel := by
  constructor <;> rfl

theorem warm_target_mismatch :
    Assembly.driverSteps 1 2 #[] (image 100 true false (u 14) spill).state = .error .OutOfGass := by rfl

theorem static_refusal_negative :
    Assembly.driverSteps 1 2 #[] (image 2600 false false (u 13) spill).state ≠ .error .StaticModeViolation := by
  rw [cold_positive.2]
  intro impossible
  cases impossible

theorem storage_warmth_not_accounts :
    Assembly.driverSteps 1 2 #[] (image 100 false false (u 13) spill).state = .error .OutOfGass := by rfl

theorem wrong_world_ledger (contracts : Unit → Contract) :
    (balanceFrame frame (seed 2600 false false).toState).funds ≠
      (ContractWorld.World.empty contracts (fun _ => slotWord (u 0))).funds := by
  intro equal
  have point := congrFun equal (Backend.Environment.account (slotWord (u 13)))
  have distinct : (balanceFrame frame (seed 2600 false false).toState).funds
      (Backend.Environment.account (slotWord (u 13))) ≠ slotWord (u 0) := by decide +kernel
  exact distinct point

#print axioms cold_positive
#print axioms warm_positive
#print axioms high_alias
#print axioms owner_balance
#print axioms source_balance
#print axioms missing_account
#print axioms maximum_balance
#print axioms writable_read
#print axioms stack_boundary
#print axioms cold_repeat
#print axioms warm_repeat
#print axioms source_encoded
#print axioms world_funded_observation
#print axioms unrealized_ledger_negative
#print axioms wrong_owner
#print axioms wrong_source
#print axioms source_address_alias
#print axioms gas_before_arity
#print axioms fuel_refusal
#print axioms warm_target_mismatch
#print axioms static_refusal_negative
#print axioms storage_warmth_not_accounts
#print axioms wrong_world_ledger
end SolidityBridge.RoadmapV15.P10.BalanceEnvironmentControls
