import SolidityBridge.RoadmapV15.P10.ExternalCodeExtent
import Solidity.Backend.Environment.Frames
namespace SolidityBridge.RoadmapV15.P10.ExternalCodeExtentControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
private def u (n : Nat) : UInt256 := .ofNat n
private def spill : List UInt256 := [u 258,u 513]
private def high : UInt256 := u (2^160+13)
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
        nonce := u 9,balance := u 73,code := ⟨#[0x60,0x01,0x00]⟩
        storage := (∅ : EvmYul.Storage).insert (u 14) (u 4097)
        tstorage := (∅ : EvmYul.Storage).insert (u 14) (u 8193)}).insert (.ofNat 14)
      {(default : Account .EVM) with nonce := u 11,balance := u (2^256-1)}}
private def base (gas : Nat) (warm perm : Bool) : Site .EXTCODESIZE :=
  ⟨seed gas warm perm,[.push ⟨1,by decide⟩ #v[0x31],.op .POP],[.op .STOP],by decide⟩
private def image (gas : Nat) (warm perm : Bool) (key : UInt256) (tail : List UInt256) : Site .EXTCODESIZE :=
  slotReadSite (base gas warm perm) key tail
private def expected (input : Site .EXTCODESIZE) (key value : UInt256) (tail : List UInt256) : EVM.State :=
  {input.state with
    pc := u 4,gasAvailable := u 0,execLength := 42,stack := value::tail
    substate := input.state.substate.addAccessedAccount (AccountAddress.ofUInt256 key)}
private theorem seed_gas (budget : Nat) (warm perm : Bool) :
    (seed budget warm perm).gasAvailable = u budget := rfl
private theorem seed_length (budget : Nat) (warm perm : Bool) :
    (seed budget warm perm).execLength = 41 := rfl

private theorem execute (budget : Nat) (warm perm : Bool) (key value : UInt256) (tail : List UInt256)
    (fits : budget < UInt256.size) (room : tail.length+1 ≤ 1024)
    (cost : EVM.C' (image budget warm perm key tail).state .EXTCODESIZE = budget)
    (read : (EvmYul.State.extCodeSize (image budget warm perm key tail).state.toState key).2 = value) :
    Assembly.driverSteps 1 2 #[] (image budget warm perm key tail).state =
      .ok (expected (image budget warm perm key tail) key value tail) := by
  have charge : EVM.C' (slotReadSite (base budget warm perm) key tail).state .EXTCODESIZE = budget := cost
  have gas : EVM.C' (slotReadSite (base budget warm perm) key tail).state .EXTCODESIZE ≤
      (base budget warm perm).seed.gasAvailable.toNat := by
    rw [charge]
    change budget ≤ budget % UInt256.size
    rw [Nat.mod_eq_of_lt fits]
  have h := extcodesize_agreement (base budget warm perm) key tail room gas 0
  dsimp only at h
  change (EvmYul.State.extCodeSize (slotReadSite (base budget warm perm) key tail).state.toState key).2 = value at read
  have native := h.1
  rw [charge,extcodesize_read_shape,read] at native
  have zero : UInt256.ofNat budget-UInt256.ofNat budget = UInt256.ofNat 0 := by
    change UInt256.mk ((UInt256.ofNat budget).val-(UInt256.ofNat budget).val) = _
    rw [sub_self]
    rfl
  simpa only [image,expected,slotReadSite,Site.state,base,seed_gas,seed_length,u,zero] using native

theorem cold_positive : Assembly.driverSteps 1 2 #[] (image 2600 false false (u 13) spill).state =
    .ok (expected (image 2600 false false (u 13) spill) (u 13) (u 3) spill) := by
  exact execute _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem warm_positive : Assembly.driverSteps 1 2 #[] (image 100 true false (u 13) spill).state =
    .ok (expected (image 100 true false (u 13) spill) (u 13) (u 3) spill) := by
  exact execute _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem high_alias : Assembly.driverSteps 1 2 #[] (image 100 true false (high) spill).state =
    .ok (expected (image 100 true false (high) spill) (high) (u 3) spill) := by
  exact execute _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem missing_account : Assembly.driverSteps 1 2 #[] (image 2600 false false (u 99) spill).state =
    .ok (expected (image 2600 false false (u 99) spill) (u 99) (u 0) spill) := by
  exact execute _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem empty_account_code : Assembly.driverSteps 1 2 #[] (image 2600 false false (u 14) spill).state =
    .ok (expected (image 2600 false false (u 14) spill) (u 14) (u 0) spill) := by
  exact execute _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem writable_read : Assembly.driverSteps 1 2 #[] (image 2600 false true (u 13) spill).state =
    .ok (expected (image 2600 false true (u 13) spill) (u 13) (u 3) spill) := by
  exact execute _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem ordered_fetched_code : (image 2600 false false (u 13) spill).state.executionEnv.code.data.toList =
    [0x60,0x31,0x50,0x3b,0x00] := rfl

theorem ordered_external_code :
    ((image 2600 false false (u 13) spill).state.accountMap.find? (.ofNat 13)).map
      (fun account => account.code.data.toList) = some [0x60,0x01,0x00] := rfl

theorem not_balance_or_self_code_size :
    (EvmYul.State.extCodeSize (image 2600 false false (u 13) spill).state.toState (u 13)).2 ≠ u 73 ∧
    (EvmYul.State.extCodeSize (image 2600 false false (u 13) spill).state.toState (u 13)).2 ≠ u 5 := by
  constructor <;> decide +kernel

theorem cold_gas_refusal : Assembly.driverSteps 1 2 #[]
    (image 2599 false false (u 13) spill).state = .error .OutOfGass := rfl

theorem warm_gas_refusal : Assembly.driverSteps 1 2 #[]
    (image 99 true false (u 13) spill).state = .error .OutOfGass := rfl

theorem fuel_precedes_gas : Assembly.driverSteps 1 1 #[]
    (image 0 false false (u 13) spill).state = .error .OutOfFuel := rfl

theorem source_profile_refusal (f : Backend.Environment.Frame) (tail : List Backend.Environment.Word) :
    Backend.Environment.admittedOp .EXTCODESIZE = false ∧
    Backend.Environment.step f (.op .EXTCODESIZE) tail = none := by
  exact ⟨rfl,rfl⟩

theorem stack_boundary :
    let tail := List.replicate 1023 (u 513)
    Assembly.driverSteps 1 2 #[] (image 2600 false false (u 13) tail).state =
      .ok (expected (image 2600 false false (u 13) tail) (u 13) (u 3) tail) := by
  have room : (List.replicate 1023 (u 513)).length+1 ≤ 1024 := by
    rw [List.length_replicate]
  exact execute _ _ _ _ _ _ (by decide +kernel) room rfl rfl

theorem empty_stack : Assembly.driverSteps 1 2 #[]
    {(base 2600 false false).state with stack := []} = .error .StackUnderflow := rfl

theorem gas_precedes_arity : Assembly.driverSteps 1 2 #[]
    {(base 0 false false).state with stack := []} = .error .OutOfGass := rfl

private theorem overflow_tail (tail : List UInt256) (large : 1024 ≤ tail.length) :
    Assembly.driverSteps 1 2 #[] (image 2600 false false (u 13) tail).state = .error .StackOverflow := by
  let start := (image 2600 false false (u 13) tail).state
  have expansion : EVM.memoryExpansionCost start .EXTCODESIZE = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : start.gasAvailable-UInt256.ofNat 0=start.gasAvailable := by
    change UInt256.mk (start.gasAvailable.val-0)=start.gasAvailable
    rw [sub_zero]
  have cost : EVM.C' start .EXTCODESIZE=2600 := rfl
  have gas : ¬start.gasAvailable.toNat < 2600 := by change ¬(u 2600).toNat<2600;decide +kernel
  have enough : ¬start.stack.length<1 := by change ¬(u 13::tail).length<1;simp only [List.length_cons];omega
  have capacity : start.stack.length-1+1>1024 := by change (u 13::tail).length-1+1>1024;simp only [List.length_cons];omega
  have gate : Assembly.driverGate #[] start .EXTCODESIZE = .error .StackOverflow := by
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    simp only [cost,EVM.δ,EVM.α,Option.getD_some,reduceCtorEq,false_and,if_false,
      if_neg (Nat.not_lt_zero _),if_neg gas,if_neg enough,if_pos capacity]
    rfl
  have decoded : EVM.decode start.executionEnv.code start.pc=some (.EXTCODESIZE,none) :=
    DecoderAgreement.decode_all (image 2600 false false (u 13) tail)
  change Assembly.driverSteps 1 2 #[] start = _
  simp only [Assembly.driverSteps]
  rw [decoded]
  dsimp only [Option.option,bind,Except.bind]
  rw [gate]

theorem capacity_refusal : Assembly.driverSteps 1 2 #[]
    (image 2600 false false (u 13) (List.replicate 1024 (u 513))).state = .error .StackOverflow := by
  apply overflow_tail
  rw [List.length_replicate]

/-- A second charge observation on the actual first-step result; not another fetched step. -/
theorem result_address_stays_cold :
    let afterRead := expected (image 2600 false false (u 13) spill) (u 13) (u 3) spill
    Assembly.driverSteps 1 2 #[] (image 2600 false false (u 13) spill).state = .ok afterRead ∧
      EVM.C' afterRead .EXTCODESIZE = 2600 := by
  exact ⟨cold_positive,rfl⟩

/-- The requested address is warm after the actual read; resetting the key here
is a cost probe, not a proved PUSH instruction or second fetched execution. -/
theorem requested_address_warmed :
    let afterRead := expected (image 2600 false false (u 13) spill) (u 13) (u 3) spill
    Assembly.driverSteps 1 2 #[] (image 2600 false false (u 13) spill).state = .ok afterRead ∧
      EVM.C' {afterRead with stack := u 13::spill} .EXTCODESIZE = 100 := by
  exact ⟨cold_positive,rfl⟩

#print axioms stack_boundary
#print axioms empty_stack
#print axioms gas_precedes_arity
#print axioms capacity_refusal
#print axioms result_address_stays_cold
#print axioms requested_address_warmed
#print axioms cold_positive
#print axioms warm_positive
#print axioms high_alias
#print axioms missing_account
#print axioms empty_account_code
#print axioms writable_read
#print axioms ordered_fetched_code
#print axioms ordered_external_code
#print axioms not_balance_or_self_code_size
#print axioms cold_gas_refusal
#print axioms warm_gas_refusal
#print axioms fuel_precedes_gas
#print axioms source_profile_refusal
end SolidityBridge.RoadmapV15.P10.ExternalCodeExtentControls
