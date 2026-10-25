import SolidityBridge.ExternalEvm

/-!
Account and transaction observations against the upstream state transformers.
The account relation is stated on the actual upstream account map, including
its absent-account default. In particular SELFBALANCE reads the executing
account, independently of the stack and of the caller's balance.
-/
namespace Solidity.Evm.External

def addressWord (a : EvmYul.AccountAddress) : Fin W :=
  ⟨a.val, Nat.lt_trans a.isLt (by decide)⟩

/-- Shared observations, without equating the two models' memory, code or gas. -/
structure EnvironmentAgrees (m : Machine) (s : EvmYul.EVM.State) : Prop where
  stack : m.stack = s.stack.map (fun a => .val (decode a))
  self : m.self = addressWord s.executionEnv.codeOwner
  caller : m.caller = addressWord s.executionEnv.source
  value : m.callvalue = decode s.executionEnv.weiValue
  time : m.timestamp = wmod s.executionEnv.header.timestamp
  balances : ∀ a : EvmYul.AccountAddress,
    (s.accountMap.find? a).elim (EvmYul.UInt256.ofNat 0) (·.balance) =
      encode (wmod (m.bal (addressWord a)))

/-- Every upstream environment has a representing machine. This also makes
the account correspondence nonvacuous for nonzero balances and distinct
caller/executing accounts. Unshared memory and storage start empty. -/
def referenceMachine (s : EvmYul.EVM.State) : Machine :=
  { Machine.init (fun a =>
      ((s.accountMap.find? (EvmYul.AccountAddress.ofNat a.val)).elim
        (EvmYul.UInt256.ofNat 0) (·.balance)).toNat) with
    stack := s.stack.map (fun a => .val (decode a))
    self := addressWord s.executionEnv.codeOwner
    caller := addressWord s.executionEnv.source
    callvalue := decode s.executionEnv.weiValue
    timestamp := wmod s.executionEnv.header.timestamp }

theorem referenceMachine_agrees (s : EvmYul.EVM.State) :
    EnvironmentAgrees (referenceMachine s) s := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro a
  have ha : EvmYul.AccountAddress.ofNat (addressWord a).val = a :=
    Fin.ext (Nat.mod_eq_of_lt a.isLt)
  change (s.accountMap.find? a).elim _ _ =
    encode (wmod (((s.accountMap.find? (EvmYul.AccountAddress.ofNat (addressWord a).val)).elim
      (EvmYul.UInt256.ofNat 0) (·.balance)).toNat))
  rw [ha]
  let v := (s.accountMap.find? a).elim (EvmYul.UInt256.ofNat 0) (·.balance)
  change v = encode (wmod v.toNat)
  have hv : wmod v.toNat = decode v := Fin.ext (Nat.mod_eq_of_lt (decode v).isLt)
  rw [hv, encode_decode]

theorem decode_ofNat (n : Nat) : decode (EvmYul.UInt256.ofNat n) = wmod n := by
  apply Fin.ext
  change n % EvmYul.UInt256.size = n % W
  rw [size_eq]

/-- The actual upstream account lookup determines the word pushed by our step. -/
theorem selfbalance_step (m : Machine) (s : EvmYul.EVM.State)
    (h : EnvironmentAgrees m s) :
    Instr.selfbalance.step m =
      m.next (.val (decode (EvmYul.State.selfbalance s.toState)) :: m.stack) := by
  have hb : (s.accountMap.find? s.executionEnv.codeOwner).elim
      (EvmYul.UInt256.ofNat 0) (·.balance) =
      encode (wmod (m.bal (addressWord s.executionEnv.codeOwner))) :=
    h.balances s.executionEnv.codeOwner
  change EvmYul.State.selfbalance s.toState = _ at hb
  rw [hb, decode_encode, ← h.self]
  rfl

/-- Link to `stateOp`, including its real PC/stack update and framed state. -/
theorem selfbalance_upstream (m : Machine) (s : EvmYul.EVM.State)
    (h : EnvironmentAgrees m s) :
    ∃ m' s', Instr.selfbalance.step m = .ok m' 0 ∧
      EvmYul.EVM.stateOp EvmYul.State.selfbalance s = .ok s' ∧
      EnvironmentAgrees m' s' := by
  refine ⟨_, _, selfbalance_step m s h, rfl, ?_⟩
  exact ⟨congrArg (List.cons _) h.stack, h.self, h.caller, h.value, h.time, h.balances⟩

theorem timestamp_upstream (m : Machine) (s : EvmYul.EVM.State)
    (h : EnvironmentAgrees m s) :
    ∃ m' s', Instr.timestamp.step m = .ok m' 0 ∧
      EvmYul.EVM.stateOp EvmYul.State.timeStamp s = .ok s' ∧
      EnvironmentAgrees m' s' := by
  refine ⟨_, _, rfl, rfl, ?_, h.self, h.caller, h.value, h.time, h.balances⟩
  change .val m.timestamp :: m.stack =
    .val (decode (EvmYul.UInt256.ofNat s.executionEnv.header.timestamp)) :: _
  rw [decode_ofNat, h.time, h.stack]

theorem address_upstream (m : Machine) (s : EvmYul.EVM.State)
    (h : EnvironmentAgrees m s) :
    ∃ m' s', Instr.address.step m = .ok m' 0 ∧
      EvmYul.EVM.executionEnvOp (fun e => .ofNat e.codeOwner.val) s = .ok s' ∧
      EnvironmentAgrees m' s' := by
  refine ⟨_, _, rfl, rfl, ?_, h.self, h.caller, h.value, h.time, h.balances⟩
  change .val m.self :: m.stack =
    .val (decode (EvmYul.UInt256.ofNat s.executionEnv.codeOwner.val)) :: _
  rw [decode_ofNat, h.self, h.stack]
  congr 2
  exact Fin.ext (Nat.mod_eq_of_lt (addressWord s.executionEnv.codeOwner).isLt).symm

theorem caller_upstream (m : Machine) (s : EvmYul.EVM.State)
    (h : EnvironmentAgrees m s) :
    ∃ m' s', Instr.caller.step m = .ok m' 0 ∧
      EvmYul.EVM.executionEnvOp (fun e => .ofNat e.source.val) s = .ok s' ∧
      EnvironmentAgrees m' s' := by
  refine ⟨_, _, rfl, rfl, ?_, h.self, h.caller, h.value, h.time, h.balances⟩
  change .val m.caller :: m.stack =
    .val (decode (EvmYul.UInt256.ofNat s.executionEnv.source.val)) :: _
  rw [decode_ofNat, h.caller, h.stack]
  congr 2
  exact Fin.ext (Nat.mod_eq_of_lt (addressWord s.executionEnv.source).isLt).symm

theorem callvalue_upstream (m : Machine) (s : EvmYul.EVM.State)
    (h : EnvironmentAgrees m s) :
    ∃ m' s', Instr.callvalue.step m = .ok m' 0 ∧
      EvmYul.EVM.executionEnvOp (·.weiValue) s = .ok s' ∧
      EnvironmentAgrees m' s' := by
  refine ⟨_, _, rfl, rfl, ?_, h.self, h.caller, h.value, h.time, h.balances⟩
  change .val m.callvalue :: m.stack = .val (decode s.executionEnv.weiValue) :: _
  rw [h.value, h.stack]

end Solidity.Evm.External

/-- info: 'Solidity.Evm.External.referenceMachine_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.referenceMachine_agrees
/-- info: 'Solidity.Evm.External.selfbalance_upstream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.selfbalance_upstream
