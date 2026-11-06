import SolidityBridge.RoadmapV15.P10.StorageReadConsumer
import Solidity.Backend.Environment.Observations

/-! BALANCE consumes the existing typed environment slice and actual account
ledger. Only its funds field is realized; other source-frame relations remain
separate. No arbitrary-callee/world execution is inferred from a balance read. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

/-- Preserve the existing frame fields and obtain its ledger from actual
accounts. This adapter does not assert the other fields match a source state. -/
def balanceFrame (frame : Backend.Environment.Frame) (s : EvmYul.State .EVM) : Backend.Environment.Frame :=
  {frame with
    funds := fun a => slotWord
      ((s.accountMap.find? (.ofNat a.1.val.toNat)).elim (UInt256.ofNat 0) (·.balance))}

theorem source_key_roundtrip (word : Backend.Environment.Word) :
    slotWord (UInt256.mk (Scalar.encodeValue .uint word).toFin) = word := by
  apply Subtype.ext
  change ((Scalar.encodeValue .uint word).toNat : Int) = word.val
  rw [Scalar.encode_uint_toNat]
  exact Int.toNat_of_nonneg (Scalar.uint_range word).1

/-- Source account truncation and the actual pin choose the same low160 bits. -/
theorem balance_address (key : UInt256) :
    AccountAddress.ofNat (Backend.Environment.account (slotWord key)).1.val.toNat =
      AccountAddress.ofUInt256 key := by
  have observed := congrArg Int.toNat (Backend.Environment.account_value (slotWord key))
  have number : (Backend.Environment.account (slotWord key)).1.val.toNat = key.toNat % 2^160 := by
    simpa only [slotWord,Int.toNat_natCast] using observed
  rw [number]
  rfl

theorem balance_source_step (frame : Backend.Environment.Frame) (s : EvmYul.State .EVM)
    (key : UInt256) (tail : List UInt256) :
    Backend.Environment.step (balanceFrame frame s) (.op .BALANCE) (slotWord key::tail.map slotWord) =
      some (slotWord (EvmYul.State.balance s key).2::tail.map slotWord) := by
  simp only [Backend.Environment.step,balanceFrame]
  rw [balance_address]
  rfl

private theorem balance_byte (site : Site .BALANCE) :
    site.state.executionEnv.code.get? (Backend.encode site.before).length = some Backend.Op.BALANCE.code := by
  change (Backend.encode (site.before ++ .op .BALANCE :: site.after)).toArray[(Backend.encode site.before).length]? = _
  rw [List.getElem?_toArray]
  simp only [Backend.encode_append,Backend.encode_cons,Instr.encode,List.singleton_append]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self,List.getElem?_cons_zero]

theorem decode_balance (site : Site .BALANCE) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (.BALANCE,none) := by
  have byte := balance_byte site
  simp only [EVM.decode,Site.pc_nat,byte]
  rfl

theorem balance_cost (site : Site .BALANCE) (key : UInt256) (tail : List UInt256) :
    EVM.C' (slotReadSite site key tail).state .BALANCE =
      if site.seed.substate.accessedAccounts.contains (AccountAddress.ofUInt256 key)
      then 100 else 2600 := by rfl

theorem balance_cost_bound (site : Site .BALANCE) (key : UInt256) (tail : List UInt256) :
    EVM.C' (slotReadSite site key tail).state .BALANCE ≤ 2600 := by
  rw [balance_cost]
  split <;> decide

private theorem balance_gate (s : EVM.State) (gas : EVM.C' s .BALANCE ≤ s.gasAvailable.toNat)
    (enough : 1 ≤ s.stack.length) (room : s.stack.length ≤ 1024) :
    Assembly.driverGate #[] s .BALANCE = .ok (s,EVM.C' s .BALANCE) := by
  have expansion : EVM.memoryExpansionCost s .BALANCE = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have capacity : s.stack.length-1+1 ≤ 1024 := by omega
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [EVM.δ,EVM.α,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge enough),if_neg (Nat.not_lt_of_ge capacity)]
  cases s.executionEnv.perm <;> rfl

theorem balance_agreement (frame : Backend.Environment.Frame) (site : Site .BALANCE)
    (key : UInt256) (tail : List UInt256) (room : tail.length+1 ≤ 1024)
    (gas : EVM.C' (slotReadSite site key tail).state .BALANCE ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (slotReadSite site key tail).state
    let read := EvmYul.State.balance input.toState key
    let cost := EVM.C' input .BALANCE
    let next := ({Assembly.chargedPrepare input cost with toState := read.1}).replaceStackAndIncrPC (read.2::tail)
    Backend.Environment.step (balanceFrame frame input.toState) (.op .BALANCE) (slotWord key::tail.map slotWord) =
      some (slotWord read.2::tail.map slotWord) ∧
      Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  refine ⟨balance_source_step frame _ key tail,?_⟩
  let input := (slotReadSite site key tail).state
  let cost := EVM.C' input .BALANCE
  have gate : Assembly.driverGate #[] input .BALANCE = .ok (input,cost) := by
    apply balance_gate input gas
    · change 1 ≤ (key::tail).length
      simp only [List.length_cons];omega
    · change (key::tail).length ≤ 1024
      exact room
  have step : EVM.step (fuel+1) cost (some (.BALANCE,none)) input =
      .ok (({Assembly.chargedPrepare input cost with toState := (EvmYul.State.balance input.toState key).1}).replaceStackAndIncrPC ((EvmYul.State.balance input.toState key).2::tail)) := by rfl
  constructor
  · simp only [Assembly.driverSteps]
    rw [decode_balance (slotReadSite site key tail)]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel #[] input input _ (.BALANCE,none) cost
      (decode_balance _) gate step (by unfold Assembly.NonhaltingOpcode;decide)

theorem source_balance_agreement (frame : Backend.Environment.Frame) (site : Site .BALANCE)
    (word : Backend.Environment.Word) (tail : List UInt256) (room : tail.length+1 ≤ 1024)
    (gas : EVM.C' (slotReadSite site ⟨(Scalar.encodeValue .uint word).toFin⟩ tail).state .BALANCE ≤
      site.seed.gasAvailable.toNat) (fuel : Nat) :
    let key := UInt256.mk (Scalar.encodeValue .uint word).toFin
    let input := (slotReadSite site key tail).state
    let read := EvmYul.State.balance input.toState key
    let cost := EVM.C' input .BALANCE
    let next := ({Assembly.chargedPrepare input cost with toState := read.1}).replaceStackAndIncrPC (read.2::tail)
    Backend.Environment.step (balanceFrame frame input.toState) (.op .BALANCE) (word::tail.map slotWord) =
      some (slotWord read.2::tail.map slotWord) ∧
      Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  have h := balance_agreement frame site ⟨(Scalar.encodeValue .uint word).toFin⟩ tail room gas fuel
  dsimp only at h ⊢
  rw [source_key_roundtrip] at h
  exact h

theorem balance_read_shape (s : EVM.State) (key : UInt256) (tail : List UInt256) (cost : Nat) :
    ({Assembly.chargedPrepare s cost with toState := (EvmYul.State.balance s.toState key).1}).replaceStackAndIncrPC ((EvmYul.State.balance s.toState key).2::tail) =
    {s with
      pc := s.pc + .ofNat 1,gasAvailable := s.gasAvailable - .ofNat cost,
      execLength := s.execLength+1,stack := (EvmYul.State.balance s.toState key).2::tail,
      substate := s.substate.addAccessedAccount (AccountAddress.ofUInt256 key)} := by rfl

/-- Consume G31's existing typed world-ledger premise for this observation
only. Neither ledger production nor world/call execution follows from it. -/
theorem balance_world_observation {K : Type} {contracts : K → Contract}
    (world : ContractWorld.World contracts) (frame : Backend.Environment.Frame)
    (s : EvmYul.State .EVM) (ledger : (balanceFrame frame s).funds = world.funds) (key : UInt256) :
    world.balance (Backend.Environment.account (slotWord key)) = slotWord (EvmYul.State.balance s key).2 := by
  have configured := Backend.Environment.world_balance world (balanceFrame frame s) ledger (slotWord key) []
  have actual : Backend.Environment.step (balanceFrame frame s) (.op .BALANCE) [slotWord key] =
      some [slotWord (EvmYul.State.balance s key).2] := by
    simpa only [List.map_nil] using balance_source_step frame s key []
  exact (List.cons.inj (Option.some.inj (actual.symm.trans configured))).1.symm

#print axioms balance_world_observation
#print axioms source_key_roundtrip
#print axioms balance_address
#print axioms balance_source_step
#print axioms decode_balance
#print axioms balance_cost
#print axioms balance_cost_bound
#print axioms balance_agreement
#print axioms source_balance_agreement
#print axioms balance_read_shape
end SolidityBridge.RoadmapV15.P10
