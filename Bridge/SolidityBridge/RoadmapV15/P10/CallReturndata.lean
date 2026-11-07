import SolidityBridge.RoadmapV15.P10.FrozenWitness

/-! Populated controls for the fetched CALL/RETURNDATA correspondence that
G42's `WorldCalls.FetchedPremises.Returndata` names as its P10 input; the
general law is `CallReturndataLaw`.

The single-step CALL controls rewrite with the frozen
`FrozenV1.api.charged.checked_call` field and then evaluate the pinned
`EVM.call`, including `Θ`/`Ξ` on the callee, in the kernel; the two-step
`absent_then_size` evaluates `Assembly.driverSteps` directly. The caller has
memory `[0xaa, 0xbb]` and a stale return buffer `[0xcc, 0xdd]`. Callee 31 is
either absent or carries the one-byte body INVALID. Kernel evaluation of
longer callee bodies exceeds the module memory budget (a three-instruction
callee peaked above 14 GB), and the identity precompile does not reduce in the
kernel, so no populated control returns nonempty data.

`outcome_needs_callee`: two states that agree on the execution environment,
PC, stack, gas, memory, stale buffer and the caller's nonce and balance push
different CALL flags. Flag dependence alone is expressible in the core through
its free `Machine.accepts` oracle; what the core lacks is a return buffer and a
code map (and its `CALL` is a two-operand payment,
`Solidity.Evm.External.call_arity_mismatch`).

`Site` remains a constructed state (no compiler/source origin); gas, resource,
Osaka and transaction adequacy are not asserted. -/
namespace SolidityBridge.RoadmapV15.P10.CallReturndata
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private def u (n : Nat) : UInt256 := .ofNat n

/-- A one-byte callee whose only instruction is INVALID (`0xfe`). -/
def invalid : ByteArray := ⟨#[0xfe]⟩

private def tail : List UInt256 := [u 258,u 513]
/-- CALL operands, top first: gas 5000, `recipient`, value 0, input window
`[0,1)`, output window `[1,2)`. -/
private def operands (recipient : Nat) : List UInt256 :=
  [u 5000,u recipient,u 0,u 0,u 1,u 1,u 1] ++ tail

/-- Caller 7 with memory `[0xaa, 0xbb]` and a stale return buffer `[0xcc, 0xdd]`;
account 31 carries `callee` as code, or is absent when `callee` is `none`. -/
def seed (recipient : Nat) (callee : Option ByteArray) : EVM.State :=
  let accounts : AccountMap .EVM :=
    ((∅ : AccountMap .EVM).insert (.ofNat 7)
      {(default : Account .EVM) with nonce := u 3,balance := u 29}).insert (.ofNat 19)
      {(default : Account .EVM) with nonce := u 6,balance := u 43}
  {(default : EVM.State) with
    execLength := 41,gasAvailable := u 100000,stack := operands recipient,activeWords := u 1
    memory := ⟨#[0xaa,0xbb]⟩,returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7,source := .ofNat 19,sender := .ofNat 19,perm := true}
    accountMap := match callee with
      | none => accounts
      | some code => accounts.insert (.ofNat 31) {(default : Account .EVM) with code := code}}

/-- `CALL; RETURNDATASIZE; STOP` at PC 0. -/
def site (recipient : Nat) (callee : Option ByteArray) : Site .CALL :=
  ⟨seed recipient callee,[],[.op .RETURNDATASIZE,.op .STOP],by decide⟩

private def valid : Array UInt256 := #[]

/-- PC, stack, return buffer, memory and the caller/account-31 balances. -/
def observe (s : EVM.State) :=
  (s.pc.toNat,s.stack.map UInt256.toNat,s.returnData.data.toList,s.memory.data.toList,
   (s.accountMap.find! (.ofNat 7)).balance.toNat,
   ((s.accountMap.find? (.ofNat 31)).map (fun a => a.balance.toNat)).getD 0)

/-- Kernel-evaluated observation of a driver run; the error case is `none`. -/
def run (steps fuel : Nat) (s : EVM.State) :=
  (Assembly.driverSteps steps fuel valid s).toOption.map observe

/-- An absent callee: flag 1, the stale buffer is cleared, memory is kept. -/
theorem absent_call :
    run 1 52 (site 31 none).state = some (1,[1,258,513],[],[0xaa,0xbb],29,0) := by
  unfold run
  rw [FrozenV1.api.charged.checked_call]
  decide +kernel

/-- A callee whose code fails: flag 0, and the stale buffer is still cleared. -/
theorem invalid_call :
    run 1 52 (site 31 (some invalid)).state = some (1,[0,258,513],[],[0xaa,0xbb],29,0) := by
  unfold run
  rw [FrozenV1.api.charged.checked_call]
  decide +kernel

/-- The following RETURNDATASIZE reads the CALL's buffer (size 0), not the
stale caller buffer (size 2). -/
theorem absent_then_size :
    run 2 53 (site 31 none).state = some (2,[0,1,258,513],[],[0xaa,0xbb],29,0) := by
  decide +kernel

/-- The two seeds agree on every caller-frame field. -/
theorem same_caller_frame :
    (site 31 none).state.executionEnv = (site 31 (some invalid)).state.executionEnv ∧
    (site 31 none).state.pc = (site 31 (some invalid)).state.pc ∧
    (site 31 none).state.stack = (site 31 (some invalid)).state.stack ∧
    (site 31 none).state.gasAvailable = (site 31 (some invalid)).state.gasAvailable ∧
    (site 31 none).state.memory = (site 31 (some invalid)).state.memory ∧
    (site 31 none).state.returnData = (site 31 (some invalid)).state.returnData ∧
    ((site 31 none).state.accountMap.find? (.ofNat 7)).map (fun a => (a.nonce,a.balance)) =
      ((site 31 (some invalid)).state.accountMap.find? (.ofNat 7)).map (fun a => (a.nonce,a.balance)) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,by decide +kernel⟩

/-- The CALL outcome is not determined by the caller frame: with the same
frame, the success flag pushed by CALL depends on the callee's code. -/
theorem outcome_needs_callee :
    ∃ s₁ s₂ : EVM.State,
      s₁.executionEnv = s₂.executionEnv ∧ s₁.pc = s₂.pc ∧ s₁.stack = s₂.stack ∧
      s₁.gasAvailable = s₂.gasAvailable ∧ s₁.memory = s₂.memory ∧
      s₁.returnData = s₂.returnData ∧
      (s₁.accountMap.find? (.ofNat 7)).map (fun a => (a.nonce,a.balance)) =
        (s₂.accountMap.find? (.ofNat 7)).map (fun a => (a.nonce,a.balance)) ∧
      (run 1 52 s₁).map (fun o => o.2.1) ≠ (run 1 52 s₂).map (fun o => o.2.1) := by
  obtain ⟨env,pc,stack,gas,memory,ret,caller⟩ := same_caller_frame
  refine ⟨_,_,env,pc,stack,gas,memory,ret,caller,?_⟩
  rw [absent_call,invalid_call]
  decide

/-- info: 'SolidityBridge.RoadmapV15.P10.CallReturndata.absent_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms absent_call
/-- info: 'SolidityBridge.RoadmapV15.P10.CallReturndata.invalid_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms invalid_call
/-- info: 'SolidityBridge.RoadmapV15.P10.CallReturndata.absent_then_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms absent_then_size
/-- info: 'SolidityBridge.RoadmapV15.P10.CallReturndata.outcome_needs_callee' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms outcome_needs_callee
end SolidityBridge.RoadmapV15.P10.CallReturndata
