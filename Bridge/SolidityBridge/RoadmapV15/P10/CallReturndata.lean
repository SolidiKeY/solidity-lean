import SolidityBridge.RoadmapV15.P10.FrozenWitness

/-! Validation of the fetched CALL/RETURNDATA correspondence that G42's
`WorldCalls.FetchedPremises.Returndata` names as its P10 input.

Every CALL law below is obtained by rewriting with the frozen
`FrozenV1.api.charged.checked_call` field, so it exercises exactly the version-1
API that consumers import, and then evaluates the pinned reference `EVM.call`
(including the callee's own code under `Θ`/`Ξ`) in the kernel. The callees are
populated: one returns the byte `0x2a`, one reverts with `0x2b`, and one is an
absent account. The caller's stale return buffer `[0xcc, 0xdd]` is distinct
from every callee output, so each law shows the buffer is replaced, not kept.

`returndata_needs_callee` is the decisive negative: two reference states that
agree on every caller-frame field (code, PC, stack, gas, memory, stale return
data, execution environment and the caller's account) produce different
post-CALL return data. So the returndata after a CALL is a function of the
callee's code, which the core `Evm.Machine` (no code map, no return buffer,
two-operand payment `CALL`, see `ExternalEvm.Obstructions.call_arity_mismatch`)
does not carry. A `FetchedPremises.Returndata` adapter from this API therefore
needs a callee/world execution producer and a core-to-reference CALL
representation; this module supplies neither and assumes neither.

`Site` remains a constructed state (no compiler/source origin), and gas,
resource, Osaka and transaction adequacy are not asserted. -/
namespace SolidityBridge.RoadmapV15.P10.CallReturndata
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private def u (n : Nat) : UInt256 := .ofNat n

/-- `PUSH1 0x2a PUSH1 0 MSTORE8 PUSH1 1 PUSH1 0 RETURN`: returns `[0x2a]`. -/
def returning : ByteArray := ⟨#[0x60,0x2a,0x60,0x00,0x53,0x60,0x01,0x60,0x00,0xf3]⟩
/-- `PUSH1 0x2b PUSH1 0 MSTORE8 PUSH1 1 PUSH1 0 REVERT`: reverts with `[0x2b]`. -/
def reverting : ByteArray := ⟨#[0x60,0x2b,0x60,0x00,0x53,0x60,0x01,0x60,0x00,0xfd]⟩

private def tail : List UInt256 := [u 258,u 513]
/-- CALL operands, top first: gas 5000, callee 31, value 0, input `[0,0)`,
output window `[0,1)`. -/
private def operands : List UInt256 := [u 5000,u 31,u 0,u 0,u 0,u 0,u 1] ++ tail

/-- Caller 7 with populated memory and a stale return buffer; callee 31
carries `callee` as code, or is absent when `callee` is `none`. -/
def seed (callee : Option ByteArray) : EVM.State :=
  let accounts : AccountMap .EVM :=
    ((∅ : AccountMap .EVM).insert (.ofNat 7)
      {(default : Account .EVM) with nonce := u 3,balance := u 29}).insert (.ofNat 19)
      {(default : Account .EVM) with nonce := u 6,balance := u 43}
  {(default : EVM.State) with
    execLength := 41,gasAvailable := u 100000,stack := operands,activeWords := u 1
    memory := ⟨#[0xaa,0xbb]⟩,returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7,source := .ofNat 19,sender := .ofNat 19,perm := true}
    accountMap := match callee with
      | none => accounts
      | some code => accounts.insert (.ofNat 31) {(default : Account .EVM) with code := code}}

/-- `CALL; RETURNDATASIZE; STOP` at PC 0. -/
def site (callee : Option ByteArray) : Site .CALL :=
  ⟨seed callee,[],[.op .RETURNDATASIZE,.op .STOP],by decide⟩

private def valid : Array UInt256 := #[]

/-- PC, stack, return buffer, memory and the caller/callee balances. -/
def observe (s : EVM.State) :=
  (s.pc.toNat,s.stack.map UInt256.toNat,s.returnData.data.toList,s.memory.data.toList,
   (s.accountMap.find! (.ofNat 7)).balance.toNat,
   ((s.accountMap.find? (.ofNat 31)).map (fun a => a.balance.toNat)).getD 0)

/-- Kernel-evaluated observation of a driver run; the error case is `none`. -/
def run (steps fuel : Nat) (s : EVM.State) :=
  (Assembly.driverSteps steps fuel valid s).toOption.map observe

/-- A returning callee: success flag 1, return buffer `[0x2a]`, and the output
window writes `0x2a` over the caller's first memory byte. -/
theorem returning_call :
    run 1 52 (site (some returning)).state = some (1,[1,258,513],[0x2a],[0x2a,0xbb],29,0) := by
  unfold run
  rw [FrozenV1.api.charged.checked_call]
  decide +kernel

/-- A reverting callee: flag 0, yet the revert bytes become the return buffer
and are written to the output window. -/
theorem reverting_call :
    run 1 52 (site (some reverting)).state = some (1,[0,258,513],[0x2b],[0x2b,0xbb],29,0) := by
  unfold run
  rw [FrozenV1.api.charged.checked_call]
  decide +kernel

/-- An absent callee: flag 1, the stale buffer is cleared and memory is kept. -/
theorem absent_call :
    run 1 52 (site none).state = some (1,[1,258,513],[],[0xaa,0xbb],29,0) := by
  unfold run
  rw [FrozenV1.api.charged.checked_call]
  decide +kernel

/-- The following RETURNDATASIZE observes the callee's output size (1), not
the stale caller buffer (2). -/
theorem returning_then_size :
    run 2 53 (site (some returning)).state = some (2,[1,1,258,513],[0x2a],[0x2a,0xbb],29,0) := by
  decide +kernel

theorem absent_then_size :
    run 2 53 (site none).state = some (2,[0,1,258,513],[],[0xaa,0xbb],29,0) := by
  decide +kernel

/-- The two seeds agree on every caller-frame field. -/
theorem same_caller_frame :
    (site (some returning)).state.executionEnv = (site (some reverting)).state.executionEnv ∧
    (site (some returning)).state.pc = (site (some reverting)).state.pc ∧
    (site (some returning)).state.stack = (site (some reverting)).state.stack ∧
    (site (some returning)).state.gasAvailable = (site (some reverting)).state.gasAvailable ∧
    (site (some returning)).state.memory = (site (some reverting)).state.memory ∧
    (site (some returning)).state.returnData = (site (some reverting)).state.returnData ∧
    ((site (some returning)).state.accountMap.find? (.ofNat 7)).map (fun a => (a.nonce,a.balance)) =
      ((site (some reverting)).state.accountMap.find? (.ofNat 7)).map (fun a => (a.nonce,a.balance)) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,by decide +kernel⟩

/-- Post-CALL return data is not determined by the caller frame: it depends on
the callee's code. -/
theorem returndata_needs_callee :
    ∃ s₁ s₂ : EVM.State,
      s₁.executionEnv = s₂.executionEnv ∧ s₁.pc = s₂.pc ∧ s₁.stack = s₂.stack ∧
      s₁.gasAvailable = s₂.gasAvailable ∧ s₁.memory = s₂.memory ∧
      s₁.returnData = s₂.returnData ∧
      (s₁.accountMap.find? (.ofNat 7)).map (fun a => (a.nonce,a.balance)) =
        (s₂.accountMap.find? (.ofNat 7)).map (fun a => (a.nonce,a.balance)) ∧
      (run 1 52 s₁).map (fun o => o.2.2.1) ≠ (run 1 52 s₂).map (fun o => o.2.2.1) := by
  obtain ⟨env,pc,stack,gas,memory,ret,caller⟩ := same_caller_frame
  refine ⟨_,_,env,pc,stack,gas,memory,ret,caller,?_⟩
  rw [returning_call,reverting_call]
  decide

#print axioms returning_call
#print axioms reverting_call
#print axioms absent_call
#print axioms returning_then_size
#print axioms absent_then_size
#print axioms returndata_needs_callee

end SolidityBridge.RoadmapV15.P10.CallReturndata
