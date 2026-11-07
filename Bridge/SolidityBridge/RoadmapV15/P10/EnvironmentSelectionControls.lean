import SolidityBridge.RoadmapV15.P10.EnvironmentSelection
import SolidityBridge.RoadmapV15.P10.SelfBalanceControls
import Solidity.Backend.Environment.ObservationsChecks

/-! Inhabited source/native observation clients built with the existing G31
represented-state fixture. This is not reached-entry or physical/world evidence. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
namespace EnvironmentSelectionControls
open WordPushFixtures (u accounts spill)
def keys : List EnvKey := [.msgSender,.msgValue,.timestamp,.selfBalance,.selfAddress]
def result : EnvKey → UInt256
  | .msgSender => u 11
  | .msgValue => u 37
  | .timestamp => u 260
  | .selfBalance => u 29
  | .selfAddress => u 7
def site (k : EnvKey) (perm : Bool) : Site (environmentOp k) :=
  HeaderEnvironmentControls.entry (environmentOp k) 9 perm (UInt256.size+260) accounts spill
def frame : Backend.Environment.Frame := SelfBalanceControls.frame
def view (k : EnvKey) (perm : Bool) : Backend.Environment.Frame :=
  nativeEnvironmentFrame frame (site k perm).state.toState
def source (k : EnvKey) (perm : Bool) : Solidity.State default [] :=
  Backend.Environment.represented (State.init default) (view k perm)
def expected (k : EnvKey) (perm : Bool) : EVM.State :=
  HeaderEnvironmentControls.observed (environmentOp k) perm (UInt256.size+260) accounts spill
    (result k) (9-environmentCost k)
theorem client (k : EnvKey) (perm : Bool) :
    Val.evalT (source k perm) (.simple (.env k rfl) : Val default [] .uint) = .ok (slotWord (result k)) ∧
    Backend.Environment.step (view k perm) (Backend.Environment.select k)
      ((site k perm).state.stack.map slotWord) = some (slotWord (result k)::(site k perm).state.stack.map slotWord) ∧
    Assembly.driverSteps 1 2 #[] (site k perm).state = .ok (expected k perm) ∧
    EVM.X 2 #[] (site k perm).state = EVM.X 1 #[] (expected k perm) ∧
    (expected k perm).toState = (site k perm).state.toState ∧
    (expected k perm).memory = (site k perm).state.memory ∧
    (expected k perm).returnData = (site k perm).state.returnData ∧
    (expected k perm).H_return = (site k perm).state.H_return := by
  have gas : environmentCost k ≤ (site k perm).state.gasAvailable.toNat := by change environmentCost k ≤ 9; cases k <;> decide
  have h := environment_source_agreement (source k perm) frame k (site k perm)
    (Backend.Environment.represented_ok _ _) 0 gas (by change 3 ≤ 1024; decide)
  dsimp only at h
  have value : environmentWord (site k perm).state.toState k = result k := by
    cases k with
    | timestamp => change u (UInt256.size+260)=u 260; decide
    | msgSender | msgValue | selfBalance | selfAddress => rfl
  have shape : (Assembly.chargedPrepare (site k perm).state (environmentCost k)).replaceStackAndIncrPC
      (environmentWord (site k perm).state.toState k::(site k perm).state.stack) = expected k perm := by
    rw [value]
    change ({(site k perm).state with pc := u 3+u 1,gasAvailable := u 9-u (environmentCost k),execLength := 42,stack := result k::spill.map (fun w => UInt256.mk w.toFin)} : EVM.State) = _
    have pc : u 3+u 1=u 4 := by rfl
    have charged : u 9-u (environmentCost k)=u (9-environmentCost k) := by cases k <;> rfl
    rw [pc,charged]
    rfl
  rw [shape,value] at h
  exact h
theorem negative : keys.map (fun k => Backend.Environment.observe (view k false) k) =
    [slotWord (u 11),slotWord (u 37),slotWord (u 260),slotWord (u 29),slotWord (u 7)] ∧
    (expected .msgSender false).stack ≠ [u 19,u 258,u 513] ∧
    (expected .selfAddress true).stack ≠ [u 11,u 258,u 513] ∧
    (expected .timestamp false).stack ≠ [u 260,u 513,u 258] ∧
    Backend.Environment.observe frame .selfBalance ≠ Backend.Environment.observe (view .selfBalance false) .selfBalance := by decide
theorem complete_ordered_observation (perm : Bool) :
    (expected .timestamp perm).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x42,0x00] ∧
    (expected .timestamp perm).executionEnv.header.timestamp = UInt256.size+260 ∧
    (expected .timestamp perm).stack = [u 260,u 258,u 513] ∧
    (expected .timestamp perm).pc = u 4 ∧
    (expected .timestamp perm).gasAvailable = u 7 ∧
    (expected .selfBalance perm).gasAvailable = u 4 ∧
    (expected .timestamp perm).execLength = 42 ∧
    (expected .timestamp perm).memory.data.toList = [0xaa,0xbb]++List.replicate 30 0 ∧
    (expected .timestamp perm).returnData.data.toList = [0xcc,0xdd] ∧
    (expected .timestamp perm).H_return.data.toList = [0xee,0xff] ∧
    (expected .timestamp perm).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (expected .timestamp perm).accountMap = accounts ∧
    (expected .timestamp perm).σ₀ = accounts := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
#print axioms client
#print axioms negative
#print axioms complete_ordered_observation
end EnvironmentSelectionControls
end SolidityBridge.RoadmapV15.P10
