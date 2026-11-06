import SolidityBridge.RoadmapV15.P10.SelfBalanceTransport
import SolidityBridge.RoadmapV15.P10.InvocationEnvironment

/-! A canonical G31 observation view from actual native fields. Represents is
an explicit source-state premise, not a supplied frame-origin proof. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def environmentOp : EnvKey → Backend.Op
  | .msgSender => .CALLER
  | .msgValue => .CALLVALUE
  | .timestamp => .TIMESTAMP
  | .selfBalance => .SELFBALANCE
  | .selfAddress => .ADDRESS

def environmentCost : EnvKey → Nat
  | .selfBalance => 5
  | _ => 2

def environmentWord (s : EvmYul.State .EVM) : EnvKey → UInt256
  | .msgSender => UInt256.ofNat s.executionEnv.source.val
  | .msgValue => s.executionEnv.weiValue
  | .timestamp => UInt256.ofNat s.executionEnv.header.timestamp
  | .selfBalance => EvmYul.State.selfbalance s
  | .selfAddress => UInt256.ofNat s.executionEnv.codeOwner.val

def nativeEnvironmentFrame (frame : Backend.Environment.Frame) (s : EvmYul.State .EVM) :
    Backend.Environment.Frame :=
  {selfBalanceFrame frame s with
    sender := Backend.Environment.account (slotWord (UInt256.ofNat s.executionEnv.source.val))
    value := slotWord s.executionEnv.weiValue
    time := slotWord (UInt256.ofNat s.executionEnv.header.timestamp)}

theorem native_address_observation (a : AccountAddress) :
    (Backend.Environment.account (slotWord (UInt256.ofNat a.val))).1 =
      slotWord (UInt256.ofNat a.val) := by
  apply Subtype.ext
  have wide : a.val < UInt256.size := Nat.lt_trans a.isLt (by decide)
  have narrow : a.val < 2^160 := a.isLt
  change (((a.val % UInt256.size) % 2^160 : Nat) : Int) = ((a.val % UInt256.size : Nat) : Int)
  simp only [Nat.mod_eq_of_lt wide,Nat.mod_eq_of_lt narrow]

#print axioms native_address_observation
theorem native_environment_observation (frame : Backend.Environment.Frame) (s : EvmYul.State .EVM) (k : EnvKey) :
    Backend.Environment.observe (nativeEnvironmentFrame frame s) k = slotWord (environmentWord s k) := by
  cases k with
  | selfBalance =>
    change (selfBalanceFrame frame s).funds (selfBalanceFrame frame s).self = slotWord (EvmYul.State.selfbalance s)
    simp only [selfBalanceFrame,balanceFrame]
    rw [balance_address,native_address_word_roundtrip]
    rfl
  | msgSender => exact native_address_observation _
  | msgValue => rfl
  | timestamp => rfl
  | selfAddress => exact native_address_observation _
theorem environment_fetched (k : EnvKey) (site : Site (environmentOp k)) (fuel : Nat)
    (gas : environmentCost k ≤ site.state.gasAvailable.toNat)
    (room : site.state.stack.length+1 ≤ 1024) :
    let next := (Assembly.chargedPrepare site.state (environmentCost k)).replaceStackAndIncrPC
      (environmentWord site.state.toState k::site.state.stack)
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
      EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  cases k with
  | msgSender => exact caller_fetched site fuel gas room
  | msgValue => exact callvalue_fetched site fuel gas room
  | timestamp => exact timestamp_fetched site fuel gas room
  | selfBalance => exact selfbalance_fetched site fuel gas room
  | selfAddress => exact address_fetched site fuel gas room

#print axioms native_environment_observation
#print axioms environment_fetched
theorem environment_source_agreement {C : Contract} {Γ : Ctx} (σ : Solidity.State C Γ)
    (frame : Backend.Environment.Frame) (k : EnvKey) (site : Site (environmentOp k))
    (repr : Backend.Environment.Represents (nativeEnvironmentFrame frame site.state.toState) σ)
    (fuel : Nat) (gas : environmentCost k ≤ site.state.gasAvailable.toNat)
    (room : site.state.stack.length+1 ≤ 1024) :
    let next := (Assembly.chargedPrepare site.state (environmentCost k)).replaceStackAndIncrPC
      (environmentWord site.state.toState k::site.state.stack)
    Val.evalT σ (.simple (.env k rfl) : Val C Γ .uint) = .ok (slotWord (environmentWord site.state.toState k)) ∧
    Backend.Environment.step (nativeEnvironmentFrame frame site.state.toState) (Backend.Environment.select k)
      (site.state.stack.map slotWord) = some (slotWord (environmentWord site.state.toState k)::site.state.stack.map slotWord) ∧
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
    EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next ∧
    next.toState = site.state.toState ∧ next.memory = site.state.memory ∧
    next.returnData = site.state.returnData ∧ next.H_return = site.state.H_return := by
  have source := Backend.Environment.intrinsic_correct repr k (site.state.stack.map slotWord)
  rw [native_environment_observation] at source
  have fetched := environment_fetched k site fuel gas room
  exact ⟨source.1,source.2,fetched.1,fetched.2,rfl,rfl,rfl,rfl⟩

#print axioms environment_source_agreement
end SolidityBridge.RoadmapV15.P10
