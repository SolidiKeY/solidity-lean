import SolidityBridge.RoadmapV15.P10.BalanceEnvironmentConsumer
import SolidityBridge.RoadmapV15.P10.HeaderEnvironment

/-! Canonical code-owner ledger observations for SELFBALANCE. The view derives
self and funds from the actual native state; source/world origin remains open. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem native_address_word_roundtrip (a : AccountAddress) :
    AccountAddress.ofUInt256 (UInt256.ofNat a.val) = a := by
  apply Fin.ext
  have wide : a.val < UInt256.size := Nat.lt_trans a.isLt (by decide)
  change ((a.val % UInt256.size) % AccountAddress.size) % AccountAddress.size = a.val
  simp only [Nat.mod_eq_of_lt wide,Nat.mod_eq_of_lt a.isLt]

def selfBalanceFrame (frame : Backend.Environment.Frame) (s : EvmYul.State .EVM) :
    Backend.Environment.Frame :=
  {balanceFrame frame s with self := Backend.Environment.account (slotWord (UInt256.ofNat s.executionEnv.codeOwner.val))}

theorem selfbalance_source_step :
    ∀ (frame : Backend.Environment.Frame) (s : EvmYul.State .EVM) (tail : List UInt256), Backend.Environment.step (selfBalanceFrame frame s) (.op .SELFBALANCE) (tail.map slotWord) = some (slotWord (EvmYul.State.selfbalance s)::tail.map slotWord)
    := by
  intro frame s tail
  simp only [Backend.Environment.step,selfBalanceFrame,balanceFrame]
  rw [balance_address,native_address_word_roundtrip]
  rfl

#print axioms selfbalance_source_step

theorem selfbalance_agreement :
    ∀ (frame : Backend.Environment.Frame) (site : Site .SELFBALANCE) (fuel : Nat) (_gas : 5 ≤ site.state.gasAvailable.toNat) (_room : site.state.stack.length+1 ≤ 1024),
     let next := (Assembly.chargedPrepare site.state 5).replaceStackAndIncrPC (EvmYul.State.selfbalance site.state.toState::site.state.stack)
     Backend.Environment.step (selfBalanceFrame frame site.state.toState) (Backend.Environment.select .selfBalance) (site.state.stack.map slotWord) = some (slotWord (EvmYul.State.selfbalance site.state.toState)::site.state.stack.map slotWord) ∧ Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧ EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next ∧ next.toState = site.state.toState ∧ next.memory = site.state.memory ∧ next.returnData = site.state.returnData ∧ next.H_return = site.state.H_return
    := by
  intro frame site fuel gas room
  dsimp only
  have h := selfbalance_fetched site fuel gas room
  dsimp only at h
  refine ⟨?_,h.1,h.2,rfl,rfl,rfl,rfl⟩
  simp only [Backend.Environment.select,Backend.Environment.step,selfBalanceFrame,balanceFrame]
  rw [balance_address,native_address_word_roundtrip]
  rfl

#print axioms selfbalance_agreement

#print axioms native_address_word_roundtrip
end SolidityBridge.RoadmapV15.P10
