import SolidityBridge.RoadmapV15.P10.ExponentConsumer

/-! Composition of the existing counted charged driver, not a new execution
relation or a claim that terminal opcodes continue in actual X. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem fetched_steps_append (n m fuel : Nat) (valid : Array UInt256) (s : EVM.State) :
    Assembly.driverSteps (n+m) (fuel+n+1) valid s =
      (Assembly.driverSteps n (fuel+n+1) valid s).bind
        (fun next => Assembly.driverSteps m (fuel+1) valid next) := by
  induction n generalizing s with
  | zero => simp only [Nat.zero_add,Nat.add_zero,Assembly.driverSteps,Except.bind]
  | succ n ih =>
    rw [Nat.succ_add]
    have total : fuel+(n+1)+1 = fuel+n+2 := by omega
    rw [total,fetched_steps_cons (n+m) (fuel+n),fetched_steps_cons n (fuel+n)]
    cases step : Assembly.driverSteps 1 (fuel+n+2) valid s with
    | error e => rfl
    | ok next => exact ih next

#print axioms fetched_steps_append
end SolidityBridge.RoadmapV15.P10
