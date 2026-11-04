import SolidityBridge.RoadmapV15.P10.EnvironmentGuards
import SolidityBridge.RoadmapV15.P10.EnvironmentSelectionControls

/-! All-key/both-permission native resource clients at legal input bounds.
Independent complete States and exact ordered bytes do not prove reached source
entry, consensus header admission or rollback from an error without a State. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
namespace EnvironmentGuardControls
open WordPushFixtures (u accounts spill)
open EnvironmentSelectionControls (result)
def words (n : Nat) : Scalar.Stack := spill++List.replicate n 777
def site (k : EnvKey) (gas : Nat) (perm : Bool) (n : Nat) : Site (environmentOp k) :=
  HeaderEnvironmentControls.entry (environmentOp k) gas perm 260 accounts (words n)
def expected (k : EnvKey) (perm : Bool) : EVM.State :=
  HeaderEnvironmentControls.observed (environmentOp k) perm 260 accounts (words 1021) (result k) (9-environmentCost k)
theorem refusal_client (k : EnvKey) (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (site k 1 perm 1022).state = .error .OutOfGass ∧
    EVM.X 2 #[] (site k 1 perm 1022).state = .error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (site k 9 perm 1022).state = .error .StackOverflow ∧
    EVM.X 2 #[] (site k 9 perm 1022).state = .error .StackOverflow := by
  have low : (site k 1 perm 1022).state.gasAvailable.toNat < environmentCost k := by
    change 1 < environmentCost k; cases k <;> decide
  have enough : environmentCost k ≤ (site k 9 perm 1022).state.gasAvailable.toNat := by
    change environmentCost k ≤ 9; cases k <;> decide
  have full : 1024 < (site k 9 perm 1022).state.stack.length+1 := by
    change 1024 < ((spill++List.replicate 1022 777).map (fun (w : Scalar.Word) => UInt256.mk w.toFin)).length+1
    simp only [List.length_map,List.length_append,List.length_replicate]; decide
  have a := environment_driver_result k (site k 1 perm 1022) 0
  have b := environment_driver_result k (site k 9 perm 1022) 0
  simp only [if_pos low] at a
  simp only [if_neg (Nat.not_lt_of_ge enough),if_pos full] at b
  exact ⟨a,(environment_x_refusals k _ 0).1 low,b,(environment_x_refusals k _ 0).2 enough full⟩
theorem short_fuel_client (k : EnvKey) (perm : Bool) :
    Assembly.driverSteps 1 1 #[] (site k 1 perm 1022).state = .error .OutOfFuel ∧
    EVM.X 1 #[] (site k 1 perm 1022).state = .error .OutOfGass ∧
    Assembly.driverSteps 1 1 #[] (site k 9 perm 1022).state = .error .OutOfFuel ∧
    EVM.X 1 #[] (site k 9 perm 1022).state = .error .StackOverflow ∧
    EVM.X 1 #[] (site k 9 perm 0).state = .error .OutOfFuel := by
  have low : (site k 1 perm 1022).state.gasAvailable.toNat < environmentCost k := by
    change 1 < environmentCost k; cases k <;> decide
  have enough : ¬(site k 9 perm 1022).state.gasAvailable.toNat < environmentCost k := by
    change ¬9 < environmentCost k; cases k <;> decide
  have enough0 : ¬(site k 9 perm 0).state.gasAvailable.toNat < environmentCost k := by
    change ¬9 < environmentCost k; cases k <;> decide
  have full : 1024 < (site k 9 perm 1022).state.stack.length+1 := by
    change 1024 < ((spill++List.replicate 1022 777).map (fun (w : Scalar.Word) => UInt256.mk w.toFin)).length+1
    simp only [List.length_map,List.length_append,List.length_replicate]; decide
  have room : ¬1024 < (site k 9 perm 0).state.stack.length+1 := by change ¬1024 < 3; decide
  have a := (environment_short_fuel k (site k 1 perm 1022)).2.2.2
  have b := (environment_short_fuel k (site k 9 perm 1022)).2.2.2
  have c := (environment_short_fuel k (site k 9 perm 0)).2.2.2
  simp only [if_pos low] at a
  simp only [if_neg enough,if_pos full] at b
  simp only [if_neg enough0,if_neg room] at c
  exact ⟨rfl,a,rfl,b,c⟩
theorem capacity_client (k : EnvKey) (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (site k 9 perm 1021).state = .ok (expected k perm) ∧
    (expected k perm).toState = (site k 9 perm 1021).state.toState ∧
    (expected k perm).memory = (site k 9 perm 1021).state.memory ∧
    (expected k perm).returnData = (site k 9 perm 1021).state.returnData ∧
    (expected k perm).H_return = (site k 9 perm 1021).state.H_return := by
  have gas : ¬(site k 9 perm 1021).state.gasAvailable.toNat < environmentCost k := by
    change ¬9 < environmentCost k; cases k <;> decide
  have room : ¬1024 < (site k 9 perm 1021).state.stack.length+1 := by
    change ¬1024 < ((spill++List.replicate 1021 777).map (fun (w : Scalar.Word) => UInt256.mk w.toFin)).length+1
    simp only [List.length_map,List.length_append,List.length_replicate]; decide
  have value : environmentWord (site k 9 perm 1021).state.toState k = result k := by cases k <;> rfl
  have shape : (Assembly.chargedPrepare (site k 9 perm 1021).state (environmentCost k)).replaceStackAndIncrPC
      (environmentWord (site k 9 perm 1021).state.toState k::(site k 9 perm 1021).state.stack) = expected k perm := by
    rw [value]
    change ({(site k 9 perm 1021).state with pc := u 3+u 1,gasAvailable := u 9-u (environmentCost k),execLength := 42,stack := result k::(words 1021).map (fun (w : Scalar.Word) => UInt256.mk w.toFin)} : EVM.State) = _
    have pc : u 3+u 1=u 4 := by rfl
    have charged : u 9-u (environmentCost k)=u (9-environmentCost k) := by cases k <;> rfl
    rw [pc,charged]
    rfl
  have h := environment_driver_result k (site k 9 perm 1021) 0
  dsimp only at h
  rw [shape] at h
  simp only [if_neg gas,if_neg room] at h
  exact ⟨h,rfl,rfl,rfl,rfl⟩
theorem complete_ordered_observation (k : EnvKey) (perm : Bool) :
    (expected k perm).stack = result k::(words 1021).map (fun (w : Scalar.Word) => UInt256.mk w.toFin) ∧
    (expected k perm).stack ≠ result k::u 513::u 258::(List.replicate 1021 (777 : Scalar.Word)).map (fun w => UInt256.mk w.toFin) ∧
    (expected k perm).executionEnv.code.data.toList = [0x60,0x7f,0x50,(environmentOp k).code,0x00] ∧
    (expected k perm).memory.data.toList = [0xaa,0xbb]++List.replicate 30 0 ∧
    (expected k perm).returnData.data.toList = [0xcc,0xdd] ∧
    (expected k perm).H_return.data.toList = [0xee,0xff] ∧
    (expected k perm).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (expected k perm).accountMap = accounts ∧
    (expected k perm).σ₀ = accounts ∧
    (expected k perm).pc = u 4 ∧ (expected k perm).execLength = 42 := by
  refine ⟨rfl,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  intro bad
  have different := congrArg (fun xs : List UInt256 => xs[1]?) bad
  change some (u 258) = some (u 513) at different
  exact (by decide : some (u 258) ≠ some (u 513)) different
#print axioms refusal_client
#print axioms short_fuel_client
#print axioms capacity_client
#print axioms complete_ordered_observation
end EnvironmentGuardControls
end SolidityBridge.RoadmapV15.P10
