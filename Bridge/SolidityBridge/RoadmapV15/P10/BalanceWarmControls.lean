import SolidityBridge.RoadmapV15.P10.BalanceWarmTransport

/-! Populated post-BALANCE observations. Probe stack replacement is explicit;
returned funds need not be the original account address. -/
namespace SolidityBridge.RoadmapV15.P10.BalanceWarmControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def u (n : Nat) : UInt256 := .ofNat n
def spill : List UInt256 := [u 258,u 513]
def seed : EVM.State :=
  {(default : EVM.State) with
    gasAvailable := u 2700,execLength := 41,activeWords := u 1
    memory := ⟨#[0xaa,0xbb]⟩,returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7,source := .ofNat 11,sender := .ofNat 19,weiValue := u 3,
      perm := false,calldata := ⟨#[0x11,0x22,0x33]⟩}
    substate := {(default : Substate) with
      refundBalance := u 17
      accessedStorageKeys := (default : Substate).accessedStorageKeys.insert (.ofNat 7,u 13),
      logSeries := #[⟨.ofNat 7,#[u 5,u 7],⟨#[0x44,0x55]⟩⟩]}
    accountMap := ((∅ : AccountMap .EVM).insert (.ofNat 13)
      {(default : Account .EVM) with
        nonce := u 9,balance := u 73
        storage := (∅ : EvmYul.Storage).insert (u 14) (u 4097),
        tstorage := (∅ : EvmYul.Storage).insert (u 14) (u 8193)}).insert (.ofNat 14)
      {(default : Account .EVM) with nonce := u 11,balance := u 99}}
def site : Site .BALANCE := ⟨seed,[],[.op .STOP],by decide⟩
def input : EVM.State := (slotReadSite site (u 13) spill).state
def expected : EVM.State :=
  {input with
    pc := u 1,gasAvailable := u 100,execLength := 42
    stack := [u 73,u 258,u 513],substate := input.substate.addAccessedAccount (.ofNat 13)}
def lowInput : EVM.State :=
  (slotReadSite ({site with seed := {seed with gasAvailable := u 2599}} : Site .BALANCE) (u 13) spill).state

theorem populated :
    Assembly.driverSteps 1 2 #[] input = .ok expected
    := by
  rfl

#print axioms populated

theorem probe_distinctions :
    EVM.C' {expected with stack := UInt256.ofNat 13::spill} .BALANCE = 100 ∧ EVM.C' {expected with stack := UInt256.ofNat (2^160+13)::spill} .BALANCE = 100 ∧ EVM.C' {expected with stack := UInt256.ofNat 14::spill} .BALANCE = 2600 ∧ EVM.C' expected .BALANCE = 2600
    := by
  decide

#print axioms probe_distinctions

theorem resource_and_order_negatives :
    Assembly.driverSteps 1 2 #[] lowInput = .error .OutOfGass ∧ Assembly.driverSteps 1 1 #[] input = .error .OutOfFuel ∧ expected.stack ≠ [UInt256.ofNat 73,UInt256.ofNat 513,UInt256.ofNat 258]
    := by
  refine ⟨rfl,rfl,?_⟩
  decide

#print axioms resource_and_order_negatives

theorem headline_client :
    let frame : Backend.Environment.Frame := balanceFrame {self := Solidity.Backend.Environment.account (slotWord (UInt256.ofNat 7)),sender := Solidity.Backend.Environment.account (slotWord (UInt256.ofNat 19)),value := slotWord (UInt256.ofNat 3),time := slotWord (UInt256.ofNat input.executionEnv.header.timestamp),funds := fun _ => slotWord (UInt256.ofNat 0)} input.toState; Assembly.driverSteps 1 2 #[] input = .ok expected ∧ EVM.X 2 #[] input = EVM.X 1 #[] expected ∧ EVM.C' {expected with stack := UInt256.ofNat 13::spill} .BALANCE = 100 ∧ balanceFrame frame expected.toState = balanceFrame frame input.toState ∧ expected.accountMap = input.accountMap ∧ expected.memory = input.memory ∧ expected.returnData = input.returnData ∧ expected.H_return = input.H_return
    := by
  let f : Backend.Environment.Frame := balanceFrame {self := Solidity.Backend.Environment.account (slotWord (UInt256.ofNat 7)),sender := Solidity.Backend.Environment.account (slotWord (UInt256.ofNat 19)),value := slotWord (UInt256.ofNat 3),time := slotWord (UInt256.ofNat input.executionEnv.header.timestamp),funds := fun _ => slotWord (UInt256.ofNat 0)} input.toState
  exact balance_resource_frame f site (UInt256.ofNat 13) spill (by decide) (by decide) 0

#print axioms headline_client

theorem alias_client :
    EVM.C' {expected with stack := UInt256.ofNat (2^160+13)::spill} .BALANCE = 100
    := by
  exact balance_alias_probe_cost input (UInt256.ofNat 13) (UInt256.ofNat (2^160+13)) spill (by decide)

#print axioms alias_client

end SolidityBridge.RoadmapV15.P10.BalanceWarmControls
