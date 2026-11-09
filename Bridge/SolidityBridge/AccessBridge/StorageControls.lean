import SolidityBridge.AccessBridge.Storage

/-! Regressions: charged reads/writes retain unequal account payloads and an
older stack tail; absent accounts are not silently created; gas, stack,
static-mode and stipend failures keep their actual ordering. These are native
opcode controls, not symbolic compiler-storage or transaction lifecycle proofs. -/
namespace SolidityBridge.AccessBridge.StorageControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open SolidityBridge.RoadmapV15
private def u (n : Nat) : UInt256 := .ofNat n
private def owner : AccountAddress := (default : EVM.State).executionEnv.codeOwner
private def account : Account .EVM :=
  {(default : Account .EVM) with
    storage := (default : EvmYul.Storage).insert (u 3) (u 7)
    tstorage := (default : EvmYul.Storage).insert (u 5) (u 11)}
private def tail : List UInt256 := [u 258,u 513]
private def site (op : Backend.Op) (gas : Nat) (perm present : Bool)
    (stack : List UInt256) : P10.Site op where
  seed := {(default : EVM.State) with
    gasAvailable := u gas
    execLength := 41
    stack := stack
    executionEnv := {(default : EVM.State).executionEnv with perm := perm}
    accountMap := if present then (default : AccountMap .EVM).insert owner account else default}
  before := []
  after := []
  pcFits := by decide
private def observe (state : EVM.State) : Option (UInt256 × UInt256) × List UInt256 :=
  ((state.toState.lookupAccount owner).map fun acc =>
    (acc.storage.findD (u 3) (u 0),acc.tstorage.findD (u 5) (u 0)),state.stack)

theorem inhabited : Nonempty StorageAccessCertificate := ⟨Storage.certificate⟩

theorem read_persistent :
    (Assembly.driverSteps 1 2 #[] (site .SLOAD 2100 true true (u 3::tail)).state).map
      (fun state => state.stack)=.ok (u 7::tail) := by
  rw [Storage.read_charged .SLOAD (by simp only [List.mem_cons,List.not_mem_nil,or_false,true_or])]
  simp only [ite_true]
  rfl

theorem read_transient :
    (Assembly.driverSteps 1 2 #[] (site .TLOAD 100 true true (u 5::tail)).state).map
      (fun state => state.stack)=.ok (u 11::tail) := by
  rw [Storage.read_charged .TLOAD (by simp only [List.mem_cons,List.not_mem_nil,or_false,or_true])]
  simp only [reduceCtorEq,ite_false]
  rfl

theorem write_persistent :
    (Assembly.driverSteps 1 2 #[] (site .SSTORE 50000 true true (u 3::u 42::tail)).state).map
      observe=.ok (some (u 42,u 11),tail) := by
  rw [Storage.write_charged .SSTORE (by simp only [List.mem_cons,List.not_mem_nil,or_false,true_or])]
  simp only [ite_true]
  rfl

theorem write_transient :
    (Assembly.driverSteps 1 2 #[] (site .TSTORE 100 true true (u 5::u 99::tail)).state).map
      observe=.ok (some (u 7,u 99),tail) := by
  rw [Storage.write_charged .TSTORE (by simp only [List.mem_cons,List.not_mem_nil,or_false,or_true])]
  simp only [reduceCtorEq,ite_false]
  rfl

theorem absent_account_preserved :
    (Assembly.driverSteps 1 2 #[] (site .SSTORE 50000 true false (u 3::u 42::tail)).state).map
      observe=.ok (none,tail) := by
  rw [Storage.write_charged .SSTORE (by simp only [List.mem_cons,List.not_mem_nil,or_false,true_or])]
  simp only [ite_true]
  rfl

theorem static_rejected :
    Assembly.driverSteps 1 2 #[] (site .TSTORE 1000 false true (u 5::u 99::tail)).state=
      .error .StaticModeViolation := by
  rw [Storage.write_charged .TSTORE (by simp only [List.mem_cons,List.not_mem_nil,or_false,or_true])]
  simp only [reduceCtorEq,ite_false]
  rfl

theorem gas_before_stack :
    Assembly.driverSteps 1 2 #[] (site .TLOAD 0 true true []).state=.error .OutOfGass := by
  rw [Storage.read_charged .TLOAD (by simp only [List.mem_cons,List.not_mem_nil,or_false,or_true])]
  simp only [reduceCtorEq,ite_false]
  rfl

theorem stack_before_static :
    Assembly.driverSteps 1 2 #[] (site .TSTORE 1000 false true []).state=.error .StackUnderflow := by
  rw [Storage.write_charged .TSTORE (by simp only [List.mem_cons,List.not_mem_nil,or_false,or_true])]
  simp only [reduceCtorEq,ite_false]
  rfl

theorem stipend_rejected :
    Assembly.driverSteps 1 2 #[] (site .SSTORE 2300 true true (u 3::u 7::tail)).state=
      .error .OutOfGass := by
  rw [Storage.write_charged .SSTORE (by simp only [List.mem_cons,List.not_mem_nil,or_false,true_or])]
  simp only [ite_true]
  rfl

theorem cold_read_charge :
    (Assembly.driverSteps 1 2 #[] (site .SLOAD 2100 true true (u 3::tail)).state).map
      (fun state => (state.gasAvailable.toNat,state.execLength,state.pc.toNat,state.stack))=
        .ok (0,42,1,u 7::tail) := by
  rw [Storage.read_charged .SLOAD (by simp only [List.mem_cons,List.not_mem_nil,or_false,true_or])]
  simp only [ite_true]
  rfl

theorem transient_read_charge :
    (Assembly.driverSteps 1 2 #[] (site .TLOAD 100 true true (u 5::tail)).state).map
      (fun state => (state.gasAvailable.toNat,state.execLength,state.pc.toNat,state.stack))=
        .ok (0,42,1,u 11::tail) := by
  rw [Storage.read_charged .TLOAD (by simp only [List.mem_cons,List.not_mem_nil,or_false,or_true])]
  simp only [reduceCtorEq,ite_false]
  rfl

theorem low_fuel (op : Backend.Op) :
    Assembly.driverSteps 1 0 #[] (site op 0 false false []).state=.error .OutOfFuel ∧
    Assembly.driverSteps 1 1 #[] (site op 0 false false []).state=.error .OutOfFuel := ⟨rfl,rfl⟩

/-- info: 'SolidityBridge.AccessBridge.StorageControls.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inhabited
/-- info: 'SolidityBridge.AccessBridge.StorageControls.read_persistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_persistent
/-- info: 'SolidityBridge.AccessBridge.StorageControls.read_transient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_transient
/-- info: 'SolidityBridge.AccessBridge.StorageControls.write_persistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms write_persistent
/-- info: 'SolidityBridge.AccessBridge.StorageControls.write_transient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms write_transient
/-- info: 'SolidityBridge.AccessBridge.StorageControls.absent_account_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms absent_account_preserved
/-- info: 'SolidityBridge.AccessBridge.StorageControls.static_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms static_rejected
/-- info: 'SolidityBridge.AccessBridge.StorageControls.gas_before_stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gas_before_stack
/-- info: 'SolidityBridge.AccessBridge.StorageControls.stack_before_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stack_before_static
/-- info: 'SolidityBridge.AccessBridge.StorageControls.stipend_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stipend_rejected
/-- info: 'SolidityBridge.AccessBridge.StorageControls.cold_read_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cold_read_charge
/-- info: 'SolidityBridge.AccessBridge.StorageControls.transient_read_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transient_read_charge
/-- info: 'SolidityBridge.AccessBridge.StorageControls.low_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms low_fuel

end SolidityBridge.AccessBridge.StorageControls
