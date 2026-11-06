import SolidityBridge.RoadmapV15.P10.StorageReadConsumer
import Batteries.Data.RBMap.Lemmas
/-! Resource and persistent/transient frame consumers of actual SLOAD.
The next-cost observation explicitly reinstalls the same key; it does not claim
that an arbitrary following opcode or returned value supplies that key. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
private theorem keys_transitive : Std.TransCmp Substate.storageKeysCmp := by
  have cmp : Substate.storageKeysCmp = compareLex
      (compareOn (fun p : AccountAddress × UInt256 => p.1.val))
      (compareOn (fun p : AccountAddress × UInt256 => p.2.val.val)) := by
    funext a b
    change (compare a.1.val b.1.val).then ((compare a.2.val.val b.2.val.val).then .eq) =
      (compare a.1.val b.1.val).then (compare a.2.val.val b.2.val.val)
    rw [Ordering.then_eq]
  rw [cmp]
  infer_instance
theorem sload_warm_cost (s : EVM.State) (key : UInt256) (tail : List UInt256) (cost : Nat) :
    let next := ({Assembly.chargedPrepare s cost with toState := (EvmYul.State.sload s.toState key).1}).replaceStackAndIncrPC ((EvmYul.State.sload s.toState key).2::tail)
    EVM.C' {next with stack := key::tail} .SLOAD = 100 := by
  letI : Std.TransCmp Substate.storageKeysCmp := keys_transitive
  have warmed : (s.substate.accessedStorageKeys.insert (s.executionEnv.codeOwner,key)).contains (s.executionEnv.codeOwner,key) = true :=
    Batteries.RBSet.contains_iff.mpr (Batteries.RBSet.mem_insert_self _ _)
  change (if (s.substate.accessedStorageKeys.insert (s.executionEnv.codeOwner,key)).contains (s.executionEnv.codeOwner,key) then 100 else 2100) = 100
  rw [warmed]
  rfl

theorem tload_retains_sload_cost (s : EVM.State) (key : UInt256) (tail : List UInt256) (cost : Nat) :
    let next := ({Assembly.chargedPrepare s cost with toState := (EvmYul.State.tload s.toState key).1}).replaceStackAndIncrPC ((EvmYul.State.tload s.toState key).2::tail)
    EVM.C' {next with stack := key::tail} .SLOAD = EVM.C' {s with stack := key::tail} .SLOAD := by
  rfl
theorem sload_resource_frame (site : Site .SLOAD) (key other : UInt256) (tail : List UInt256)
    (room : tail.length+1 ≤ 1024)
    (gas : EVM.C' (slotReadSite site key tail).state .SLOAD ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (slotReadSite site key tail).state
    let cost := EVM.C' input .SLOAD
    let read := EvmYul.State.sload input.toState key
    let next := ({Assembly.chargedPrepare input cost with toState := read.1}).replaceStackAndIncrPC (read.2::tail)
    Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
    EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next ∧
    EVM.C' {next with stack := key::tail} .SLOAD = 100 ∧
    Solidity.Evm.StorageSlots.storageRead next.toState = Solidity.Evm.StorageSlots.storageRead input.toState ∧
    (EvmYul.State.tload next.toState other).2 = (EvmYul.State.tload input.toState other).2 := by
  dsimp only
  have actual := sload_agreement site key tail room gas fuel
  refine ⟨actual.1,actual.2,sload_warm_cost _ _ _ _,?_,rfl⟩
  exact Solidity.Evm.StorageSlots.sload_preserves _ key

/-- Equality of actual numeric owner/key pairs, not a hash-model assumption. -/
theorem storage_keys_compare_eq (a b : AccountAddress × UInt256) :
    Substate.storageKeysCmp a b = .eq ↔ a = b := by
  rcases a with ⟨ao,⟨ak⟩⟩
  rcases b with ⟨bo,⟨bk⟩⟩
  change (compare ao.val bo.val).then ((compare ak.val bk.val).then .eq) = .eq ↔
    (ao,UInt256.mk ak) = (bo,UInt256.mk bk)
  simp only [Ordering.then_eq_eq,Nat.compare_eq_eq,Prod.mk.injEq,UInt256.mk.injEq,Fin.ext_iff,and_true]

/-- An actual SLOAD changes no other owner/key's persistent-read charge.
Both probes explicitly install the same owner/key; no following execution is assumed. -/
theorem sload_distinct_cost (s : EVM.State) (key probe : UInt256) (owner : AccountAddress)
    (tail : List UInt256) (cost : Nat) (apart : (owner,probe) ≠ (s.executionEnv.codeOwner,key)) :
    let next := ({Assembly.chargedPrepare s cost with toState := (EvmYul.State.sload s.toState key).1}).replaceStackAndIncrPC ((EvmYul.State.sload s.toState key).2::tail)
    EVM.C' {next with stack := probe::tail,executionEnv := {next.executionEnv with codeOwner := owner}} .SLOAD =
      EVM.C' {s with stack := probe::tail,executionEnv := {s.executionEnv with codeOwner := owner}} .SLOAD := by
  letI : Std.TransCmp Substate.storageKeysCmp := keys_transitive
  have separated : Substate.storageKeysCmp (s.executionEnv.codeOwner,key) (owner,probe) ≠ .eq := by
    intro equal
    exact apart ((storage_keys_compare_eq _ _).mp equal).symm
  have unchanged : (s.substate.accessedStorageKeys.insert (s.executionEnv.codeOwner,key)).contains (owner,probe) =
      s.substate.accessedStorageKeys.contains (owner,probe) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Batteries.RBSet.contains_iff,Batteries.RBSet.mem_insert,separated,or_false]
  change (if (s.substate.accessedStorageKeys.insert (s.executionEnv.codeOwner,key)).contains (owner,probe) then 100 else 2100) =
    (if s.substate.accessedStorageKeys.contains (owner,probe) then 100 else 2100)
  rw [unchanged]

#print axioms storage_keys_compare_eq
#print axioms sload_distinct_cost
#print axioms sload_warm_cost
#print axioms tload_retains_sload_cost
#print axioms sload_resource_frame
end SolidityBridge.RoadmapV15.P10
