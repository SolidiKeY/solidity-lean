import SolidityBridge.RoadmapV15.P10.StorageReadConsumer
import SolidityBridge.RoadmapV15.P10.ExponentConsumer

/-! Populated persistent/transient, warming and source-representation clients.
All positive execution claims retain complete State, not just loaded values. -/
namespace SolidityBridge.RoadmapV15.P10.StorageReadControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
private def u (n : Nat) : UInt256 := .ofNat n
private def spill : List UInt256 := [u 258,u 513]
private def owner : AccountAddress := .ofNat 7
private def account : Account .EVM :=
  {(default : Account .EVM) with
    nonce := u 3,balance := u 29
    storage := (((∅ : EvmYul.Storage).insert (u 13) (u 513)).insert (u 14) (u 17)).insert
      (u 15) (u (2^256-1)) |>.insert (u 16) (u 1)
    tstorage := (∅ : EvmYul.Storage).insert (u 13) (u 1025)}
private def other : Account .EVM :=
  {(default : Account .EVM) with
    nonce := u 5,balance := u 41
    storage := (∅ : EvmYul.Storage).insert (u 13) (u 4097)
    tstorage := (∅ : EvmYul.Storage).insert (u 13) (u 8193)}
private def seed (gas : Nat) (warm perm : Bool) : EVM.State :=
  {(default : EVM.State) with
    execLength := 41,gasAvailable := u gas,activeWords := u 1
    memory := ⟨#[0xaa,0xbb]⟩,returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := owner,source := .ofNat 11,sender := .ofNat 19,perm := perm
      calldata := ⟨#[0x11,0x22,0x33]⟩}
    substate := if warm then (default : Substate).addAccessedStorageKey (owner,u 13) else default
    accountMap := ((∅ : AccountMap .EVM).insert owner account).insert (.ofNat 11) other}
private def base (op : Backend.Op) (gas : Nat) (warm perm : Bool) : Site op :=
  ⟨seed gas warm perm,[.push ⟨1,by decide⟩ #v[0x54],.op .POP],[.op .STOP],by decide⟩
private def image (op : Backend.Op) (gas : Nat) (warm perm : Bool) (key : UInt256) (tail : List UInt256) : Site op :=
  slotReadSite (base op gas warm perm) key tail
private def persistentExpected (input : Site .SLOAD) (key value : UInt256) (tail : List UInt256) : EVM.State :=
  {input.state with
    pc := u 4,gasAvailable := u 0,execLength := 42,stack := value::tail
    substate := input.state.substate.addAccessedStorageKey (input.state.executionEnv.codeOwner,key)}
private def transientExpected (input : Site .TLOAD) (value : UInt256) (tail : List UInt256) : EVM.State :=
  {input.state with pc := u 4,gasAvailable := u 0,execLength := 42,stack := value::tail}

private theorem seed_gas (budget : Nat) (warm perm : Bool) :
    (seed budget warm perm).gasAvailable = u budget := rfl
private theorem seed_length (budget : Nat) (warm perm : Bool) :
    (seed budget warm perm).execLength = 41 := rfl

private theorem execute_sload (budget : Nat) (warm perm : Bool) (key value : UInt256) (tail : List UInt256)
    (fits : budget < UInt256.size) (room : tail.length+1 ≤ 1024)
    (cost : EVM.C' (image .SLOAD budget warm perm key tail).state .SLOAD = budget)
    (read : (EvmYul.State.sload (image .SLOAD budget warm perm key tail).state.toState key).2 = value) :
    Assembly.driverSteps 1 2 #[] (image .SLOAD budget warm perm key tail).state =
      .ok (persistentExpected (image .SLOAD budget warm perm key tail) key value tail) := by
  have actualCost : EVM.C' (slotReadSite (base .SLOAD budget warm perm) key tail).state .SLOAD = budget := cost
  have gas : EVM.C' (slotReadSite (base .SLOAD budget warm perm) key tail).state .SLOAD ≤
      (base .SLOAD budget warm perm).seed.gasAvailable.toNat := by
    rw [actualCost]
    change budget ≤ budget % UInt256.size
    rw [Nat.mod_eq_of_lt fits]
  have h := (sload_agreement (base .SLOAD budget warm perm) key tail room gas 0).1
  dsimp only at h
  change (EvmYul.State.sload (slotReadSite (base .SLOAD budget warm perm) key tail).state.toState key).2 = value at read
  rw [actualCost,sload_read_shape,read] at h
  have zero : UInt256.ofNat budget-UInt256.ofNat budget = UInt256.ofNat 0 := by
    change UInt256.mk ((UInt256.ofNat budget).val-(UInt256.ofNat budget).val) = _
    rw [sub_self]
    rfl
  simpa only [image,persistentExpected,slotReadSite,Site.state,base,seed_gas,seed_length,u,zero] using h

private theorem execute_tload (warm perm : Bool) (key value : UInt256) (tail : List UInt256)
    (room : tail.length+1 ≤ 1024)
    (read : (EvmYul.State.tload (image .TLOAD 100 warm perm key tail).state.toState key).2 = value) :
    Assembly.driverSteps 1 2 #[] (image .TLOAD 100 warm perm key tail).state =
      .ok (transientExpected (image .TLOAD 100 warm perm key tail) value tail) := by
  have h := (tload_agreement (base .TLOAD 100 warm perm) key tail room (by change 100 ≤ 100;decide) 0).1
  dsimp only at h
  have cost : EVM.C' (slotReadSite (base .TLOAD 100 warm perm) key tail).state .TLOAD = 100 := rfl
  change (EvmYul.State.tload (slotReadSite (base .TLOAD 100 warm perm) key tail).state.toState key).2 = value at read
  rw [cost,tload_read_shape,read] at h
  simpa only [image,transientExpected,slotReadSite,Site.state,base,seed_gas,seed_length,u] using h

theorem cold_persistent :
    Assembly.driverSteps 1 2 #[] (image .SLOAD 2100 false false (u 13) spill).state =
      .ok (persistentExpected (image .SLOAD 2100 false false (u 13) spill) (u 13) (u 513) spill) := by
  exact execute_sload _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem warm_persistent :
    Assembly.driverSteps 1 2 #[] (image .SLOAD 100 true false (u 13) spill).state =
      .ok (persistentExpected (image .SLOAD 100 true false (u 13) spill) (u 13) (u 513) spill) := by
  exact execute_sload _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem neighbor_slot :
    Assembly.driverSteps 1 2 #[] (image .SLOAD 2100 false false (u 14) spill).state =
      .ok (persistentExpected (image .SLOAD 2100 false false (u 14) spill) (u 14) (u 17) spill) := by
  exact execute_sload _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem unset_slot :
    Assembly.driverSteps 1 2 #[] (image .SLOAD 2100 false false (u 99) spill).state =
      .ok (persistentExpected (image .SLOAD 2100 false false (u 99) spill) (u 99) (u 0) spill) := by
  exact execute_sload _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem wrapped_root :
    Assembly.driverSteps 1 2 #[] (image .SLOAD 2100 false false (u (2^256+13)) spill).state =
      .ok (persistentExpected (image .SLOAD 2100 false false (u (2^256+13)) spill) (u (2^256+13)) (u 513) spill) := by
  exact execute_sload _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl

theorem transient_separate :
    Assembly.driverSteps 1 2 #[] (image .TLOAD 100 false false (u 13) spill).state =
      .ok (transientExpected (image .TLOAD 100 false false (u 13) spill) (u 1025) spill) := by
  exact execute_tload _ _ _ _ _ (by decide +kernel) rfl

theorem writable_reads :
    Assembly.driverSteps 1 2 #[] (image .SLOAD 2100 false true (u 13) spill).state =
      .ok (persistentExpected (image .SLOAD 2100 false true (u 13) spill) (u 13) (u 513) spill) ∧
    Assembly.driverSteps 1 2 #[] (image .TLOAD 100 false true (u 13) spill).state =
      .ok (transientExpected (image .TLOAD 100 false true (u 13) spill) (u 1025) spill) := by
  exact ⟨execute_sload _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl rfl,
    execute_tload _ _ _ _ _ (by decide +kernel) rfl⟩

theorem stack_boundary :
    Assembly.driverSteps 1 2 #[] (image .SLOAD 2100 false false (u 13) (List.replicate 1023 (u 513))).state =
      .ok (persistentExpected (image .SLOAD 2100 false false (u 13) (List.replicate 1023 (u 513)))
        (u 13) (u 513) (List.replicate 1023 (u 513))) := by
  apply execute_sload
  · decide +kernel
  · simp only [List.length_replicate];decide
  · rfl
  · rfl

private def absent : Site .SLOAD :=
  slotReadSite {base .SLOAD 2100 false false with seed := {(seed 2100 false false) with accountMap := ∅}} (u 13) spill

theorem absent_account_zero :
    Assembly.driverSteps 1 2 #[] absent.state =
      .ok (persistentExpected absent (u 13) (u 0) spill) := by rfl

private def sequence (budget : Nat) (warm : Bool) : Site .SLOAD :=
  slotReadSite ⟨seed budget warm false,[.push ⟨1,by decide⟩ #v[0x54],.op .POP],
    [.push ⟨1,by decide⟩ #v[0x0d],.op .SLOAD,.op .STOP],by decide⟩ (u 13) spill
private def sequenceExpected (budget : Nat) (warm : Bool) : EVM.State :=
  {(sequence budget warm).state with
    pc := u 7,gasAvailable := u 0,execLength := 44,stack := u 513::u 513::spill
    substate := ((sequence budget warm).state.substate.addAccessedStorageKey (owner,u 13)).addAccessedStorageKey (owner,u 13)}

private def firstSequenceExpected (budget : Nat) (warm : Bool) : EVM.State :=
  {(sequence budget warm).state with
    pc := u 4,gasAvailable := u 103,execLength := 42,stack := u 513::spill
    substate := (sequence budget warm).state.substate.addAccessedStorageKey
      ((sequence budget warm).state.executionEnv.codeOwner,u 13)}

private theorem first_sequence (budget : Nat) (warm : Bool) (cost : Nat)
    (fits : budget < UInt256.size) (adequate : cost ≤ budget)
    (charge : EVM.C' (sequence budget warm).state .SLOAD = cost)
    (remaining : UInt256.ofNat budget - UInt256.ofNat cost = UInt256.ofNat 103) :
    Assembly.driverSteps 1 4 #[] (sequence budget warm).state = .ok (firstSequenceExpected budget warm) := by
  let entry : Site .SLOAD := ⟨seed budget warm false,[.push ⟨1,by decide⟩ #v[0x54],.op .POP],
    [.push ⟨1,by decide⟩ #v[0x0d],.op .SLOAD,.op .STOP],by decide⟩
  have actualCost : EVM.C' (slotReadSite entry (u 13) spill).state .SLOAD = cost := charge
  have gas : EVM.C' (slotReadSite entry (u 13) spill).state .SLOAD ≤ entry.seed.gasAvailable.toNat := by
    rw [actualCost]
    change cost ≤ budget % UInt256.size
    rw [Nat.mod_eq_of_lt fits]
    exact adequate
  have h := (sload_agreement entry (u 13) spill (by decide +kernel) gas 2).1
  dsimp only at h
  have point : (EvmYul.State.sload (slotReadSite entry (u 13) spill).state.toState (u 13)).2 = u 513 := rfl
  rw [actualCost,sload_read_shape,point] at h
  simpa only [entry,sequence,firstSequenceExpected,slotReadSite,Site.state,seed_gas,seed_length,u,remaining] using h

theorem cold_to_warm :
    Assembly.driverSteps 3 4 #[] (sequence 2203 false).state = .ok (sequenceExpected 2203 false) := by
  have first := first_sequence 2203 false 2100 (by decide +kernel) (by decide) rfl (by decide +kernel)
  rw [fetched_steps_cons 2 2 #[] (sequence 2203 false).state,first]
  rfl

theorem warm_to_warm :
    Assembly.driverSteps 3 4 #[] (sequence 203 true).state = .ok (sequenceExpected 203 true) := by
  have first := first_sequence 203 true 100 (by decide +kernel) (by decide) rfl (by decide +kernel)
  rw [fetched_steps_cons 2 2 #[] (sequence 203 true).state,first]
  rfl

theorem gas_before_arity :
    Assembly.driverSteps 1 2 #[] (base .SLOAD 2099 false false).state = .error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (base .SLOAD 2100 false false).state = .error .StackUnderflow := by
  constructor <;> rfl

theorem transient_gas_before_arity :
    Assembly.driverSteps 1 2 #[] (base .TLOAD 99 false false).state = .error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (base .TLOAD 100 false false).state = .error .StackUnderflow := by
  constructor <;> rfl

theorem fuel_guard_order :
    Assembly.driverSteps 1 1 #[] (image .SLOAD 2100 false false (u 13) spill).state = .error .OutOfFuel ∧
    Assembly.driverSteps 1 1 #[] (image .SLOAD 2099 false false (u 13) spill).state = .error .OutOfFuel := by
  constructor <;> rfl

theorem warm_key_mismatch :
    Assembly.driverSteps 1 2 #[] (image .SLOAD 100 true false (u 14) spill).state = .error .OutOfGass := by rfl

theorem wrong_owner :
    (EvmYul.State.sload (seed 2100 false false).toState (u 13)).2 ≠ u 4097 := by decide +kernel

theorem persistent_transient_distinct :
    (EvmYul.State.sload (seed 2100 false false).toState (u 13)).2 ≠
      (EvmYul.State.tload (seed 2100 false false).toState (u 13)).2 := by decide +kernel

private def uintValue : PrimTy.uint.Denote := ⟨513,by decide⟩
private def intValue : PrimTy.int.Denote := ⟨-1,by decide⟩
private def boolValue : PrimTy.bool.Denote := true

private theorem maximum_word : slotWord (u (2^256-1)) = PrimTy.toWord intValue := by
  have below : 2^256-1 < 2^256 := by
    have positive : 0 < (2 : Nat)^256 := by decide
    omega
  have readNat : (u (2^256-1)).toNat = 2^256-1 := Nat.mod_eq_of_lt below
  apply Subtype.ext
  change ((u (2^256-1)).toNat : Int) = (PrimTy.toWord intValue).val
  rw [readNat]
  simp only [PrimTy.toWord,intValue,show ¬(0 : Int) ≤ -1 from by decide,dite_false]
  rw [Int.natCast_sub (by decide : 1 ≤ (2 : Nat)^256),Int.natCast_pow]
  omega

theorem source_uint :
    Assembly.driverSteps 1 2 #[] (image .SLOAD 2100 false false (u 13) spill).state =
      .ok (persistentExpected (image .SLOAD 2100 false false (u 13) spill) (u 13) (u 513) spill) := by
  let source : SVal (.prim .uint) := .prim uintValue
  let words : Solidity.Storage.Representation.Store := fun _ => PrimTy.toWord uintValue
  have found : source.find .nil = some (.prim uintValue) := rfl
  have represented : Solidity.Storage.Representation.ValueRep (.prim uintValue) .word (.root 13) words :=
    .scalar uintValue (.root 13) words rfl
  have transported : Solidity.Storage.Representation.Transport (2^256) (fun _ => 0) [.root 13] words
      (persistentWords (image .SLOAD 2100 false false (u 13) spill).state.toState) := by
    intro l covered
    have same : l = .root 13 := List.mem_singleton.mp covered
    subst l
    rfl
  have word := source_sload_word (source := source) (path := .nil) (v := uintValue)
    (l := .root 13) (words := words) (H := fun _ => 0) (touched := [.root 13])
    (image .SLOAD 2100 false false (u 13) spill).state.toState
    found represented transported (by simp only [List.mem_singleton])
  have observed : source.obs.word .nil = uintValue := by
    rw [SVal.obs_word,←SVal.find_eq_findM,found]
    rfl
  rw [observed] at word
  have encoded : UInt256.mk (Scalar.encodeValue .uint uintValue).toFin = u 513 := by rfl
  rw [encoded] at word
  exact execute_sload _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl word

theorem source_int :
    Assembly.driverSteps 1 2 #[] (image .SLOAD 2100 false false (u 15) spill).state =
      .ok (persistentExpected (image .SLOAD 2100 false false (u 15) spill) (u 15) (u (2^256-1)) spill) := by
  let source : SVal (.prim .int) := .prim intValue
  let words : Solidity.Storage.Representation.Store := fun _ => PrimTy.toWord intValue
  have found : source.find .nil = some (.prim intValue) := rfl
  have represented : Solidity.Storage.Representation.ValueRep (.prim intValue) .word (.root 15) words :=
    .scalar intValue (.root 15) words rfl
  have transported : Solidity.Storage.Representation.Transport (2^256) (fun _ => 0) [.root 15] words
      (persistentWords (image .SLOAD 2100 false false (u 15) spill).state.toState) := by
    intro l covered
    have same : l = .root 15 := List.mem_singleton.mp covered
    subst l
    have point : (EvmYul.State.sload (image .SLOAD 2100 false false (u 15) spill).state.toState (u 15)).2 = u (2^256-1) := rfl
    change slotWord (EvmYul.State.sload (image .SLOAD 2100 false false (u 15) spill).state.toState (u 15)).2 = PrimTy.toWord intValue
    rw [point]
    exact maximum_word
  have word := source_sload_word (source := source) (path := .nil) (v := intValue)
    (l := .root 15) (words := words) (H := fun _ => 0) (touched := [.root 15])
    (image .SLOAD 2100 false false (u 15) spill).state.toState
    found represented transported (by simp only [List.mem_singleton])
  have observed : source.obs.word .nil = intValue := by
    rw [SVal.obs_word,←SVal.find_eq_findM,found]
    rfl
  rw [observed] at word
  have encoded : UInt256.mk (Scalar.encodeValue .int intValue).toFin = u (2^256-1) := by rfl
  rw [encoded] at word
  exact execute_sload _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl word

theorem source_bool :
    Assembly.driverSteps 1 2 #[] (image .SLOAD 2100 false false (u 16) spill).state =
      .ok (persistentExpected (image .SLOAD 2100 false false (u 16) spill) (u 16) (u 1) spill) := by
  let source : SVal (.prim .bool) := .prim boolValue
  let words : Solidity.Storage.Representation.Store := fun _ => PrimTy.toWord boolValue
  have found : source.find .nil = some (.prim boolValue) := rfl
  have represented : Solidity.Storage.Representation.ValueRep (.prim boolValue) .word (.root 16) words :=
    .scalar boolValue (.root 16) words rfl
  have transported : Solidity.Storage.Representation.Transport (2^256) (fun _ => 0) [.root 16] words
      (persistentWords (image .SLOAD 2100 false false (u 16) spill).state.toState) := by
    intro l covered
    have same : l = .root 16 := List.mem_singleton.mp covered
    subst l
    rfl
  have word := source_sload_word (source := source) (path := .nil) (v := boolValue)
    (l := .root 16) (words := words) (H := fun _ => 0) (touched := [.root 16])
    (image .SLOAD 2100 false false (u 16) spill).state.toState
    found represented transported (by simp only [List.mem_singleton])
  have observed : source.obs.word .nil = boolValue := by
    rw [SVal.obs_word,←SVal.find_eq_findM,found]
    rfl
  rw [observed] at word
  have encoded : UInt256.mk (Scalar.encodeValue .bool boolValue).toFin = u 1 := by rfl
  rw [encoded] at word
  exact execute_sload _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) rfl word

theorem wrong_representation_root :
    ¬Solidity.Storage.Representation.Transport (2^256) (fun _ => 0) [.root 14]
      (fun _ => PrimTy.toWord uintValue) (persistentWords (seed 2100 false false).toState) := by
  intro represented
  have bad : persistentWords (seed 2100 false false).toState 14 ≠ PrimTy.toWord uintValue := by decide +kernel
  exact bad (represented (.root 14) (by simp only [List.mem_singleton]))

private def otherOwner : Site .SLOAD :=
  let old := image .SLOAD 100 true false (u 13) spill
  {old with seed := {old.seed with executionEnv := {old.seed.executionEnv with codeOwner := .ofNat 11}}}

theorem warm_owner_mismatch :
    Assembly.driverSteps 1 2 #[] otherOwner.state = .error .OutOfGass := by rfl

theorem read_static_refusal_negative :
    Assembly.driverSteps 1 2 #[] (image .SLOAD 2100 false false (u 13) spill).state ≠ .error .StaticModeViolation ∧
    Assembly.driverSteps 1 2 #[] (image .TLOAD 100 false false (u 13) spill).state ≠ .error .StaticModeViolation := by
  constructor
  · rw [cold_persistent]
    intro impossible
    cases impossible
  · rw [transient_separate]
    intro impossible
    cases impossible

#print axioms warm_owner_mismatch
#print axioms read_static_refusal_negative
#print axioms cold_persistent
#print axioms warm_persistent
#print axioms neighbor_slot
#print axioms unset_slot
#print axioms wrapped_root
#print axioms transient_separate
#print axioms writable_reads
#print axioms stack_boundary
#print axioms absent_account_zero
#print axioms cold_to_warm
#print axioms warm_to_warm
#print axioms gas_before_arity
#print axioms transient_gas_before_arity
#print axioms fuel_guard_order
#print axioms warm_key_mismatch
#print axioms wrong_owner
#print axioms persistent_transient_distinct
#print axioms source_uint
#print axioms source_int
#print axioms source_bool
#print axioms wrong_representation_root
end SolidityBridge.RoadmapV15.P10.StorageReadControls
