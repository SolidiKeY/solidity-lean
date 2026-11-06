import Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation

/-! Actual overlapping fixed snapshot, frozen numeric/symbolic prefixes and
executing wrong streaming control. Per-run address premise is inhabited. -/
namespace Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph PrimitiveSnapshotNumeric
private def word (n : Fin 128) : Semantics.Word := lengthWord n.val (by have bound:=n.isLt; omega)
private def ma : FixedSize := ⟨2,by decide⟩
private def mb : FixedSize := ⟨3,by decide⟩
private def src : Solidity.Storage.Loc := .root 0
private def dst : Solidity.Storage.Loc := .root 1
private def locations : List Solidity.Storage.Loc := [.root 0,.root 1,.root 2,.root 3,.root 4,.root 5,.root 6,.root 7,.root 8]
private def hash (_ : Solidity.Storage.Pre) : Nat := 0
private def captured : Store := fun l => if l=.root 0 then word 17 else if l=.root 1 then word 23 else
 if l=.root 2 then word 53 else if l=.root 3 then word 71 else if l=.root 4 then word 87 else if l=.root 5 then word 99 else if l=.root 6 then word 101 else if l=.root 7 then word 109 else if l=.root 8 then word 127 else word 0
private def initial : WordStore := fun a => captured (.root a)
private noncomputable def target : Evm.Machine :=
 {Evm.Machine.init (fun _ => 19) ⟨7,by decide⟩ with
 store:=⟨fun slot => TargetOperations.encodeWord (captured (Solidity.Storage.ofSlot slot))⟩
 stack:=[.val ⟨31,by decide⟩,.slot (.root 9)]
 mem:=fun _ => .val ⟨41,by decide⟩
 caller:=⟨13,by decide⟩
 timestamp:=⟨59,by decide⟩}
private theorem finite : FiniteRun 16 1 9 hash [] locations := by
 constructor
 · intro p; change 0<16; decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
private theorem before : Transport 16 hash locations captured initial := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
private theorem covered (offset count : Nat) (bound : offset+count≤9) : ∀ i<count,(Solidity.Storage.Loc.root offset).add i ∈ locations := by
 intro i inside
 have cases : offset+i=0 ∨ offset+i=1 ∨ offset+i=2 ∨ offset+i=3 ∨ offset+i=4 ∨ offset+i=5 ∨ offset+i=6 ∨ offset+i=7 ∨ offset+i=8 := by omega
 change Solidity.Storage.Loc.root (offset+i) ∈ locations
 rcases cases with h|h|h|h|h|h|h|h|h <;> rw [h] <;> decide
private theorem fitting : ∀ l ∈ locations,TargetOperations.KeysFit l := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact True.intro
private theorem agreement : ∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (initial (l.word 16 hash)) := by
 intro l member
 change TargetOperations.encodeWord (captured (Solidity.Storage.ofSlot (TargetOperations.toSlot l (fitting l member))))=_
 rw [TargetOperations.ofSlot_toSlot,← before l member]
private def an (m : WordStore) := numeric 16 hash m (.root 1) (.root 0) 2
private def bn (m : WordStore) := numeric 16 hash m (.root 5) (.root 4) 3
private def ast (m : Store) := symbolic m (.root 1) (.root 0) 2
private def bst (m : Store) := symbolic m (.root 5) (.root 4) 3
private noncomputable def machineA (m : Evm.Machine) := TargetFixedSnapshot.afterCopy .uint ma m (.root 0) (.root 1)
private noncomputable def bt (m : Evm.Machine) := TargetFixedSnapshot.afterCopy .uint mb m (.root 4) (.root 5)
private def ca := TargetFixedSnapshot.code .uint ma (.root 0) (.root 1)
private def cb := TargetFixedSnapshot.code .uint mb (.root 4) (.root 5)
private def nw (m : WordStore) := locations.map (fun l => (m (l.word 16 hash)).val)
private def sw (m : Store) := locations.map (fun l => (m l).val)
private noncomputable def tw (m : Evm.Machine) := locations.attach.map (fun l => (m.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)

theorem commutes : bn (an initial)=an (bn initial) := by
 apply commute finite initial (.root 1) (.root 0) 2 (.root 5) (.root 4) 3
  (covered 1 2 (by decide)) (covered 0 2 (by decide)) (covered 5 3 (by decide)) (covered 4 3 (by decide))
 all_goals intro i hi j hj same
 all_goals have equal:=Solidity.Storage.Loc.root.inj same
 all_goals omega

theorem forward : Transport 16 hash locations (bst (ast captured)) (bn (an initial)) ∧
 Evm.run (ca++cb) target=.ok (bt (machineA target)) 0 ∧
 (∀ l (member : l ∈ locations),(bt (machineA target)).store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (bn (an initial) (l.word 16 hash))) := by
 exact target_sequence finite .uint .uint ma mb captured initial target before (.root 1) (.root 0) (.root 5) (.root 4)
  True.intro True.intro True.intro True.intro (covered 1 2 (by decide)) (covered 0 2 (by decide)) (covered 5 3 (by decide)) (covered 4 3 (by decide)) fitting agreement

theorem backward : Transport 16 hash locations (ast (bst captured)) (an (bn initial)) ∧
 Evm.run (cb++ca) target=.ok (machineA (bt target)) 0 ∧
 (∀ l (member : l ∈ locations),(machineA (bt target)).store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (an (bn initial) (l.word 16 hash))) := by
 exact target_sequence finite .uint .uint mb ma captured initial target before (.root 5) (.root 4) (.root 1) (.root 0)
  True.intro True.intro True.intro True.intro (covered 5 3 (by decide)) (covered 4 3 (by decide)) (covered 1 2 (by decide)) (covered 0 2 (by decide)) fitting agreement

theorem ordered :
 sw captured=[17,23,53,71,87,99,101,109,127] ∧
 sw (ast captured)=[17,17,23,71,87,99,101,109,127] ∧
 sw (bst captured)=[17,23,53,71,87,87,99,101,127] ∧
 sw (bst (ast captured))=[17,17,23,71,87,87,99,101,127] ∧
 sw (ast (bst captured))=[17,17,23,71,87,87,99,101,127] ∧
 nw initial=[17,23,53,71,87,99,101,109,127] ∧
 nw (an initial)=[17,17,23,71,87,99,101,109,127] ∧
 nw (bn initial)=[17,23,53,71,87,87,99,101,127] ∧
 nw (bn (an initial))=[17,17,23,71,87,87,99,101,127] ∧
 nw (an (bn initial))=[17,17,23,71,87,87,99,101,127] ∧
 tw target=[17,23,53,71,87,99,101,109,127] ∧
 tw (machineA target)=[17,17,23,71,87,99,101,109,127] ∧
 tw (bt target)=[17,23,53,71,87,87,99,101,127] ∧
 tw (bt (machineA target))=[17,17,23,71,87,87,99,101,127] ∧
 tw (machineA (bt target))=[17,17,23,71,87,87,99,101,127] ∧
 {machineA target with store:=target.store}=target ∧
 {bt target with store:=target.store}=target ∧
 {bt (machineA target) with store:=target.store}=target ∧
 {machineA (bt target) with store:=target.store}=target := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,by decide,by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl⟩

theorem stable_logs :
 (log 16 hash (an initial) (.root 5) (.root 4) 3).map (fun op => (op.1,op.2.val))=[(.root 5,87),(.root 6,99),(.root 7,101)] ∧
 log 16 hash (an initial) (.root 5) (.root 4) 3=log 16 hash initial (.root 5) (.root 4) 3 ∧
 initial 1=word 23 ∧ an initial 1=word 17 ∧ bn (an initial) 2=word 23 := by
 refine ⟨rfl,?_,rfl,rfl,rfl⟩
 apply log_stable finite initial (.root 1) (.root 0) 2 (.root 5) (.root 4) 3 (covered 1 2 (by decide)) (covered 4 3 (by decide))
 intro j hj i hi same
 have equal:=Solidity.Storage.Loc.root.inj same
 omega

private def dependentn (m : WordStore) := numeric 16 hash m (.root 5) (.root 1) 3
private def dependents (m : Store) := symbolic m (.root 5) (.root 1) 3
private noncomputable def dependentt (m : Evm.Machine) := TargetFixedSnapshot.afterCopy .uint mb m (.root 1) (.root 5)
private def dependentCode := TargetFixedSnapshot.code .uint mb (.root 1) (.root 5)
theorem dependent_order :
 Transport 16 hash locations (dependents (ast captured)) (dependentn (an initial)) ∧
 Transport 16 hash locations (ast (dependents captured)) (an (dependentn initial)) ∧
 Evm.run (ca++dependentCode) target=.ok (dependentt (machineA target)) 0 ∧
 Evm.run (dependentCode++ca) target=.ok (machineA (dependentt target)) 0 ∧
 sw (dependents (ast captured))=[17,17,23,71,87,17,23,71,127] ∧ sw (ast (dependents captured))=[17,17,23,71,87,23,53,71,127] ∧
 nw (dependentn (an initial))=[17,17,23,71,87,17,23,71,127] ∧ nw (an (dependentn initial))=[17,17,23,71,87,23,53,71,127] ∧
 tw (dependentt (machineA target))=[17,17,23,71,87,17,23,71,127] ∧ tw (machineA (dependentt target))=[17,17,23,71,87,23,53,71,127] ∧
 (∀ l (member : l ∈ locations),(dependentt (machineA target)).store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (dependentn (an initial) (l.word 16 hash))) ∧
 (∀ l (member : l ∈ locations),(machineA (dependentt target)).store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (an (dependentn initial) (l.word 16 hash))) ∧
 {dependentt (machineA target) with store:=target.store}=target ∧
 {machineA (dependentt target) with store:=target.store}=target ∧
 dependentn (an initial) 5≠an (dependentn initial) 5 := by
 have ab:=target_sequence finite .uint .uint ma mb captured initial target before (.root 1) (.root 0) (.root 5) (.root 1)
  True.intro True.intro True.intro True.intro (covered 1 2 (by decide)) (covered 0 2 (by decide)) (covered 5 3 (by decide)) (covered 1 3 (by decide)) fitting agreement
 have ba:=target_sequence finite .uint .uint mb ma captured initial target before (.root 5) (.root 1) (.root 1) (.root 0)
  True.intro True.intro True.intro True.intro (covered 5 3 (by decide)) (covered 1 3 (by decide)) (covered 1 2 (by decide)) (covered 0 2 (by decide)) fitting agreement
 exact ⟨ab.1,ba.1,ab.2.1,ba.2.1,rfl,rfl,rfl,rfl,by decide,by decide,ab.2.2,ba.2.2,rfl,rfl,by decide⟩

private def collisionn (m : WordStore) := numeric 16 hash m (.root 2) (.root 4) 3
private def collisions (m : Store) := symbolic m (.root 2) (.root 4) 3
private noncomputable def collisiont (m : Evm.Machine) := TargetFixedSnapshot.afterCopy .uint mb m (.root 4) (.root 2)
private def collisionCode := TargetFixedSnapshot.code .uint mb (.root 4) (.root 2)
theorem collision_order :
 Transport 16 hash locations (collisions (ast captured)) (collisionn (an initial)) ∧
 Transport 16 hash locations (ast (collisions captured)) (an (collisionn initial)) ∧
 Evm.run (ca++collisionCode) target=.ok (collisiont (machineA target)) 0 ∧
 Evm.run (collisionCode++ca) target=.ok (machineA (collisiont target)) 0 ∧
 sw (collisions (ast captured))=[17,17,87,99,101,99,101,109,127] ∧ sw (ast (collisions captured))=[17,17,23,99,101,99,101,109,127] ∧
 nw (collisionn (an initial))=[17,17,87,99,101,99,101,109,127] ∧ nw (an (collisionn initial))=[17,17,23,99,101,99,101,109,127] ∧
 tw (collisiont (machineA target))=[17,17,87,99,101,99,101,109,127] ∧ tw (machineA (collisiont target))=[17,17,23,99,101,99,101,109,127] ∧
 (∀ l (member : l ∈ locations),(collisiont (machineA target)).store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (collisionn (an initial) (l.word 16 hash))) ∧
 (∀ l (member : l ∈ locations),(machineA (collisiont target)).store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (an (collisionn initial) (l.word 16 hash))) ∧
 {collisiont (machineA target) with store:=target.store}=target ∧
 {machineA (collisiont target) with store:=target.store}=target ∧
 collisionn (an initial) 2≠an (collisionn initial) 2 := by
 have ab:=target_sequence finite .uint .uint ma mb captured initial target before (.root 1) (.root 0) (.root 2) (.root 4)
  True.intro True.intro True.intro True.intro (covered 1 2 (by decide)) (covered 0 2 (by decide)) (covered 2 3 (by decide)) (covered 4 3 (by decide)) fitting agreement
 have ba:=target_sequence finite .uint .uint mb ma captured initial target before (.root 2) (.root 4) (.root 1) (.root 0)
  True.intro True.intro True.intro True.intro (covered 2 3 (by decide)) (covered 4 3 (by decide)) (covered 1 2 (by decide)) (covered 0 2 (by decide)) fitting agreement
 exact ⟨ab.1,ba.1,ab.2.1,ba.2.1,rfl,rfl,rfl,rfl,by decide,by decide,ab.2.2,ba.2.2,rfl,rfl,by decide⟩

/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation.Controls.commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms commutes
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation.Controls.forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms forward
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation.Controls.backward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms backward
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation.Controls.stable_logs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms stable_logs
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation.Controls.dependent_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms dependent_order
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation.Controls.collision_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms collision_order
end Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation.Controls
