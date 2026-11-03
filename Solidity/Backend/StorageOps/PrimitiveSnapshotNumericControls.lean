import Solidity.Backend.StorageOps.PrimitiveSnapshotNumeric

/-! Actual overlapping fixed snapshot, frozen numeric/symbolic prefixes and
executing wrong streaming control. Per-run address premise is inhabited. -/
namespace Solidity.Backend.StorageOps.PrimitiveSnapshotNumeric.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def word (n : Fin 128) : Semantics.Word := lengthWord n.val (by have bound:=n.isLt; omega)
private def size : FixedSize := ⟨3,by decide⟩
private def src : Solidity.Storage.Loc := .root 0
private def dst : Solidity.Storage.Loc := .root 1
private def locations : List Solidity.Storage.Loc := [.root 0,.root 1,.root 2,.root 3,.root 4,.root 5]
private def hash (_ : Solidity.Storage.Pre) : Nat := 0
private def captured : Store := fun l => if l=.root 0 then word 17 else if l=.root 1 then word 23 else
 if l=.root 2 then word 53 else if l=.root 3 then word 71 else if l=.root 4 then word 87 else if l=.root 5 then word 99 else word 0
private def initial : WordStore := fun a => captured (.root a)
private noncomputable def target : Evm.Machine :=
 {Evm.Machine.init (fun _ => 19) ⟨7,by decide⟩ with
 store:=⟨fun slot => TargetOperations.encodeWord (captured (Solidity.Storage.ofSlot slot))⟩
 stack:=[.val ⟨31,by decide⟩,.slot (.root 9)]
 mem:=fun _ => .val ⟨41,by decide⟩
 caller:=⟨13,by decide⟩
 timestamp:=⟨59,by decide⟩}
private noncomputable def output := TargetFixedSnapshot.afterCopy .uint size target (.root 0) (.root 1)
private def afterNumeric := numeric 16 hash initial dst src 3
private def afterSymbolic := symbolic captured dst src 3
private theorem finite : FiniteRun 16 1 6 hash [] locations := by
 constructor
 · intro p; change 0<16; decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
private theorem before : Transport 16 hash locations captured initial := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
private theorem sourceCovered : ∀ i<3,src.add i ∈ locations := by
 intro i inside
 have cases : i=0 ∨ i=1 ∨ i=2 := by omega
 rcases cases with rfl|rfl|rfl <;> decide
private theorem dstCovered : ∀ i<3,dst.add i ∈ locations := by
 intro i inside
 have cases : i=0 ∨ i=1 ∨ i=2 := by omega
 rcases cases with rfl|rfl|rfl <;> decide
private theorem fitting : ∀ l ∈ locations,TargetOperations.KeysFit l := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> exact True.intro
private theorem agreement : ∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (initial (l.word 16 hash)) := by
 intro l member
 change TargetOperations.encodeWord (captured (Solidity.Storage.ofSlot (TargetOperations.toSlot l (fitting l member))))=_
 rw [TargetOperations.ofSlot_toSlot,← before l member]

/-- A nonempty overlap discharges actual full target/numeric and symbolic
transport premises; no intermediate source stability is assumed. -/
theorem certificate :
 Evm.run (TargetFixedSnapshot.code .uint size (.root 0) (.root 1)) target=.ok output 0 ∧
 Transport 16 hash locations afterSymbolic afterNumeric ∧
 (∀ l (member : l ∈ locations),output.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (afterNumeric (l.word 16 hash))) := by
 have targetRun := target_complete finite .uint size target initial dst src True.intro True.intro sourceCovered dstCovered fitting agreement
 exact ⟨targetRun.1,transported finite captured initial before dst src 3 sourceCovered dstCovered 3 (by decide),targetRun.2⟩

theorem prefixes :
 (List.range 4).map (fun count => locations.map (fun l => (symbolic captured dst src count l).val))=
 [[17,23,53,71,87,99],[17,17,53,71,87,99],[17,17,23,71,87,99],[17,17,23,53,87,99]] ∧
 (List.range 4).map (fun count => locations.map (fun l => (numeric 16 hash initial dst src count (l.word 16 hash)).val))=
 [[17,23,53,71,87,99],[17,17,53,71,87,99],[17,17,23,71,87,99],[17,17,23,53,87,99]] ∧
 locations.attach.map (fun l => (target.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[17,23,53,71,87,99] ∧
 locations.attach.map (fun l => (output.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[17,17,23,53,87,99] ∧
 {output with store:=target.store}=target := by
 exact ⟨rfl,rfl,rfl,by decide,rfl⟩

theorem frozen_source : initial 1=word 23 ∧ numeric 16 hash initial dst src 1 1=word 17 ∧
 numeric 16 hash initial dst src 2 2=word 23 ∧
 (∀ count,count≤3 → Transport 16 hash locations (symbolic captured dst src count) (numeric 16 hash initial dst src count)) := by
 exact ⟨rfl,rfl,rfl,transported finite captured initial before dst src 3 sourceCovered dstCovered⟩

private def streaming1 := writeWord initial 1 (initial 0)
private def streaming2 := writeWord streaming1 2 (streaming1 1)
private def streaming3 := writeWord streaming2 3 (streaming2 2)
private noncomputable def target1 := {target with store:=Evm.WordStore.write target.store (.root 1) 17}
private noncomputable def target2 := {target1 with store:=Evm.WordStore.write target1.store (.root 2) 17}
private noncomputable def wrongTarget := {target2 with store:=Evm.WordStore.write target2.store (.root 3) 17}
private def wrongCode := TargetOperations.copyCode (.root 1) (.root 0) ++
 (TargetOperations.copyCode (.root 2) (.root 1) ++ TargetOperations.copyCode (.root 3) (.root 2))
private theorem copy_known (machine : Evm.Machine) (dst src : Evm.Slot) (value : Nat) (known : machine.store src=value) :
 Evm.run (TargetOperations.copyCode dst src) machine=.ok {machine with store:=Evm.WordStore.write machine.store dst value} 0 := by
 rw [TargetOperations.run_copy,Evm.WordStore.cells_val,known]

theorem wrong_streaming :
 Evm.run wrongCode target=.ok wrongTarget 0 ∧
 locations.map (fun l => (streaming3 (l.word 16 hash)).val)=[17,17,17,17,87,99] ∧
 locations.attach.map (fun l => (wrongTarget.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[17,17,17,17,87,99] ∧
 ¬ Transport 16 hash locations afterSymbolic streaming3 := by
 refine ⟨?_,rfl,by decide,?_⟩
 · unfold wrongCode
   rw [Evm.run_append_ok (copy_known target (.root 1) (.root 0) 17 rfl)]
   change Evm.run (TargetOperations.copyCode (.root 2) (.root 1) ++ TargetOperations.copyCode (.root 3) (.root 2)) target1=.ok wrongTarget 0
   rw [Evm.run_append_ok (copy_known target1 (.root 2) (.root 1) 17 (Evm.WordStore.write_same_of_lt _ _ _ (by decide)))]
   exact copy_known target2 (.root 3) (.root 2) 17 (Evm.WordStore.write_same_of_lt _ _ _ (by decide))
 · intro alleged
   have bad:=alleged (.root 2) (by decide)
   change word 17=word 23 at bad
   have impossible:=congrArg (fun w : Semantics.Word => w.val) bad
   change (17:Int)=23 at impossible
   omega

/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotNumeric.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotNumeric.Controls.prefixes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms prefixes
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotNumeric.Controls.frozen_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms frozen_source
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotNumeric.Controls.wrong_streaming' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_streaming
end Solidity.Backend.StorageOps.PrimitiveSnapshotNumeric.Controls
