import Solidity.Backend.StorageOps.PrimitiveSnapshotOwner

/-! Nonempty fixed primitive graph owner and actual numeric/target snapshot,
including absent-versus-stored-zero and overlapping physical spans. -/
namespace Solidity.Backend.StorageOps.PrimitiveSnapshotOwner.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def graph : Schema 0 where
 origin := "v10-fixed-primitive"
 declId := fun i => nomatch i
 declId_injective := by intro i; exact Fin.elim0 i
 name := fun i => nomatch i
 fields := fun i => nomatch i
 rank := fun i => nomatch i
 nonempty := by intro i; exact Fin.elim0 i
 distinct := by intro i; exact Fin.elim0 i
 guarded := by intro i; exact Fin.elim0 i
private def word (n : Fin 128) : Semantics.Word := lengthWord n.val (by have bound:=n.isLt; omega)
private def size : FixedSize := ⟨3,by decide⟩
private def src : Solidity.Storage.Loc := .root 0
private def dst : Solidity.Storage.Loc := .root 1
private def locations : List Solidity.Storage.Loc := [.root 0,.root 1,.root 2,.root 3,.root 4,.root 5]
private def hash (_ : Solidity.Storage.Pre) : Nat := 0
private def captured : Store := fun l => if l=.root 0 then word 17 else if l=.root 1 then word 0 else
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
private def afterNumeric := PrimitiveSnapshotNumeric.numeric 16 hash initial dst src 3
private def afterSymbolic := PrimitiveSnapshotNumeric.symbolic captured dst src 3
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


private def sourceSlots : Fin size.val → Slot graph (.prim .uint) := fun i =>
 if i.val=1 then .absent else .present (.prim (if i.val=0 then word 17 else word 53))
private def oldSlots : Fin size.val → Slot graph (.prim .uint) := fun i =>
 if i.val=0 then .absent else .present (.prim (if i.val=1 then word 53 else word 71))
private def source : Value graph (.fixed (.prim .uint) size) := .fixed sourceSlots
private def old : Value graph (.fixed (.prim .uint) size) := .fixed oldSlots
private def result := recursiveCopy old source
private def resultSlots : Fin size.val → Slot graph (.prim .uint) := fun i => recursiveSlot (oldSlots i) (sourceSlots i)
private def indices : List (Fin size.val) := [⟨2,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩]
private def qs := indices.map (query (G:=graph) (p:=PrimTy.uint))
private def ix (i : Fin 4) : Index := ⟨i.val,by have bound:=i.isLt; omega⟩
private def observations : List (Query graph (.fixed (.prim .uint) size)) :=
 [.word (TargetFixedPrimitive.path (ix 0)),.word (TargetFixedPrimitive.path (ix 1)),.word (TargetFixedPrimitive.path (ix 2)),.word (TargetFixedPrimitive.path (ix 3))]
private theorem sourceOwner : Represented source qs src captured := by
 intro q member
 obtain ⟨i,inside,rfl⟩:=List.mem_map.mp member
 change i ∈ indices at inside
 simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at inside
 rcases inside with rfl|rfl|rfl|rfl
 all_goals refine ⟨?_,True.intro,?_⟩
 all_goals first
  | (change 2<size.val ∧ True; decide)
  | (change 0<size.val ∧ True; decide)
  | (change 1<size.val ∧ True; decide)
  | (intro value observed; have same:=Option.some.inj observed; subst value; rfl)
private theorem targetBefore : ∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (captured l) := by
 intro l member
 change TargetOperations.encodeWord (captured (Solidity.Storage.ofSlot (TargetOperations.toSlot l (fitting l member))))=_
 rw [TargetOperations.ofSlot_toSlot]

theorem certificate : Represented result qs dst afterSymbolic ∧ Transport 16 hash locations afterSymbolic afterNumeric ∧
 Evm.run (TargetFixedSnapshot.code .uint size (.root 0) (.root 1)) target=.ok output 0 ∧
 (∀ l (member : l ∈ locations),output.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (afterNumeric (l.word 16 hash))) := by
 exact complete finite old source indices dst src True.intro True.intro captured initial target before sourceOwner sourceCovered dstCovered fitting targetBefore

theorem graph_ordered :
 observations.map (fun q => (q.read source).map Subtype.val)=[some 17,some 0,some 53,none] ∧
 observations.map (fun q => (q.read old).map Subtype.val)=[some 0,some 53,some 71,none] ∧
 observations.map (fun q => (q.read result).map Subtype.val)=[some 17,some 0,some 53,none] ∧
 qs.map (fun q => (q.read result).map Subtype.val)=[some 53,some 17,some 0,some 53] := by
 exact ⟨rfl,rfl,rfl,rfl⟩

theorem storage_ordered :
 locations.map (fun l => (captured l).val)=[17,0,53,71,87,99] ∧
 locations.map (fun l => (afterSymbolic l).val)=[17,17,0,53,87,99] ∧
 locations.map (fun l => (initial (l.word 16 hash)).val)=[17,0,53,71,87,99] ∧
 locations.map (fun l => (afterNumeric (l.word 16 hash)).val)=[17,17,0,53,87,99] ∧
 locations.attach.map (fun l => (target.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[17,0,53,71,87,99] ∧
 locations.attach.map (fun l => (output.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[17,17,0,53,87,99] ∧
 {output with store:=target.store}=target := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,by decide,rfl⟩

theorem raw_presence : result=.fixed resultSlots ∧ sourceSlots ⟨1,by decide⟩=.absent ∧
 oldSlots ⟨0,by decide⟩=.absent ∧ resultSlots ⟨0,by decide⟩=.present (.prim (word 17)) ∧
 resultSlots ⟨1,by decide⟩=.present (.prim (word 0)) ∧ resultSlots ⟨1,by decide⟩≠sourceSlots ⟨1,by decide⟩ := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,by intro same; cases same⟩

theorem malformed : source.find (TargetFixedPrimitive.path (ix 3))=none ∧
 result.find (TargetFixedPrimitive.path (ix 3))=none ∧
 Evm.run (TargetOperations.readCode (.root 4)) output=.ok {output with stack:=.val (TargetOperations.encodeWord (word 87))::output.stack} 0 ∧
 Evm.run (TargetOperations.readCode (.root 2)) output=.ok {output with stack:=.val (TargetOperations.encodeWord (word 0))::output.stack} 0 := by
 exact ⟨rfl,rfl,rfl,rfl⟩

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

theorem wrong_streaming : Evm.run wrongCode target=.ok wrongTarget 0 ∧
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
   change word 17=word 0 at bad
   have impossible:=congrArg (fun w : Semantics.Word => w.val) bad
   change (17:Int)=0 at impossible
   omega

private def wrongDefault := Representation.write captured (.root 1) (word 23)
theorem required_default_owner : ¬ Represented source qs src wrongDefault := by
 intro alleged
 have bad:=(alleged (query (G:=graph) (p:=PrimTy.uint) ⟨1,by decide⟩) (by
  apply List.mem_map.mpr
  exact ⟨⟨1,by decide⟩,by decide,rfl⟩)).2.2 (word 0) rfl
 change word 23=word 0 at bad
 have impossible:=congrArg (fun w : Semantics.Word => w.val) bad
 change (23:Int)=0 at impossible
 omega

/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotOwner.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotOwner.Controls.graph_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms graph_ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotOwner.Controls.storage_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms storage_ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotOwner.Controls.raw_presence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms raw_presence
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotOwner.Controls.malformed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms malformed
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotOwner.Controls.wrong_streaming' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_streaming
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotOwner.Controls.required_default_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms required_default_owner
end Solidity.Backend.StorageOps.PrimitiveSnapshotOwner.Controls
