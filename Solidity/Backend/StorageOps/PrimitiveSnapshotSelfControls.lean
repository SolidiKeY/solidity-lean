import Solidity.Backend.StorageOps.PrimitiveSnapshotSelf

/-! Actual self-copy with nonzero values and default-prefix materialization. -/
namespace Solidity.Backend.StorageOps.PrimitiveSnapshotSelf.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph PrimitiveSnapshotSequence
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
private def size : FixedSize := ⟨3,by decide⟩
private def ix (i : Fin 5) : Index := ⟨i.val,by have bound:=i.isLt; omega⟩
private def w (x : Fin 256) : Semantics.Word := lengthWord x.val (by have bound:=x.isLt; omega)

private abbrev T : TypeGraph.Ty 0 := .fixed (.prim .uint) size
private def leaf : Value graph T := .fixed (fun i => if i.val=1 then .absent else .present (.prim (if i.val=0 then w 17 else w 53)))
private def root : Value graph (.mapping .uint T) := .mapping (fun _ => .absent)
private def pre : TypeGraph.Path graph (.mapping .uint T) T := .cons (.key (w 0)) .nil
private def other : TypeGraph.Path graph (.mapping .uint T) T := .cons (.key (w 1)) .nil
private def old : Value graph T := Value.dflt T
private def result := (recursiveCopyAt root pre pre).getD root
private def indices : List (Fin size.val) := [⟨2,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩]
private def hash (_ : Solidity.Storage.Pre) : Nat := 16
private def mapped (i : Nat) : Solidity.Storage.Loc := .hash 0 (.root 0) i
private def locations : List Solidity.Storage.Loc := [.root 0,.root 1,.root 2,.root 3,.root 4,mapped 0,mapped 1,mapped 2]
private def captured : Store := fun l => if l=.root 0 then w 71 else if l=.root 1 then w 17 else if l=.root 3 then w 53 else if l=.root 4 then w 99 else w 0
private def initial : WordStore := fun a => captured (.root a)
private noncomputable def target : Evm.Machine :=
 {Evm.Machine.init (fun _ => 19) ⟨7,by decide⟩ with
 store:=⟨fun slot => TargetOperations.encodeWord (captured (Solidity.Storage.ofSlot slot))⟩
 stack:=[.val ⟨31,by decide⟩,.slot (.root 9)]
 mem:=fun _ => .val ⟨41,by decide⟩
 caller:=⟨13,by decide⟩
 timestamp:=⟨59,by decide⟩}
private def slot : Evm.Slot := .hash ⟨0,by decide⟩ (.root 0) 0
private def leafCode := TargetFixedSnapshot.code .uint size (.root 1) (.root 1)
private def mapCode := TargetFixedSnapshot.code .uint size slot slot
private theorem before : Transport 64 hash locations captured initial := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
private theorem fitting : ∀ l ∈ locations,TargetOperations.KeysFit l := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals first | exact True.intro | exact ⟨by decide,True.intro⟩
private theorem agreement : ∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (initial (l.word 64 hash)) := by
 intro l member
 change TargetOperations.encodeWord (captured (Solidity.Storage.ofSlot (TargetOperations.toSlot l (fitting l member))))=_
 rw [TargetOperations.ofSlot_toSlot,← before l member]
private theorem leafOwner : Represented leaf (queries .nil indices) (.root 1) captured := by
 intro query member
 simp only [queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl
 all_goals refine ⟨?_,True.intro,?_⟩
 all_goals first
  | (change 2<size.val ∧ True; decide)
  | (change 0<size.val ∧ True; decide)
  | (change 1<size.val ∧ True; decide)
  | (intro value observed; have same:=Option.some.inj observed; subst value; rfl)
private theorem mapOwner : Represented root (queries pre indices) (.root 0) captured := by
 intro query member
 simp only [queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl
 all_goals refine ⟨?_,True.intro,?_⟩
 all_goals first
  | (change True ∧ (2<size.val ∧ True); decide)
  | (change True ∧ (0<size.val ∧ True); decide)
  | (change True ∧ (1<size.val ∧ True); decide)
  | (intro value observed; have same:=Option.some.inj observed; subst value; rfl)

theorem leaf_certificate : Represented leaf (queries .nil indices) (.root 1) captured ∧
 Transport 64 hash locations captured initial ∧ Evm.run leafCode target=.ok target 0 ∧
 (∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (initial (l.word 64 hash))) := by
 have copied : recursiveCopyAt leaf .nil .nil=some leaf := by
  change some (recursiveCopy leaf leaf)=some leaf
  exact congrArg some (value_self leaf)
 have all:=complete leaf leaf .nil leaf rfl copied True.intro indices (.root 1) True.intro captured initial target hash locations leafOwner before fitting agreement
 simpa only [symbolic_self,numeric_self] using all

theorem mapping_certificate : Represented result (queries pre indices) (.root 0) captured ∧
 Transport 64 hash locations captured initial ∧ Evm.run mapCode target=.ok target 0 ∧
 (∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (initial (l.word 64 hash))) := by
 have all:=complete root result pre old rfl rfl (by exact ⟨True.intro,True.intro⟩) indices (.root 0) True.intro captured initial target hash locations mapOwner before fitting agreement
 simpa only [symbolic_self,numeric_self] using all

theorem raw_materialization : recursiveCopyAt root pre pre=some result ∧ recursiveCopyAt result pre pre=some result ∧ result≠root ∧
 root.find pre=some old ∧ result.find pre=some old ∧
 pre.readLive Value.dflt root=some old ∧ pre.readLive Value.dflt result=some old ∧
 root.find other=some old ∧ result.find other=some old := by
 refine ⟨rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
 · exact after_save root result pre (recursiveCopy old old) rfl
 · intro same
   have slots:=Value.mapping.inj same
   have bad:=congrFun slots (w 0)
   cases bad

theorem graph_ordered :
 (queries .nil indices).map (fun q => (q.read leaf).map Subtype.val)=[some 53,some 17,some 0,some 53] ∧
 (queries .nil indices).map (fun q => (q.read (recursiveCopy leaf leaf)).map Subtype.val)=[some 53,some 17,some 0,some 53] ∧
 (queries pre indices).map (fun q => (q.read root).map Subtype.val)=[some 0,some 0,some 0,some 0] ∧
 (queries pre indices).map (fun q => (q.read result).map Subtype.val)=[some 0,some 0,some 0,some 0] ∧
 (queries other indices).map (fun q => (q.read root).map Subtype.val)=[some 0,some 0,some 0,some 0] ∧
 (queries other indices).map (fun q => (q.read result).map Subtype.val)=[some 0,some 0,some 0,some 0] := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

private def selfStoreLeaf := PrimitiveSnapshotNumeric.symbolic captured (.root 1) (.root 1) 3
private def selfStoreMap := PrimitiveSnapshotNumeric.symbolic captured (mapped 0) (mapped 0) 3
private def selfNumericLeaf := PrimitiveSnapshotNumeric.numeric 64 hash initial (.root 1) (.root 1) 3
private def selfNumericMap := PrimitiveSnapshotNumeric.numeric 64 hash initial (mapped 0) (mapped 0) 3
private noncomputable def selfTargetLeaf := TargetFixedSnapshot.afterCopy .uint size target (.root 1) (.root 1)
private noncomputable def selfTargetMap := TargetFixedSnapshot.afterCopy .uint size target slot slot
theorem physical_ordered :
 locations.map (fun l => (captured l).val)=[71,17,0,53,99,0,0,0] ∧
 locations.map (fun l => (selfStoreLeaf l).val)=[71,17,0,53,99,0,0,0] ∧
 locations.map (fun l => (selfStoreMap l).val)=[71,17,0,53,99,0,0,0] ∧
 locations.map (fun l => (initial (l.word 64 hash)).val)=[71,17,0,53,99,0,0,0] ∧
 locations.map (fun l => (selfNumericLeaf (l.word 64 hash)).val)=[71,17,0,53,99,0,0,0] ∧
 locations.map (fun l => (selfNumericMap (l.word 64 hash)).val)=[71,17,0,53,99,0,0,0] ∧
 locations.attach.map (fun l => (target.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[71,17,0,53,99,0,0,0] ∧
 locations.attach.map (fun l => (selfTargetLeaf.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[71,17,0,53,99,0,0,0] ∧
 locations.attach.map (fun l => (selfTargetMap.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[71,17,0,53,99,0,0,0] ∧
 {selfTargetLeaf with store:=target.store}=target ∧
 {selfTargetMap with store:=target.store}=target := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,by decide,by decide,by decide,rfl,rfl⟩

theorem child_presence : recursiveCopy leaf leaf=leaf ∧ fixedView leaf ⟨1,by decide⟩=.absent ∧
 fixedView (recursiveCopy leaf leaf) ⟨1,by decide⟩=.absent ∧
 fixedView old ⟨1,by decide⟩=.absent ∧
 (result.find pre).map (fun (v : Value graph T) => fixedView (T:=T) v ⟨1,by decide⟩)=some .absent := by
 exact ⟨value_self leaf,rfl,rfl,rfl,rfl⟩

private def badStore := Representation.write captured (.root 1) (w 0)
private def badNumeric := writeWord initial 1 (w 0)
private noncomputable def badTarget := {target with store:=Evm.WordStore.write target.store (.root 1) 0}
theorem wrong_clear : Evm.run (mapCode++TargetOperations.writeCode (.root 1) (w 0)) target=.ok badTarget 0 ∧
 locations.map (fun l => (badStore l).val)=[71,0,0,53,99,0,0,0] ∧
 locations.map (fun l => (badNumeric (l.word 64 hash)).val)=[71,0,0,53,99,0,0,0] ∧
 locations.attach.map (fun l => (badTarget.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[71,0,0,53,99,0,0,0] ∧
 {badTarget with store:=target.store}=target ∧ badTarget.store (.root 1)≠target.store (.root 1) ∧
 ¬ Represented leaf (queries .nil indices) (.root 1) badStore := by
 refine ⟨?_,rfl,rfl,by decide,rfl,by decide,?_⟩
 · unfold mapCode
   rw [Evm.run_append_ok (run_self .uint size target slot)]
   exact TargetOperations.run_write _ _ _
 · intro alleged
   have member : (PrimitiveSnapshotOwner.query (G:=graph) (p:=PrimTy.uint) ⟨0,by decide⟩).prefix .nil ∈ queries .nil indices := by
    apply List.mem_map.mpr
    refine ⟨PrimitiveSnapshotOwner.query ⟨0,by decide⟩,?_,rfl⟩
    apply List.mem_map.mpr
    exact ⟨⟨0,by decide⟩,by decide,rfl⟩
   have bad:=(alleged _ member).2.2 (w 17) rfl
   have impossible:=congrArg (fun w : Semantics.Word => w.val) bad
   change (0:Int)=17 at impossible
   omega

private def emptyRoot : Value graph (.array T) := .array ⟨0,by decide⟩ (ix 0) (by decide) (fun i => Fin.elim0 i)
private def missing : TypeGraph.Path graph (.array T) T := .cons (.index (ix 0)) .nil
theorem failed_path : emptyRoot.find missing=none ∧ recursiveCopyAt emptyRoot missing missing=none ∧
 Evm.run (TargetFixedSnapshot.code .uint size (.data (.root 0) 0) (.data (.root 0) 0)) target=.ok target 0 := by
 exact ⟨rfl,rfl,run_self _ _ _ _⟩

/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSelf.Controls.leaf_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms leaf_certificate
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSelf.Controls.mapping_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_certificate
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSelf.Controls.raw_materialization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms raw_materialization
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSelf.Controls.graph_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms graph_ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSelf.Controls.physical_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms physical_ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSelf.Controls.child_presence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms child_presence
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSelf.Controls.wrong_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_clear
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSelf.Controls.failed_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failed_path
end Solidity.Backend.StorageOps.PrimitiveSnapshotSelf.Controls
