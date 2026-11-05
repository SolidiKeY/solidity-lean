import Solidity.Backend.StorageOps.PrimitiveSnapshotRoot

/-! Captured fixed ROOT copy at a retained destination. Complete logical,
symbolic, numeric and actual target observations keep liveness distinct. -/
namespace Solidity.Backend.StorageOps.PrimitiveSnapshotRoot.Controls
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
private def size : FixedSize := ⟨3,by decide⟩
private def ix (i : Fin 4) : Index := ⟨i.val,by have bound:=i.isLt; omega⟩
private def w (x : Fin 256) : Semantics.Word := lengthWord x.val (by have bound:=x.isLt; omega)

private abbrev T : TypeGraph.Ty 0 := .fixed (.prim .uint) size
private def leaf (a b c : Semantics.Word) : Value graph T := .fixed fun i =>
 if i.val=1 then (if b.val=0 then .absent else .present (.prim b)) else .present (.prim (if i.val=0 then a else c))
private def old : Value graph T := leaf (w 53) (w 0) (w 71)
private def root : Value graph (.array T) := .array ⟨2,by decide⟩ (ix 1) (by decide)
 (fun i => .present (if i.val=0 then leaf (w 7) (w 17) (w 23) else old))
private def pre : TypeGraph.Path graph (.array T) T := .cons (.index (ix 1)) .nil
private def dst := pre.append (TargetFixedPrimitive.path (p:=PrimTy.uint) (ix 1))
private def path (a b : Fin 4) : TypeGraph.Path graph (.array T) (.prim .uint) :=
 .cons (.index (ix a)) (TargetFixedPrimitive.path (ix b))
private def q (a b : Fin 4) : Query graph (.array T) := .word (path a b)
private def contexts := [q 0 1,q 1 0,q 1 2]
private def observations := [.length .nil,q 0 0,q 0 1,q 0 2,q 1 0,q 1 1,q 1 2,q 1 3,q 2 0]
private def base : Solidity.Storage.Loc := .root 0
private def part (i : Nat) : Solidity.Storage.Loc := .data base i
private def locations := [base,.root 1,part 0,part 1,part 2,part 3,part 4,part 5,part 6,part 7,part 8]
private def hash (_ : Solidity.Storage.Pre) : Nat := 16
private def store : Store := fun l => if l=base then w 1 else if l=.root 1 then w 109 else
 if l=part 0 then w 7 else if l=part 1 then w 17 else if l=part 2 then w 23 else
 if l=part 3 then w 53 else if l=part 5 then w 71 else if l=part 6 then w 87 else if l=part 8 then w 99 else w 0
private def numeric : WordStore := fun a => if a=0 then w 1 else if a=1 then w 109 else
 if a=16 then w 7 else if a=17 then w 17 else if a=18 then w 23 else
 if a=19 then w 53 else if a=21 then w 71 else if a=22 then w 87 else if a=24 then w 99 else w 0
private noncomputable def target : Evm.Machine :=
 {Evm.Machine.init (fun _ => 19) ⟨7,by decide⟩ with
 store:=⟨fun slot => TargetOperations.encodeWord (store (Solidity.Storage.ofSlot slot))⟩
 stack:=[.val ⟨23,by decide⟩,.slot (.root 9)]
 mem:=fun _ => .val ⟨31,by decide⟩
 caller:=⟨13,by decide⟩
 timestamp:=⟨53,by decide⟩}
private theorem finite : FiniteRun 64 16 2 hash [.data 0] locations := by
 constructor
 · intro p; change 16<64; decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [part,base,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
private theorem transported : Transport 64 hash locations store numeric := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
private theorem fitting : ∀ l ∈ locations,TargetOperations.KeysFit l := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact True.intro
private theorem agreement : ∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (store l) := by
 intro l member
 change TargetOperations.encodeWord (store (Solidity.Storage.ofSlot (TargetOperations.toSlot l (fitting l member))))=_
 rw [TargetOperations.ofSlot_toSlot]

private def sourcePre : TypeGraph.Path graph (.array T) T := .cons (.index (ix 0)) .nil
private def snapshot : Value graph T := leaf (w 7) (w 17) (w 23)
private def result := (recursiveCopyAt root pre sourcePre).getD root
private def indices : List (Fin size.val) := [⟨2,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩]
private def qs := indices.map (PrimitiveSnapshotOwner.query (G:=graph) (p:=PrimTy.uint))
private def afterStore := PrimitiveSnapshotNumeric.symbolic store (part 3) (part 0) 3
private def afterNumeric := PrimitiveSnapshotNumeric.numeric 64 hash numeric (part 3) (part 0) 3
private noncomputable def output := TargetFixedSnapshot.afterCopy .uint size target (.data (.root 0) 0) (.data (.root 0) 3)
private theorem sourceOwner : Represented root (qs.map (Query.prefix sourcePre)) base store := by
 intro query member
 change query ∈ (indices.map (PrimitiveSnapshotOwner.query (G:=graph) (p:=PrimTy.uint))).map (Query.prefix sourcePre) at member
 obtain ⟨q,outerMember,rfl⟩:=List.mem_map.mp member
 change q ∈ indices.map (PrimitiveSnapshotOwner.query (G:=graph) (p:=PrimTy.uint)) at outerMember
 obtain ⟨i,innerMember,rfl⟩:=List.mem_map.mp outerMember
 change i ∈ indices at innerMember
 simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at innerMember
 rcases innerMember with rfl|rfl|rfl|rfl
 all_goals refine ⟨?_,True.intro,?_⟩
 all_goals first
  | (change 0<lmax ∧ (2<size.val ∧ True); decide)
  | (change 0<lmax ∧ (0<size.val ∧ True); decide)
  | (change 0<lmax ∧ (1<size.val ∧ True); decide)
  | (intro value observed; have same:=Option.some.inj observed; subst value; rfl)
private theorem sourceCovered : ∀ i<size.val,(pathLoc sourcePre base).add i ∈ locations := by
 intro i inside
 have cases : i=0 ∨ i=1 ∨ i=2 := by change i<3 at inside; omega
 rcases cases with rfl|rfl|rfl <;> decide
private theorem dstCovered : ∀ i<size.val,(pathLoc pre base).add i ∈ locations := by
 intro i inside
 have cases : i=0 ∨ i=1 ∨ i=2 := by change i<3 at inside; omega
 rcases cases with rfl|rfl|rfl <;> decide

theorem certificate : result.find pre=some (recursiveCopy old snapshot) ∧
 Represented result (qs.map (Query.prefix pre)) base afterStore ∧
 Transport 64 hash locations afterStore afterNumeric ∧
 Evm.run (TargetFixedSnapshot.code .uint size (.data (.root 0) 0) (.data (.root 0) 3)) target=.ok output 0 ∧
 (∀ l (member : l ∈ locations),output.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (afterNumeric (l.word 64 hash))) := by
 exact complete finite root result pre sourcePre old snapshot rfl rfl rfl (by change 1<lmax ∧ True; decide)
  indices base True.intro store numeric target transported sourceOwner sourceCovered dstCovered fitting agreement

theorem graph_ordered :
 observations.map (fun q => (q.read root).map Subtype.val)=[some 1,some 7,some 17,some 23,some 53,some 0,some 71,none,none] ∧
 observations.map (fun q => (q.read result).map Subtype.val)=[some 1,some 7,some 17,some 23,some 7,some 17,some 23,none,none] ∧
 (qs.map (Query.prefix pre)).map (fun q => (q.read result).map Subtype.val)=[some 23,some 7,some 17,some 23] := ⟨rfl,rfl,rfl⟩

theorem storage_ordered :
 locations.map (fun l => (store l).val)=[1,109,7,17,23,53,0,71,87,0,99] ∧
 locations.map (fun l => (numeric (l.word 64 hash)).val)=[1,109,7,17,23,53,0,71,87,0,99] ∧
 locations.map (fun l => (afterStore l).val)=[1,109,7,17,23,7,17,23,87,0,99] ∧
 locations.map (fun l => (afterNumeric (l.word 64 hash)).val)=[1,109,7,17,23,7,17,23,87,0,99] ∧
 locations.attach.map (fun l => (target.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[1,109,7,17,23,53,0,71,87,0,99] ∧
 locations.attach.map (fun l => (output.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[1,109,7,17,23,7,17,23,87,0,99] ∧
 {output with store:=target.store}=target := by exact ⟨rfl,rfl,rfl,rfl,by decide,by decide,rfl⟩

theorem retained_not_live : root.find pre=some old ∧ pre.readLive Value.dflt root=none ∧
 pre.readLive Value.dflt result=none ∧ result.length=root.length ∧ result.extent=root.extent := ⟨rfl,rfl,rfl,rfl,rfl⟩

private def missing : TypeGraph.Path graph (.array T) T := .cons (.index (ix 3)) .nil
theorem missing_failure : root.find missing=none ∧ recursiveCopyAt root missing sourcePre=none ∧
 recursiveCopyAt root pre missing=none := ⟨rfl,rfl,rfl⟩

theorem wrong_direction :
 (recursiveCopyAt root sourcePre pre).map (fun r => observations.map (fun q => (q.read r).map Subtype.val))=
 some [some 1,some 53,some 0,some 71,some 53,some 0,some 71,none,none] ∧
 (recursiveCopyAt root sourcePre pre).map (fun r => (q 0 0).read r) ≠ some ((q 0 0).read result) := by
 exact ⟨rfl,by intro same; have impossible:=Option.some.inj (Option.some.inj same); have wordEq:=congrArg (fun w : Semantics.Word => w.val) impossible; change (53:Int)=7 at wordEq; omega⟩

private noncomputable def wrongOutput := TargetFixedSnapshot.afterCopy .uint size target (.data (.root 0) 3) (.data (.root 0) 0)
theorem wrong_target_direction :
 Evm.run (TargetFixedSnapshot.code .uint size (.data (.root 0) 3) (.data (.root 0) 0)) target=.ok wrongOutput 0 ∧
 locations.attach.map (fun l => (wrongOutput.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[1,109,53,0,71,53,0,71,87,0,99] ∧
 {wrongOutput with store:=target.store}=target := by
 exact ⟨TargetFixedSnapshot.run_code _ _ _ _ _,by decide,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRoot.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRoot.Controls.graph_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms graph_ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRoot.Controls.storage_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms storage_ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRoot.Controls.retained_not_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms retained_not_live
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRoot.Controls.missing_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms missing_failure
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRoot.Controls.wrong_direction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_direction
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRoot.Controls.wrong_target_direction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_target_direction
end Solidity.Backend.StorageOps.PrimitiveSnapshotRoot.Controls
