import Solidity.Backend.StorageOps.PrimitiveSnapshotFrames

/-! Captured fixed ROOT copy at a retained destination. Complete logical,
symbolic, numeric and actual target observations keep liveness distinct. -/
namespace Solidity.Backend.StorageOps.PrimitiveSnapshotFrames.Controls
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

private def frames : List (Query graph (.array T)) := [q 0 2,q 0 0,q 2 0,q 0 2]
private theorem frameOwner : Represented root frames base store := by
 intro query member
 simp only [frames,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl
 all_goals refine ⟨?_,True.intro,?_⟩
 all_goals first
  | (change 0<lmax ∧ (2<size.val ∧ True); decide)
  | (change 0<lmax ∧ (0<size.val ∧ True); decide)
  | (change 2<lmax ∧ (0<size.val ∧ True); decide)
  | (intro value observed; have same:=Option.some.inj observed; subst value; rfl)
  | (intro value observed; cases observed)
private theorem apart : ∀ q ∈ frames,q.apart pre := by
 intro query member
 simp only [frames,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl
 all_goals apply Apart.fork (StepApart.index _ _ (by decide))
private theorem outside : ∀ q ∈ frames,∀ i<size.val,q.location base≠(pathLoc pre base).add i := by
 intro query member i inside
 have cases : i=0 ∨ i=1 ∨ i=2 := by change i<3 at inside; omega
 simp only [frames,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl <;> rcases cases with rfl|rfl|rfl <;> decide
private theorem oldHeader : Represented root [.length .nil] base store := by
 intro query member
 have same : query=.length .nil := List.mem_singleton.mp member
 subst query
 refine ⟨True.intro,?_,?_⟩
 · change 1≤lmax ∧ 2≤lmax; decide
 · intro value observed
   have same:=Option.some.inj observed
   subst value
   rfl

theorem certificate : result.find pre=some (recursiveCopy old snapshot) ∧
 Represented result ((qs.map (Query.prefix pre))++frames) base afterStore ∧
 Transport 64 hash locations afterStore afterNumeric ∧
 Evm.run (TargetFixedSnapshot.code .uint size (.data (.root 0) 0) (.data (.root 0) 3)) target=.ok output 0 ∧
 (∀ l (member : l ∈ locations),output.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (afterNumeric (l.word 64 hash))) := by
 exact complete finite root result pre sourcePre old snapshot rfl rfl rfl (by change 1<lmax ∧ True; decide)
  indices frames base True.intro store numeric target transported sourceOwner frameOwner apart outside sourceCovered dstCovered fitting agreement

theorem header_owner : Represented result [.length .nil] base afterStore := by
 exact represented_header root result .nil (ix 1) .nil sourcePre old snapshot rfl rfl rfl base store oldHeader
  (by
   intro i _
   change (Solidity.Storage.Loc.root 0)≠.data (.root 0) (3+i)
   intro same
   cases same)

theorem whole_owner : Represented result (.length .nil::(qs.map (Query.prefix pre))++frames) base afterStore := by
 intro query member
 rcases List.mem_cons.mp member with first|later
 · exact header_owner query (List.mem_singleton.mpr first)
 · exact certificate.2.1 query later

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

theorem frame_ordered :
 frames.map (fun q => (q.read root).map Subtype.val)=[some 23,some 7,none,some 23] ∧
 frames.map (fun q => (q.read result).map Subtype.val)=[some 23,some 7,none,some 23] ∧
 frames.map (fun q => (store (q.location base)).val)=[23,7,87,23] ∧
 frames.map (fun q => (afterStore (q.location base)).val)=[23,7,87,23] ∧
 frames.map (fun q => (afterNumeric ((q.location base).word 64 hash)).val)=[23,7,87,23] := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem inside_not_frame : ¬ Represented result [q 1 0] base store := by
 intro alleged
 have bad:=(alleged (q 1 0) (List.mem_singleton.mpr rfl)).2.2 (w 7) rfl
 have impossible:=congrArg (fun w : Semantics.Word => w.val) bad
 change (53:Int)=7 at impossible
 omega

private def wrongStore := Representation.write afterStore base (w 0)
private noncomputable def wrongOutput := {output with store:=Evm.WordStore.write output.store (.root 0) (TargetOperations.encodeWord (w 0)).val}
theorem wrong_header_clear :
 Evm.run (TargetFixedSnapshot.code .uint size (.data (.root 0) 0) (.data (.root 0) 3) ++ TargetOperations.writeCode (.root 0) (w 0)) target=.ok wrongOutput 0 ∧
 locations.attach.map (fun l => (wrongOutput.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[0,109,7,17,23,7,17,23,87,0,99] ∧
 locations.map (fun l => (wrongStore l).val)=[0,109,7,17,23,7,17,23,87,0,99] ∧
 (Query.length .nil).read result=some (w 1) ∧
 ¬ Represented result [.length .nil] base wrongStore := by
 refine ⟨?_,by decide,rfl,rfl,?_⟩
 · rw [Evm.run_append_ok (TargetFixedSnapshot.run_code _ _ _ _ _)]
   exact TargetOperations.run_write _ _ _
 · intro alleged
   have bad:=(alleged (.length .nil) (List.mem_singleton.mpr rfl)).2.2 (w 1) rfl
   have impossible:=congrArg (fun w : Semantics.Word => w.val) bad
   change (0:Int)=1 at impossible
   omega

/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotFrames.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotFrames.Controls.header_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms header_owner
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotFrames.Controls.whole_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms whole_owner
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotFrames.Controls.graph_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms graph_ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotFrames.Controls.storage_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms storage_ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotFrames.Controls.retained_not_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms retained_not_live
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotFrames.Controls.frame_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms frame_ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotFrames.Controls.inside_not_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms inside_not_frame
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotFrames.Controls.wrong_header_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_header_clear
end Solidity.Backend.StorageOps.PrimitiveSnapshotFrames.Controls
