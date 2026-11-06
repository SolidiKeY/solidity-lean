import Solidity.Backend.StorageOps.PrimitiveSnapshotSequence
import Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation

/-! Actual two-copy ROOT clients with retained sources/destinations and complete observations. -/
namespace Solidity.Backend.StorageOps.PrimitiveSnapshotSequence.Controls
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
private def ix (i : Fin 5) : Index := ⟨i.val,by have bound:=i.isLt; omega⟩
private def w (x : Fin 256) : Semantics.Word := lengthWord x.val (by have bound:=x.isLt; omega)

private abbrev T : TypeGraph.Ty 0 := .fixed (.prim .uint) size
private def leaf (a b c : Semantics.Word) : Value graph T := .fixed fun i =>
 if i.val=1 then (if b.val=0 then .absent else .present (.prim b)) else .present (.prim (if i.val=0 then a else c))
private def snapshotA := leaf (w 7) (w 17) (w 23)
private def oldA := leaf (w 53) (w 0) (w 71)
private def snapshotB := leaf (w 87) (w 0) (w 99)
private def oldB := leaf (w 101) (w 109) (w 127)
private def root : Value graph (.array T) := .array ⟨4,by decide⟩ (ix 2) (by decide)
 (fun i => .present (if i.val=0 then snapshotA else if i.val=1 then oldA else if i.val=2 then snapshotB else oldB))
private def pre (i : Fin 5) : TypeGraph.Path graph (.array T) T := .cons (.index (ix i)) .nil
private def da := pre 1
private def sa := pre 0
private def db := pre 3
private def sb := pre 2
private def path (a b : Fin 5) : TypeGraph.Path graph (.array T) (.prim .uint) :=
 .cons (.index (ix a)) (TargetFixedPrimitive.path (ix b))
private def q (a b : Fin 5) : Query graph (.array T) := .word (path a b)
private def frames : List (Query graph (.array T)) := [q 0 0,q 4 0,q 0 2,q 0 0]
private def indices : List (Fin size.val) := [⟨2,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩]
private def middle := (recursiveCopyAt root da sa).getD root
private def result := (recursiveCopyAt middle db sb).getD middle
private def base : Solidity.Storage.Loc := .root 0
private def part (i : Nat) : Solidity.Storage.Loc := .data base i
private def locations : List Solidity.Storage.Loc := [base,.root 1,part 0,part 1,part 2,part 3,part 4,part 5,part 6,part 7,part 8,part 9,part 10,part 11,part 12,part 13,part 14]
private def hash (_ : Solidity.Storage.Pre) : Nat := 16
private def captured : Store := fun l => if l=base then w 2 else if l=.root 1 then w 211 else
 if l=part 0 then w 7 else if l=part 1 then w 17 else if l=part 2 then w 23 else if l=part 3 then w 53 else if l=part 4 then w 0 else if l=part 5 then w 71 else if l=part 6 then w 87 else if l=part 7 then w 0 else if l=part 8 then w 99 else if l=part 9 then w 101 else if l=part 10 then w 109 else if l=part 11 then w 127 else if l=part 12 then w 131 else if l=part 13 then w 149 else if l=part 14 then w 151 else w 0
private def initial : WordStore := fun a => if a<16 then captured (.root a) else captured (part (a-16))
private noncomputable def target : Evm.Machine :=
 {Evm.Machine.init (fun _ => 19) ⟨7,by decide⟩ with
 store:=⟨fun slot => TargetOperations.encodeWord (captured (Solidity.Storage.ofSlot slot))⟩
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
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [part,base,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
private theorem before : Transport 64 hash locations captured initial := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
private theorem fitting : ∀ l ∈ locations,TargetOperations.KeysFit l := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact True.intro
private theorem agreement : ∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (initial (l.word 64 hash)) := by
 intro l member
 change TargetOperations.encodeWord (captured (Solidity.Storage.ofSlot (TargetOperations.toSlot l (fitting l member))))=_
 rw [TargetOperations.ofSlot_toSlot,← before l member]
private theorem covered (offset : Nat) (bound : offset+3≤15) : ∀ i<size.val,(part offset).add i ∈ locations := by
 intro i inside
 change i<3 at inside
 have cases : offset+i=0 ∨ offset+i=1 ∨ offset+i=2 ∨ offset+i=3 ∨ offset+i=4 ∨ offset+i=5 ∨ offset+i=6 ∨ offset+i=7 ∨ offset+i=8 ∨ offset+i=9 ∨ offset+i=10 ∨ offset+i=11 ∨ offset+i=12 ∨ offset+i=13 ∨ offset+i=14 := by omega
 change Solidity.Storage.Loc.data base (offset+i) ∈ locations
 rcases cases with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> rw [h] <;> decide
private theorem sourceA : Represented root (queries sa indices) base captured := by
 intro query member
 simp only [queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl
 all_goals refine ⟨?_,True.intro,?_⟩
 all_goals first
  | (change 0<lmax ∧ (2<size.val ∧ True); decide)
  | (change 0<lmax ∧ (0<size.val ∧ True); decide)
  | (change 0<lmax ∧ (1<size.val ∧ True); decide)
  | (intro value observed; have same:=Option.some.inj observed; subst value; rfl)
private theorem oldFrames : Represented root (queries sb indices++frames) base captured := by
 intro query member
 simp only [queries,indices,frames,List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with (rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl)
 all_goals refine ⟨?_,True.intro,?_⟩
 all_goals first
  | (change 2<lmax ∧ (2<size.val ∧ True); decide)
  | (change 2<lmax ∧ (0<size.val ∧ True); decide)
  | (change 2<lmax ∧ (1<size.val ∧ True); decide)
  | (change 0<lmax ∧ (0<size.val ∧ True); decide)
  | (change 0<lmax ∧ (2<size.val ∧ True); decide)
  | (change 4<lmax ∧ (0<size.val ∧ True); decide)
  | (intro value observed; have same:=Option.some.inj observed; subst value; rfl)
  | (intro value observed; cases observed)
private theorem apartA : ∀ q ∈ queries sb indices++frames,q.apart da := by
 intro query member
 simp only [queries,indices,frames,List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with (rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl)
 all_goals apply Apart.fork (StepApart.index _ _ (by decide))
private theorem outsideA : ∀ q ∈ queries sb indices++frames,∀ i<size.val,q.location base≠(pathLoc da base).add i := by
 intro query member i inside
 have cases : i=0 ∨ i=1 ∨ i=2 := by change i<3 at inside; omega
 simp only [queries,indices,frames,List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with (rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl) <;> rcases cases with rfl|rfl|rfl <;> decide
private theorem apartB : ∀ q ∈ queries da indices++frames,q.apart db := by
 intro query member
 simp only [queries,indices,frames,List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with (rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl)
 all_goals apply Apart.fork (StepApart.index _ _ (by decide))
private theorem outsideB : ∀ q ∈ queries da indices++frames,∀ i<size.val,q.location base≠(pathLoc db base).add i := by
 intro query member i inside
 have cases : i=0 ∨ i=1 ∨ i=2 := by change i<3 at inside; omega
 simp only [queries,indices,frames,List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with (rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl) <;> rcases cases with rfl|rfl|rfl <;> decide
private def storeA := PrimitiveSnapshotNumeric.symbolic captured (part 3) (part 0) 3
private def numericA := PrimitiveSnapshotNumeric.numeric 64 hash initial (part 3) (part 0) 3
private noncomputable def targetA := TargetFixedSnapshot.afterCopy .uint size target (.data (.root 0) 0) (.data (.root 0) 3)
private def finalStore := PrimitiveSnapshotNumeric.symbolic storeA (part 9) (part 6) 3
private def finalNumeric := PrimitiveSnapshotNumeric.numeric 64 hash numericA (part 9) (part 6) 3
private noncomputable def finalTarget := TargetFixedSnapshot.afterCopy .uint size targetA (.data (.root 0) 6) (.data (.root 0) 9)
private def codeA := TargetFixedSnapshot.code .uint size (.data (.root 0) 0) (.data (.root 0) 3)
private def codeB := TargetFixedSnapshot.code .uint size (.data (.root 0) 6) (.data (.root 0) 9)

theorem certificate : result.find db=some (recursiveCopy oldB snapshotB) ∧
 Represented result (queries db indices++(queries da indices++frames)) base finalStore ∧
 Transport 64 hash locations finalStore finalNumeric ∧ Evm.run (codeA++codeB) target=.ok finalTarget 0 ∧
 (∀ l (member : l ∈ locations),finalTarget.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (finalNumeric (l.word 64 hash))) := by
 exact complete finite root middle result da sa db sb oldA snapshotA oldB snapshotB rfl rfl rfl rfl rfl rfl
  (by change 1<lmax ∧ True; decide) (by change 3<lmax ∧ True; decide) indices indices frames base True.intro captured initial target before sourceA oldFrames apartA outsideA apartB outsideB
  (covered 3 (by decide)) (covered 0 (by decide)) (covered 9 (by decide)) (covered 6 (by decide)) fitting agreement

private theorem oldHeader : Represented root [.length .nil] base captured := by
 intro query member
 have same : query=.length .nil := List.mem_singleton.mp member
 subst query
 refine ⟨True.intro,?_,?_⟩
 · change 2≤lmax ∧ 4≤lmax; decide
 · intro value observed; have same:=Option.some.inj observed; subst value; rfl

theorem header_owner : Represented result [.length .nil] base finalStore := by
 exact headers root middle result .nil (ix 1) (ix 3) .nil .nil sa sb oldA snapshotA oldB snapshotB rfl rfl rfl rfl rfl rfl base captured oldHeader
  (by intro i _; change (Solidity.Storage.Loc.root 0)≠.data (.root 0) (3+i); intro same; cases same)
  (by intro i _; change (Solidity.Storage.Loc.root 0)≠.data (.root 0) (9+i); intro same; cases same)

theorem whole_owner : Represented result (.length .nil::queries db indices++(queries da indices++frames)) base finalStore := by
 intro query member
 rcases List.mem_cons.mp member with header|copied
 · exact header_owner query (List.mem_singleton.mpr header)
 · exact certificate.2.1 query copied

private def observations : List (Query graph (.array T)) :=
 [.length .nil,q 0 0,q 0 1,q 0 2,q 1 0,q 1 1,q 1 2,q 2 0,q 2 1,q 2 2,q 3 0,q 3 1,q 3 2,q 1 3,q 4 0]
theorem graph_ordered :
 observations.map (fun q => (q.read root).map Subtype.val)=[some 2,some 7,some 17,some 23,some 53,some 0,some 71,some 87,some 0,some 99,some 101,some 109,some 127,none,none] ∧
 observations.map (fun q => (q.read middle).map Subtype.val)=[some 2,some 7,some 17,some 23,some 7,some 17,some 23,some 87,some 0,some 99,some 101,some 109,some 127,none,none] ∧
 observations.map (fun q => (q.read result).map Subtype.val)=[some 2,some 7,some 17,some 23,some 7,some 17,some 23,some 87,some 0,some 99,some 87,some 0,some 99,none,none] ∧
 (.length .nil::queries db indices++(queries da indices++frames)).map (fun q => (q.read result).map Subtype.val)=[some 2,some 99,some 87,some 0,some 99,some 23,some 7,some 17,some 23,some 7,none,some 23,some 7] := ⟨rfl,rfl,rfl,rfl⟩

theorem storage_ordered :
 locations.map (fun l => (captured l).val)=[2,211,7,17,23,53,0,71,87,0,99,101,109,127,131,149,151] ∧
 locations.map (fun l => (storeA l).val)=[2,211,7,17,23,7,17,23,87,0,99,101,109,127,131,149,151] ∧
 locations.map (fun l => (finalStore l).val)=[2,211,7,17,23,7,17,23,87,0,99,87,0,99,131,149,151] ∧
 locations.map (fun l => (initial (l.word 64 hash)).val)=[2,211,7,17,23,53,0,71,87,0,99,101,109,127,131,149,151] ∧
 locations.map (fun l => (numericA (l.word 64 hash)).val)=[2,211,7,17,23,7,17,23,87,0,99,101,109,127,131,149,151] ∧
 locations.map (fun l => (finalNumeric (l.word 64 hash)).val)=[2,211,7,17,23,7,17,23,87,0,99,87,0,99,131,149,151] ∧
 locations.attach.map (fun l => (target.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[2,211,7,17,23,53,0,71,87,0,99,101,109,127,131,149,151] ∧
 locations.attach.map (fun l => (targetA.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[2,211,7,17,23,7,17,23,87,0,99,101,109,127,131,149,151] ∧
 locations.attach.map (fun l => (finalTarget.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[2,211,7,17,23,7,17,23,87,0,99,87,0,99,131,149,151] ∧
 {targetA with store:=target.store}=target ∧
 {finalTarget with store:=target.store}=target := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,by decide,by decide,by decide,rfl,rfl⟩

theorem retained_and_presence : sb.readLive Value.dflt root=none ∧ db.readLive Value.dflt root=none ∧
 sb.readLive Value.dflt result=none ∧ db.readLive Value.dflt result=none ∧ result.length=root.length ∧ result.extent=root.extent ∧
 fixedView snapshotB ⟨1,by decide⟩=.absent ∧
 (result.find db).map (fun (v : Value graph T) => fixedView (T:=T) v ⟨1,by decide⟩)=some (.present (.prim (w 0))) := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem failures_and_raw : root.find (pre 4)=none ∧ recursiveCopyAt middle (pre 4) sb=none ∧
 recursiveCopyAt middle db (pre 4)=none ∧ (q 4 0).read result=none ∧
 Evm.run (TargetOperations.readCode (.data (.root 0) 12)) finalTarget=
 .ok {finalTarget with stack:=.val (TargetOperations.encodeWord (w 131))::finalTarget.stack} 0 := ⟨rfl,rfl,rfl,rfl,rfl⟩

private def wrongRoot := (recursiveCopyAt middle db da).getD middle
private def wrongStore := PrimitiveSnapshotNumeric.symbolic storeA (part 9) (part 3) 3
private def wrongNumeric := PrimitiveSnapshotNumeric.numeric 64 hash numericA (part 9) (part 3) 3
private noncomputable def wrongTarget := TargetFixedSnapshot.afterCopy .uint size targetA (.data (.root 0) 3) (.data (.root 0) 9)
private def wrongCode := TargetFixedSnapshot.code .uint size (.data (.root 0) 3) (.data (.root 0) 9)
theorem wrong_source : recursiveCopyAt middle db da=some wrongRoot ∧
 observations.map (fun q => (q.read wrongRoot).map Subtype.val)=[some 2,some 7,some 17,some 23,some 7,some 17,some 23,some 87,some 0,some 99,some 7,some 17,some 23,none,none] ∧
 Evm.run (codeA++wrongCode) target=.ok wrongTarget 0 ∧
 locations.map (fun l => (wrongStore l).val)=[2,211,7,17,23,7,17,23,87,0,99,7,17,23,131,149,151] ∧
 locations.map (fun l => (wrongNumeric (l.word 64 hash)).val)=[2,211,7,17,23,7,17,23,87,0,99,7,17,23,131,149,151] ∧
 locations.attach.map (fun l => (wrongTarget.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[2,211,7,17,23,7,17,23,87,0,99,7,17,23,131,149,151] ∧
 {wrongTarget with store:=target.store}=target ∧ ¬ Represented result (queries db indices) base wrongStore := by
 refine ⟨rfl,rfl,?_,rfl,rfl,by decide,rfl,?_⟩
 · unfold codeA wrongCode
   rw [Evm.run_append_ok (TargetFixedSnapshot.run_code .uint size target (.data (.root 0) 0) (.data (.root 0) 3))]
   exact TargetFixedSnapshot.run_code _ _ _ _ _
 · intro alleged
   have bad:=(alleged ((PrimitiveSnapshotOwner.query (G:=graph) (p:=PrimTy.uint) ⟨0,by decide⟩).prefix db) (by
    simp only [queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false]
    exact Or.inr (Or.inl True.intro))).2.2 (w 87) rfl
   have impossible:=congrArg (fun w : Semantics.Word => w.val) bad
   change (7:Int)=87 at impossible
   omega

/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSequence.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSequence.Controls.header_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms header_owner
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSequence.Controls.whole_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms whole_owner
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSequence.Controls.graph_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms graph_ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSequence.Controls.storage_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms storage_ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSequence.Controls.retained_and_presence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms retained_and_presence
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSequence.Controls.failures_and_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failures_and_raw
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSequence.Controls.wrong_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_source
end Solidity.Backend.StorageOps.PrimitiveSnapshotSequence.Controls
