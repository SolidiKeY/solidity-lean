import Solidity.Backend.StorageOps.PrimitiveSnapshotDependent
import Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation

/-! Actual two-copy ROOT clients with retained sources/destinations and complete observations. -/
namespace Solidity.Backend.StorageOps.PrimitiveSnapshotDependent.Controls
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
private def leaf (a b c : Semantics.Word) : Value graph T := .fixed fun i =>
 if i.val=1 then (if b.val=0 then .absent else .present (.prim b)) else .present (.prim (if i.val=0 then a else c))
private def snapshotA := leaf (w 7) (w 0) (w 23)
private def oldA := leaf (w 53) (w 0) (w 71)
private def shadow := leaf (w 87) (w 0) (w 99)
private def oldB := leaf (w 101) (w 109) (w 127)
private def snapshotB := recursiveCopy oldA snapshotA
private def root : Value graph (.array T) := .array ⟨4,by decide⟩ (ix 2) (by decide)
 (fun i => .present (if i.val=0 then snapshotA else if i.val=1 then oldA else if i.val=2 then shadow else oldB))
private def pre (i : Fin 5) : TypeGraph.Path graph (.array T) T := .cons (.index (ix i)) .nil
private def da := pre 1
private def sa := pre 0
private def db := pre 3
private def sb := da
private def path (a b : Fin 5) : TypeGraph.Path graph (.array T) (.prim .uint) :=
 .cons (.index (ix a)) (TargetFixedPrimitive.path (ix b))
private def q (a b : Fin 5) : Query graph (.array T) := .word (path a b)
private def frames : List (Query graph (.array T)) := [q 0 0,q 4 0,q 0 2,q 0 0]
private def indicesA : List (Fin size.val) := [⟨2,by decide⟩,⟨0,by decide⟩]
private def indicesB : List (Fin size.val) := [⟨1,by decide⟩,⟨2,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩]
private def middle := (recursiveCopyAt root da sa).getD root
private def result := (recursiveCopyAt middle db sb).getD middle
private def base : Solidity.Storage.Loc := .root 0
private def part (i : Nat) : Solidity.Storage.Loc := .data base i
private def locations : List Solidity.Storage.Loc := [base,.root 1,part 0,part 1,part 2,part 3,part 4,part 5,part 6,part 7,part 8,part 9,part 10,part 11,part 12,part 13,part 14]
private def hash (_ : Solidity.Storage.Pre) : Nat := 16
private def captured : Store := fun l => if l=base then w 2 else if l=.root 1 then w 211 else
 if l=part 0 then w 7 else if l=part 1 then w 0 else if l=part 2 then w 23 else if l=part 3 then w 53 else if l=part 4 then w 0 else if l=part 5 then w 71 else if l=part 6 then w 87 else if l=part 7 then w 0 else if l=part 8 then w 99 else if l=part 9 then w 101 else if l=part 10 then w 109 else if l=part 11 then w 127 else if l=part 12 then w 131 else if l=part 13 then w 149 else if l=part 14 then w 151 else w 0
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
private theorem sourceA : Represented root (queries sa (indicesA++indicesB)) base captured := by
 intro query member
 change query ∈ queries sa [⟨2,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩] at member
 simp only [queries,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl
 all_goals refine ⟨?_,True.intro,?_⟩
 all_goals first
  | (change 0<lmax ∧ (2<size.val ∧ True); decide)
  | (change 0<lmax ∧ (0<size.val ∧ True); decide)
  | (change 0<lmax ∧ (1<size.val ∧ True); decide)
  | (intro value observed; have same:=Option.some.inj observed; subst value; rfl)
private theorem oldFrames : Represented root frames base captured := by
 intro query member
 simp only [frames,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl
 all_goals refine ⟨?_,True.intro,?_⟩
 all_goals first
  | (change 0<lmax ∧ (0<size.val ∧ True); decide)
  | (change 0<lmax ∧ (2<size.val ∧ True); decide)
  | (change 4<lmax ∧ (0<size.val ∧ True); decide)
  | (intro value observed; have same:=Option.some.inj observed; subst value; rfl)
  | (intro value observed; cases observed)
private theorem apartA : ∀ q ∈ frames,q.apart da := by
 intro query member
 simp only [frames,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl
 all_goals apply Apart.fork (StepApart.index _ _ (by decide))
private theorem outsideA : ∀ q ∈ frames,∀ i<size.val,q.location base≠(pathLoc da base).add i := by
 intro query member i inside
 have cases : i=0 ∨ i=1 ∨ i=2 := by change i<3 at inside; omega
 simp only [frames,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl <;> rcases cases with rfl|rfl|rfl <;> decide
private theorem apartB : ∀ q ∈ queries da indicesA++frames,q.apart db := by
 intro query member
 simp only [queries,indicesA,frames,List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with (rfl|rfl)|(rfl|rfl|rfl|rfl)
 all_goals apply Apart.fork (StepApart.index _ _ (by decide))
private theorem outsideB : ∀ q ∈ queries da indicesA++frames,∀ i<size.val,q.location base≠(pathLoc db base).add i := by
 intro query member i inside
 have cases : i=0 ∨ i=1 ∨ i=2 := by change i<3 at inside; omega
 simp only [queries,indicesA,frames,List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with (rfl|rfl)|(rfl|rfl|rfl|rfl) <;> rcases cases with rfl|rfl|rfl <;> decide
private def storeA := PrimitiveSnapshotNumeric.symbolic captured (part 3) (part 0) 3
private def numericA := PrimitiveSnapshotNumeric.numeric 64 hash initial (part 3) (part 0) 3
private noncomputable def targetA := TargetFixedSnapshot.afterCopy .uint size target (.data (.root 0) 0) (.data (.root 0) 3)
private def finalStore := PrimitiveSnapshotNumeric.symbolic storeA (part 9) (part 3) 3
private def finalNumeric := PrimitiveSnapshotNumeric.numeric 64 hash numericA (part 9) (part 3) 3
private noncomputable def finalTarget := TargetFixedSnapshot.afterCopy .uint size targetA (.data (.root 0) 3) (.data (.root 0) 9)
private def codeA := TargetFixedSnapshot.code .uint size (.data (.root 0) 0) (.data (.root 0) 3)
private def codeB := TargetFixedSnapshot.code .uint size (.data (.root 0) 3) (.data (.root 0) 9)

theorem certificate : result.find db=some (recursiveCopy oldB snapshotB) ∧
 Represented result (queries db indicesB++(queries da indicesA++frames)) base finalStore ∧
 Transport 64 hash locations finalStore finalNumeric ∧ Evm.run (codeA++codeB) target=.ok finalTarget 0 ∧
 (∀ l (member : l ∈ locations),finalTarget.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (finalNumeric (l.word 64 hash))) := by
 exact PrimitiveSnapshotDependent.complete finite root middle result da sa db oldA snapshotA oldB rfl rfl rfl rfl rfl
  (by change 1<lmax ∧ True; decide) (by change 3<lmax ∧ True; decide) indicesA indicesB frames base True.intro captured initial target before sourceA oldFrames apartA outsideA apartB outsideB
  (covered 3 (by decide)) (covered 0 (by decide)) (covered 9 (by decide)) fitting agreement

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

theorem whole_owner : Represented result (.length .nil::queries db indicesB++(queries da indicesA++frames)) base finalStore := by
 intro query member
 rcases List.mem_cons.mp member with header|copied
 · exact header_owner query (List.mem_singleton.mpr header)
 · exact certificate.2.1 query copied

private def observations : List (Query graph (.array T)) :=
 [.length .nil,q 0 0,q 0 1,q 0 2,q 1 0,q 1 1,q 1 2,q 2 0,q 2 1,q 2 2,q 3 0,q 3 1,q 3 2,q 1 3,q 4 0]
theorem graph_ordered :
 observations.map (fun q => (q.read root).map Subtype.val)=[some 2,some 7,some 0,some 23,some 53,some 0,some 71,some 87,some 0,some 99,some 101,some 109,some 127,none,none] ∧
 observations.map (fun q => (q.read middle).map Subtype.val)=[some 2,some 7,some 0,some 23,some 7,some 0,some 23,some 87,some 0,some 99,some 101,some 109,some 127,none,none] ∧
 observations.map (fun q => (q.read result).map Subtype.val)=[some 2,some 7,some 0,some 23,some 7,some 0,some 23,some 87,some 0,some 99,some 7,some 0,some 23,none,none] ∧
 (.length .nil::queries db indicesB++(queries da indicesA++frames)).map (fun q => (q.read result).map Subtype.val)=[some 2,some 0,some 23,some 7,some 0,some 23,some 7,some 7,none,some 23,some 7] := ⟨rfl,rfl,rfl,rfl⟩

theorem storage_ordered :
 locations.map (fun l => (captured l).val)=[2,211,7,0,23,53,0,71,87,0,99,101,109,127,131,149,151] ∧
 locations.map (fun l => (storeA l).val)=[2,211,7,0,23,7,0,23,87,0,99,101,109,127,131,149,151] ∧
 locations.map (fun l => (finalStore l).val)=[2,211,7,0,23,7,0,23,87,0,99,7,0,23,131,149,151] ∧
 locations.map (fun l => (initial (l.word 64 hash)).val)=[2,211,7,0,23,53,0,71,87,0,99,101,109,127,131,149,151] ∧
 locations.map (fun l => (numericA (l.word 64 hash)).val)=[2,211,7,0,23,7,0,23,87,0,99,101,109,127,131,149,151] ∧
 locations.map (fun l => (finalNumeric (l.word 64 hash)).val)=[2,211,7,0,23,7,0,23,87,0,99,7,0,23,131,149,151] ∧
 locations.attach.map (fun l => (target.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[2,211,7,0,23,53,0,71,87,0,99,101,109,127,131,149,151] ∧
 locations.attach.map (fun l => (targetA.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[2,211,7,0,23,7,0,23,87,0,99,101,109,127,131,149,151] ∧
 locations.attach.map (fun l => (finalTarget.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[2,211,7,0,23,7,0,23,87,0,99,7,0,23,131,149,151] ∧
 {targetA with store:=target.store}=target ∧
 {finalTarget with store:=target.store}=target := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,by decide,by decide,by decide,rfl,rfl⟩

theorem aliases_and_presence : da.readLive Value.dflt root=some oldA ∧
 da.readLive Value.dflt middle=some snapshotB ∧ da.readLive Value.dflt result=some snapshotB ∧
 db.readLive Value.dflt root=none ∧ db.readLive Value.dflt result=none ∧ result.length=root.length ∧ result.extent=root.extent ∧
 fixedView snapshotB ⟨1,by decide⟩=.absent ∧
 (result.find db).map (fun (v : Value graph T) => fixedView (T:=T) v ⟨1,by decide⟩)=some (.present (.prim (w 0))) := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem failures_and_raw : root.find (pre 4)=none ∧ recursiveCopyAt middle (pre 4) sb=none ∧
 recursiveCopyAt middle db (pre 4)=none ∧ (q 4 0).read result=none ∧
 Evm.run (TargetOperations.readCode (.data (.root 0) 12)) finalTarget=
 .ok {finalTarget with stack:=.val (TargetOperations.encodeWord (w 131))::finalTarget.stack} 0 := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem old_source_is_not_current : (q 1 0).read root=some (w 53) ∧ (q 1 0).read middle=some (w 7) ∧
 ¬ Represented middle (queries da indicesB) base captured := by
 refine ⟨rfl,rfl,?_⟩
 intro alleged
 have member : (PrimitiveSnapshotOwner.query (G:=graph) (p:=PrimTy.uint) ⟨0,by decide⟩).prefix da ∈ queries da indicesB := by
  apply List.mem_map.mpr
  refine ⟨PrimitiveSnapshotOwner.query ⟨0,by decide⟩,?_,rfl⟩
  apply List.mem_map.mpr
  exact ⟨⟨0,by decide⟩,by decide,rfl⟩
 have bad:=(alleged _ member).2.2 (w 7) rfl
 have impossible:=congrArg (fun w : Semantics.Word => w.val) bad
 change (53:Int)=7 at impossible
 omega

private def reverseRoot := ((recursiveCopyAt root db da).bind (fun m => recursiveCopyAt m da sa)).getD root
private def reverseStore := PrimitiveSnapshotNumeric.symbolic (PrimitiveSnapshotNumeric.symbolic captured (part 9) (part 3) 3) (part 3) (part 0) 3
private def reverseNumeric := PrimitiveSnapshotNumeric.numeric 64 hash (PrimitiveSnapshotNumeric.numeric 64 hash initial (part 9) (part 3) 3) (part 3) (part 0) 3
private noncomputable def reverseTarget := TargetFixedSnapshot.afterCopy .uint size (TargetFixedSnapshot.afterCopy .uint size target (.data (.root 0) 3) (.data (.root 0) 9)) (.data (.root 0) 0) (.data (.root 0) 3)
theorem reverse_order : Transport 64 hash locations reverseStore reverseNumeric ∧
 Evm.run (codeB++codeA) target=.ok reverseTarget 0 ∧
 observations.map (fun q => (q.read reverseRoot).map Subtype.val)=[some 2,some 7,some 0,some 23,some 7,some 0,some 23,some 87,some 0,some 99,some 53,some 0,some 71,none,none] ∧
 locations.map (fun l => (reverseStore l).val)=[2,211,7,0,23,7,0,23,87,0,99,53,0,71,131,149,151] ∧
 locations.map (fun l => (reverseNumeric (l.word 64 hash)).val)=[2,211,7,0,23,7,0,23,87,0,99,53,0,71,131,149,151] ∧
 locations.attach.map (fun l => (reverseTarget.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[2,211,7,0,23,7,0,23,87,0,99,53,0,71,131,149,151] ∧
 {reverseTarget with store:=target.store}=target ∧ reverseNumeric 25≠finalNumeric 25 := by
 have ordered:=PrimitiveSnapshotCommutation.target_sequence finite .uint .uint size size captured initial target before (part 9) (part 3) (part 3) (part 0)
  True.intro True.intro True.intro True.intro (covered 9 (by decide)) (covered 3 (by decide)) (covered 3 (by decide)) (covered 0 (by decide)) fitting agreement
 exact ⟨ordered.1,ordered.2.1,rfl,rfl,rfl,by decide,rfl,by decide⟩

private def badCaptured := Representation.write captured (part 1) (w 17)
private def badInitial : WordStore := fun a => if a<16 then badCaptured (.root a) else badCaptured (part (a-16))
private noncomputable def badTarget := {target with store:=⟨fun slot => TargetOperations.encodeWord (badCaptured (Solidity.Storage.ofSlot slot))⟩}
private def badStore := PrimitiveSnapshotNumeric.symbolic (PrimitiveSnapshotNumeric.symbolic badCaptured (part 3) (part 0) 3) (part 9) (part 3) 3
private def badNumeric := PrimitiveSnapshotNumeric.numeric 64 hash (PrimitiveSnapshotNumeric.numeric 64 hash badInitial (part 3) (part 0) 3) (part 9) (part 3) 3
private noncomputable def badFinal := TargetFixedSnapshot.afterCopy .uint size (TargetFixedSnapshot.afterCopy .uint size badTarget (.data (.root 0) 0) (.data (.root 0) 3)) (.data (.root 0) 3) (.data (.root 0) 9)
private theorem badBefore : Transport 64 hash locations badCaptured badInitial := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
private theorem badAgreement : ∀ l (member : l ∈ locations),badTarget.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (badInitial (l.word 64 hash)) := by
 intro l member
 change TargetOperations.encodeWord (badCaptured (Solidity.Storage.ofSlot (TargetOperations.toSlot l (fitting l member))))=_
 rw [TargetOperations.ofSlot_toSlot,← badBefore l member]
theorem bad_union : Represented root (queries sa indicesA) base badCaptured ∧
 ¬ Represented root (queries sa (indicesA++indicesB)) base badCaptured ∧
 Transport 64 hash locations badStore badNumeric ∧ Evm.run (codeA++codeB) badTarget=.ok badFinal 0 ∧
 locations.map (fun l => (badCaptured l).val)=[2,211,7,17,23,53,0,71,87,0,99,101,109,127,131,149,151] ∧
 locations.map (fun l => (badInitial (l.word 64 hash)).val)=[2,211,7,17,23,53,0,71,87,0,99,101,109,127,131,149,151] ∧
 locations.attach.map (fun l => (badTarget.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[2,211,7,17,23,53,0,71,87,0,99,101,109,127,131,149,151] ∧
 locations.map (fun l => (badStore l).val)=[2,211,7,17,23,7,17,23,87,0,99,7,17,23,131,149,151] ∧
 locations.map (fun l => (badNumeric (l.word 64 hash)).val)=[2,211,7,17,23,7,17,23,87,0,99,7,17,23,131,149,151] ∧
 locations.attach.map (fun l => (badFinal.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)=[2,211,7,17,23,7,17,23,87,0,99,7,17,23,131,149,151] ∧
 {badFinal with store:=badTarget.store}=badTarget ∧ ¬ Represented result (queries db indicesB) base badStore := by
 have ordered:=PrimitiveSnapshotCommutation.target_sequence finite .uint .uint size size badCaptured badInitial badTarget badBefore (part 3) (part 0) (part 9) (part 3)
  True.intro True.intro True.intro True.intro (covered 3 (by decide)) (covered 0 (by decide)) (covered 9 (by decide)) (covered 3 (by decide)) fitting badAgreement
 refine ⟨?_,?_,ordered.1,ordered.2.1,rfl,rfl,by decide,rfl,rfl,by decide,rfl,?_⟩
 · intro query member
   simp only [queries,indicesA,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl
   all_goals refine ⟨?_,True.intro,?_⟩
   all_goals first
    | (change 0<lmax ∧ (2<size.val ∧ True); decide)
    | (change 0<lmax ∧ (0<size.val ∧ True); decide)
    | (intro value observed; have same:=Option.some.inj observed; subst value; rfl)
 · intro alleged
   have member : (PrimitiveSnapshotOwner.query (G:=graph) (p:=PrimTy.uint) ⟨1,by decide⟩).prefix sa ∈ queries sa (indicesA++indicesB) := by
    apply List.mem_map.mpr
    refine ⟨PrimitiveSnapshotOwner.query ⟨1,by decide⟩,?_,rfl⟩
    apply List.mem_map.mpr
    exact ⟨⟨1,by decide⟩,by decide,rfl⟩
   have bad:=(alleged _ member).2.2 (w 0) rfl
   have impossible:=congrArg (fun w : Semantics.Word => w.val) bad
   change (17:Int)=0 at impossible
   omega
 · intro alleged
   have member : (PrimitiveSnapshotOwner.query (G:=graph) (p:=PrimTy.uint) ⟨1,by decide⟩).prefix db ∈ queries db indicesB := by
    apply List.mem_map.mpr
    refine ⟨PrimitiveSnapshotOwner.query ⟨1,by decide⟩,?_,rfl⟩
    apply List.mem_map.mpr
    exact ⟨⟨1,by decide⟩,by decide,rfl⟩
   have bad:=(alleged _ member).2.2 (w 0) rfl
   have impossible:=congrArg (fun w : Semantics.Word => w.val) bad
   change (17:Int)=0 at impossible
   omega

/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotDependent.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotDependent.Controls.header_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms header_owner
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotDependent.Controls.whole_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms whole_owner
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotDependent.Controls.graph_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms graph_ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotDependent.Controls.storage_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms storage_ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotDependent.Controls.aliases_and_presence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms aliases_and_presence
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotDependent.Controls.failures_and_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failures_and_raw
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotDependent.Controls.old_source_is_not_current' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms old_source_is_not_current
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotDependent.Controls.reverse_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reverse_order
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotDependent.Controls.bad_union' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms bad_union
end Solidity.Backend.StorageOps.PrimitiveSnapshotDependent.Controls
