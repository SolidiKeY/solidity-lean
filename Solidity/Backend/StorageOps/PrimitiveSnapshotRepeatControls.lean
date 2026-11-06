import Solidity.Backend.StorageOps.PrimitiveSnapshotRepeat
import Solidity.Backend.StorageOps.RecursiveRepeatCopy

/-! Inhabited represented/numeric/actual-target repetition and two independent
negative controls: CURRENT source overlap and omitted per-run hash regions.
No Source evaluation or global cryptographic relation is defined here. -/
namespace Solidity.Backend.StorageOps.PrimitiveSnapshotRepeatControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph PrimitiveSnapshotNumeric
private def graph : Schema 0 where
 origin := "v10-repeat-represented"
 declId := fun i => nomatch i
 declId_injective := by intro i; exact Fin.elim0 i
 name := fun i => nomatch i
 fields := fun i => nomatch i
 rank := fun i => nomatch i
 nonempty := by intro i; exact Fin.elim0 i
 distinct := by intro i; exact Fin.elim0 i
 guarded := by intro i; exact Fin.elim0 i
private def size : FixedSize := ⟨3,by decide⟩
private def w (x : Fin 256) : Semantics.Word := lengthWord x.val (by have bound:=x.isLt; omega)
private def base : Solidity.Storage.Loc := .root 0
private def part (i : Nat) : Solidity.Storage.Loc := .data base i
private def src := part 0
private def dst := part 4
private def locations : List Solidity.Storage.Loc := [base,.root 1,.root 2,.root 3,.root 4,part 0,part 1,part 2,part 3,part 4,part 5,part 6,part 7,part 8]
private def hash (_ : Solidity.Storage.Pre) : Nat := 16
private def captured : Store := fun l => if l=base then w 3 else if l=.root 1 then w 17 else if l=.root 2 then w 23 else if l=.root 3 then w 53 else if l=.root 4 then w 87 else
 if l=part 0 then w 7 else if l=part 1 then w 0 else if l=part 2 then w 23 else if l=part 3 then w 71 else if l=part 4 then w 53 else if l=part 5 then w 59 else if l=part 6 then w 61 else if l=part 7 then w 73 else if l=part 8 then w 79 else w 0
private def initial : WordStore := fun a => if a<16 then captured (.root a) else captured (part (a-16))
private noncomputable def target : Evm.Machine :=
 {Evm.Machine.init (fun _ => 19) ⟨7,by decide⟩ with
 store:=⟨fun slot => TargetOperations.encodeWord (captured (Solidity.Storage.ofSlot slot))⟩
 stack:=[.val ⟨23,by decide⟩,.slot (.root 9)]
 mem:=fun _ => .val ⟨31,by decide⟩
 caller:=⟨13,by decide⟩
 timestamp:=⟨53,by decide⟩}
private def s1 := symbolic captured dst src 3
private def s2 := symbolic s1 dst src 3
private def n1 := numeric 64 hash initial dst src 3
private def n2 := numeric 64 hash n1 dst src 3
private def srcSlot := TargetOperations.toSlot src True.intro
private def dstSlot := TargetOperations.toSlot dst True.intro
private noncomputable def t1 := TargetFixedSnapshot.afterCopy .uint size target srcSlot dstSlot
private noncomputable def t2 := TargetFixedSnapshot.afterCopy .uint size t1 srcSlot dstSlot
private def code := TargetFixedSnapshot.code .uint size srcSlot dstSlot
private theorem finite : FiniteRun 64 16 5 hash [.data 0] locations := by
 constructor
 · intro p; change 16<64; decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [part,base,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
private theorem before : Transport 64 hash locations captured initial := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
private theorem fitting : ∀ l ∈ locations,TargetOperations.KeysFit l := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact True.intro
private theorem agreement : ∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (initial (l.word 64 hash)) := by
 intro l member
 change TargetOperations.encodeWord (captured (Solidity.Storage.ofSlot (TargetOperations.toSlot l (fitting l member))))=_
 rw [TargetOperations.ofSlot_toSlot,← before l member]
private theorem covered (offset : Nat) (bound : offset+3≤9) : ∀ i<size.val,(part offset).add i ∈ locations := by
 intro i inside
 change i<3 at inside
 have cases : offset+i=0 ∨ offset+i=1 ∨ offset+i=2 ∨ offset+i=3 ∨ offset+i=4 ∨ offset+i=5 ∨ offset+i=6 ∨ offset+i=7 ∨ offset+i=8 := by omega
 change Solidity.Storage.Loc.data base (offset+i) ∈ locations
 rcases cases with h|h|h|h|h|h|h|h|h <;> rw [h] <;> decide
private theorem safe : src=dst ∨ ∀ i<size.val,∀ j<size.val,src.add i≠dst.add j := by decide

/-- All OLD relation/region/coverage premises are inhabited; no post owner assumed. -/
theorem certificate : Transport 64 hash locations s1 n1 ∧ Transport 64 hash locations s2 n2 ∧
 s2=s1 ∧ n2=n1 ∧ Evm.run (code++code) target=.ok t1 0 ∧
 (∀ l (member : l ∈ locations),t1.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (n2 (l.word 64 hash))) := by
 exact PrimitiveSnapshotRepeat.complete finite .uint size captured initial target before dst src True.intro True.intro (covered 0 (by decide)) (covered 4 (by decide)) safe fitting agreement

private def sourceGraph : Value graph (.fixed (.prim .uint) size) := .fixed fun i =>
 if i.val=1 then .absent else .present (.prim (if i.val=0 then w 7 else w 23))
private def oldGraph : Value graph (.fixed (.prim .uint) size) := .fixed fun i =>
 .present (.prim (if i.val=0 then w 53 else if i.val=1 then w 59 else w 61))
private def onceGraph := recursiveCopy oldGraph sourceGraph
private def twiceGraph := recursiveCopy onceGraph sourceGraph
private def indices : List (Fin size.val) := [⟨2,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩]
private def queries : List (Query graph (.fixed (.prim .uint) size)) := indices.map PrimitiveSnapshotOwner.query
private theorem sourceOwner : Represented sourceGraph queries src captured := by
 intro query member
 simp only [queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl
 all_goals refine ⟨?_,True.intro,?_⟩
 all_goals first
  | (change 2<size.val ∧ True; decide)
  | (change 0<size.val ∧ True; decide)
  | (change 1<size.val ∧ True; decide)
  | (intro value observed; have same:=Option.some.inj observed; subst value; rfl)

/-- ACTUAL graph copies obtain the PUBLIC owner relation for the repeated store;
implicit default, raw materialization and malformed/raw older word stay distinct. -/
theorem represented_client : Represented twiceGraph queries dst s2 ∧
 fixedView sourceGraph ⟨1,by decide⟩=.absent ∧
 fixedView twiceGraph ⟨1,by decide⟩=.present (.prim (w 0)) ∧
 twiceGraph.find (TargetFixedPrimitive.path ⟨1,by decide⟩)=some (.prim (w 0)) ∧
 twiceGraph.find (TargetFixedPrimitive.path ⟨3,by decide⟩)=none ∧ s2 (dst.add 3)=w 73 := by
 have owner := PrimitiveSnapshotOwner.represented finite oldGraph sourceGraph indices dst src captured initial before sourceOwner (covered 0 (by decide)) (covered 4 (by decide))
 refine ⟨?_,rfl,rfl,rfl,rfl,rfl⟩
 change Represented (recursiveCopy (recursiveCopy oldGraph sourceGraph) sourceGraph) queries dst s2
 rw [RecursiveRepeatCopy.value_repeat]
 change Represented onceGraph queries dst (symbolic (symbolic captured dst src 3) dst src 3)
 rw [PrimitiveSnapshotRepeat.symbolic_repeat finite captured initial before dst src 3 (covered 0 (by decide)) (covered 4 (by decide)) safe]
 exact owner

private def symView (s : Store) := locations.map (fun l => (s l).val)
private def numView (m : WordStore) := locations.map (fun l => (m (l.word 64 hash)).val)
private def targetView (m : Evm.Machine) := locations.attach.map (fun l => (m.store.cells (TargetOperations.toSlot l.val (fitting l.val l.property))).val)
/-- COMPLETE three-state observations in all three store models, full context. -/
theorem ordered :
 symView captured=[3,17,23,53,87,7,0,23,71,53,59,61,73,79] ∧
 symView s1=[3,17,23,53,87,7,0,23,71,7,0,23,73,79] ∧ symView s2=[3,17,23,53,87,7,0,23,71,7,0,23,73,79] ∧
 numView initial=[3,17,23,53,87,7,0,23,71,53,59,61,73,79] ∧
 numView n1=[3,17,23,53,87,7,0,23,71,7,0,23,73,79] ∧ numView n2=[3,17,23,53,87,7,0,23,71,7,0,23,73,79] ∧
 targetView target=[3,17,23,53,87,7,0,23,71,53,59,61,73,79] ∧
 targetView t1=[3,17,23,53,87,7,0,23,71,7,0,23,73,79] ∧ targetView t2=[3,17,23,53,87,7,0,23,71,7,0,23,73,79] ∧
 {t1 with store:=target.store}=target ∧ {t2 with store:=target.store}=target := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,by decide,by decide,rfl,rfl⟩

/-- Hashed exact aliases exercise the other safety branch with real execution. -/
theorem self :
 symbolic (symbolic captured src src 3) src src 3=captured ∧
 numeric 64 hash (numeric 64 hash initial src src 3) src src 3=initial ∧
 Evm.run (TargetFixedSnapshot.code .uint size srcSlot srcSlot ++ TargetFixedSnapshot.code .uint size srcSlot srcSlot) target=.ok target 0 := by
 simp only [PrimitiveSnapshotSelf.symbolic_self,PrimitiveSnapshotSelf.numeric_self]
 refine ⟨True.intro,True.intro,?_⟩
 simpa only [PrimitiveSnapshotSelf.machine_self] using
  (TargetSnapshotRepeat.complete .uint size target srcSlot srcSlot (Or.inl rfl)).1

private def os1 := symbolic captured (part 1) src 3
private def os2 := symbolic os1 (part 1) src 3
private def on1 := numeric 64 hash initial (part 1) src 3
private def on2 := numeric 64 hash on1 (part 1) src 3
private def overlapDstSlot := TargetOperations.toSlot (part 1) True.intro
private noncomputable def ot1 := TargetFixedSnapshot.afterCopy .uint size target srcSlot overlapDstSlot
private noncomputable def ot2 := TargetFixedSnapshot.afterCopy .uint size ot1 srcSlot overlapDstSlot
/-- With a VALID region, CURRENT overlap changes all three models consistently. -/
theorem overlap :
 Transport 64 hash locations os2 on2 ∧
 Evm.run (TargetFixedSnapshot.code .uint size srcSlot overlapDstSlot ++ TargetFixedSnapshot.code .uint size srcSlot overlapDstSlot) target=.ok ot2 0 ∧
 symView os1=[3,17,23,53,87,7,7,0,23,53,59,61,73,79] ∧ symView os2=[3,17,23,53,87,7,7,7,0,53,59,61,73,79] ∧
 numView on1=[3,17,23,53,87,7,7,0,23,53,59,61,73,79] ∧ numView on2=[3,17,23,53,87,7,7,7,0,53,59,61,73,79] ∧
 targetView ot1=[3,17,23,53,87,7,7,0,23,53,59,61,73,79] ∧ targetView ot2=[3,17,23,53,87,7,7,7,0,53,59,61,73,79] ∧
 on2 ((part 2).word 64 hash)≠on1 ((part 2).word 64 hash) := by
 have sequence := PrimitiveSnapshotCommutation.target_sequence finite .uint .uint size size captured initial target before (part 1) src (part 1) src True.intro True.intro True.intro True.intro (covered 1 (by decide)) (covered 0 (by decide)) (covered 1 (by decide)) (covered 0 (by decide)) fitting agreement
 exact ⟨sequence.1,sequence.2.1,rfl,rfl,rfl,rfl,by decide,by decide,by decide⟩

private def badHash (_ : Solidity.Storage.Pre) : Nat := 0
private def badCaptured : Store := fun l => if l=base ∨ l=part 0 then w 7 else if l=.root 1 ∨ l=part 1 then w 17 else if l=.root 2 ∨ l=part 2 then w 23 else if l=.root 3 ∨ l=part 3 then w 53 else if l=.root 4 ∨ l=part 4 then w 87 else w 0
private def badInitial : WordStore := fun a => badCaptured (.root a)
private theorem badBefore : Transport 64 badHash locations badCaptured badInitial := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
private noncomputable def badTarget : Evm.Machine :=
 {target with store:=⟨fun slot => TargetOperations.encodeWord (badCaptured (Solidity.Storage.ofSlot slot))⟩}
private theorem badAgreement : ∀ l (member : l ∈ locations),badTarget.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (badInitial (l.word 64 badHash)) := by
 intro l member
 change TargetOperations.encodeWord (badCaptured (Solidity.Storage.ofSlot (TargetOperations.toSlot l (fitting l member))))=_
 rw [TargetOperations.ofSlot_toSlot,← badBefore l member]
private def badDst : Solidity.Storage.Loc := .root 1
private def bs1 := symbolic badCaptured badDst src 3
private def bs2 := symbolic bs1 badDst src 3
private def bn1 := numeric 64 badHash badInitial badDst src 3
private def bn2 := numeric 64 badHash bn1 badDst src 3
private def badDstSlot := TargetOperations.toSlot badDst True.intro
private noncomputable def bt1 := TargetFixedSnapshot.afterCopy .uint size badTarget srcSlot badDstSlot
private noncomputable def bt2 := TargetFixedSnapshot.afterCopy .uint size bt1 srcSlot badDstSlot
private def badNumView (m : WordStore) := locations.map (fun l => (m (l.word 64 badHash)).val)

/-- OLD relations and logical separation hold, but actual region evidence is FALSE. -/
theorem bad_run :
 Transport 64 badHash locations badCaptured badInitial ∧
 (∀ l (member : l ∈ locations),badTarget.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (badInitial (l.word 64 badHash))) ∧
 (∀ p,badHash p<64) ∧ 16≤64 ∧ 5≤64 ∧
 (∀ l ∈ locations,Solidity.Storage.Loc.Bounded 16 5 l) ∧
 (∀ l ∈ locations,∀ p ∈ Solidity.Storage.Loc.pres 64 badHash l,p ∈ [.data 0]) ∧
 (src=badDst ∨ ∀ i<size.val,∀ j<size.val,src.add i≠badDst.add j) ∧
 ¬ FiniteRun 64 16 5 badHash [.data 0] locations := by
 refine ⟨badBefore,badAgreement,?_,by decide,by decide,finite.bounded,?_,by decide,?_⟩
 · intro p; change 0<64; decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
 · intro alleged
   have impossible := alleged.word_inj (a:=Solidity.Storage.Loc.root 1) (b:=part 1) (by decide) (by decide) rfl
   cases impossible

/-- COMPLETE bad-region three-state observations expose actual numeric aliasing. -/
theorem bad_ordered :
 symView badCaptured=[7,17,23,53,87,7,17,23,53,87,0,0,0,0] ∧
 symView bs1=[7,7,17,23,87,7,17,23,53,87,0,0,0,0] ∧ symView bs2=[7,7,17,23,87,7,17,23,53,87,0,0,0,0] ∧
 badNumView badInitial=[7,17,23,53,87,7,17,23,53,87,0,0,0,0] ∧
 badNumView bn1=[7,7,17,23,87,7,7,17,23,87,0,0,0,0] ∧ badNumView bn2=[7,7,7,17,87,7,7,7,17,87,0,0,0,0] ∧
 targetView badTarget=[7,17,23,53,87,7,17,23,53,87,0,0,0,0] ∧
 targetView bt1=[7,7,17,23,87,7,17,23,53,87,0,0,0,0] ∧ targetView bt2=[7,7,17,23,87,7,17,23,53,87,0,0,0,0] ∧
 {bt1 with store:=badTarget.store}=badTarget ∧ {bt2 with store:=badTarget.store}=badTarget := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,by decide,by decide,rfl,rfl⟩

/-- Actual symbolic target execution remains valid, but numeric transport fails;
region hypotheses cannot be silently omitted or replaced by global hash faith. -/
theorem bad_refutes :
 Evm.run (TargetFixedSnapshot.code .uint size srcSlot badDstSlot ++ TargetFixedSnapshot.code .uint size srcSlot badDstSlot) badTarget=.ok bt1 0 ∧
 ¬ Transport 64 badHash locations bs1 bn1 ∧ ¬ Transport 64 badHash locations bs2 bn2 ∧
 bn2 2≠bn1 2 ∧
 bt2.store.cells (TargetOperations.toSlot (.root 2) True.intro)≠TargetOperations.encodeWord (bn2 2) := by
 refine ⟨?_,?_,?_,by decide,by decide⟩
 · exact (TargetSnapshotRepeat.complete .uint size badTarget srcSlot badDstSlot (Or.inr (by decide))).1
 · intro alleged
   have bad:=alleged (part 1) (by decide)
   have impossible:=congrArg (fun value : Semantics.Word => value.val) bad
   change (7:Int)=17 at impossible
   omega
 · intro alleged
   have bad:=alleged (.root 2) (by decide)
   have impossible:=congrArg (fun value : Semantics.Word => value.val) bad
   change (7:Int)=17 at impossible
   omega

/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRepeatControls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRepeatControls.represented_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_client
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRepeatControls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRepeatControls.self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms self
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRepeatControls.overlap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms overlap
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRepeatControls.bad_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms bad_run
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRepeatControls.bad_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms bad_ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRepeatControls.bad_refutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms bad_refutes
end Solidity.Backend.StorageOps.PrimitiveSnapshotRepeatControls
