import Solidity.Backend.StorageOps.FreshArrayHistory
import Solidity.Backend.StorageOps.CopyDemandControls

/-! Fresh child HEADER provenance plus actual child push resets dirty payload.
All primitive kinds, complete ordered logical/raw/target views and bad-history
control. This is captured typed storage composition, not Source/world closure. -/
namespace Solidity.Backend.StorageOps.FreshArrayHistory.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private abbrev G := CopyDemandControls.graph
private def ix (i : Fin 3) : Index := ⟨i.val,by have h:=i.isLt; omega⟩
private def w0 : Semantics.Word := ClearDemands.zero
private def w1 : Semantics.Word := ⟨1,by decide⟩
private def w2 : Semantics.Word := ⟨2,by decide⟩
private def w3 : Semantics.Word := ⟨3,by decide⟩
private def w7 : Semantics.Word := ⟨7,by decide⟩
private def w87 : Semantics.Word := ⟨87,by decide⟩
private def w99 : Semantics.Word := ⟨99,by decide⟩
private def payload : (p : PrimTy) → p.Denote
 | .bool => true
 | .uint => ⟨53,by decide⟩
 | .int => ⟨-17,by decide⟩
private def encoded (p : PrimTy) := PrimTy.toWord (payload p)
private def old (p : PrimTy) : Value G (.array (.array (.prim p))) :=
 .array ⟨1,by decide⟩ (ix 1) (by decide) (fun _ => .present (.array ⟨2,by decide⟩ (ix 2) (by decide) (fun _ => .present (.prim (payload p)))))
private def middle (p : PrimTy) := (operationPush (old p)).getD (old p)
private def path (p : PrimTy) := NestedCopyObservations.childPath (G:=G) (p:=p) (ix 1)
private def result (p : PrimTy) := (pushAt (middle p) (path p)).getD (middle p)
private def base : Solidity.Storage.Loc := .root 0
private def child (i : Nat) : Solidity.Storage.Loc := .data base i
private def cell (i j : Nat) : Solidity.Storage.Loc := .data (child i) j
private def history (p : PrimTy) : List (Solidity.Storage.Loc × Semantics.Word) :=
 [(base,w1),(child 0,w2),(cell 0 0,encoded p),(cell 1 0,w87),(cell 1 1,w99),(child 2,w7)]
private def hash (key : Solidity.Storage.Pre) : Nat :=
 if key=.data 0 then 8 else if key=.data 8 then 16 else if key=.data 9 then 24 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 8,.data 9]
private def locations : List Solidity.Storage.Loc := [base,child 0,cell 0 0,child 1,cell 1 0,cell 1 1,child 2]
private def indices : List Index := [ix 1,ix 0,ix 2,ix 0]
private theorem run : FiniteRun 64 8 1 hash preimages locations := by
 constructor
 · intro key; simp only [hash]; split <;> first | decide | (split <;> first | decide | (split <;> decide))
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [base,child,cell,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem historyCovered (p : PrimTy) : ∀ op ∈ history p, op.1 ∈ locations := by
 intro op member
 simp only [history,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide
private theorem untouched (p : PrimTy) : ∀ op ∈ history p, child 1 ≠ op.1 := by
 intro op member
 simp only [history,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide
private theorem supported (p : PrimTy) : ∀ q ∈ PrimitivePop.queries (G:=G) (p:=p) indices, q.supported := by
 intro q member
 simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl
 · exact True.intro
 all_goals change _<lmax ∧ True; constructor; decide; exact True.intro
private theorem before (p : PrimTy) : Represented (old p) [.length .nil] base (FreshMappingHistory.symbolic (history p)) := by
 intro q member
 have same:=List.mem_singleton.mp member; subst q
 refine ⟨True.intro,⟨by change (1:Nat)≤lmax; decide,by change (1:Nat)≤lmax; decide⟩,?_⟩
 intro word observed
 change some w1=some word at observed
 cases observed
 rfl
private theorem fitting : ∀ l ∈ locations, TargetOperations.KeysFit l := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact True.intro
private noncomputable def target (p : PrimTy) : Evm.Machine :=
 {Evm.Machine.init (fun _ => 19) ⟨7,by decide⟩ with
 store := ⟨fun slot => TargetOperations.encodeWord (FreshMappingHistory.symbolic (history p) (Solidity.Storage.ofSlot slot))⟩
 stack := [.val ⟨23,by decide⟩,.slot (.root 9)]
 mem := fun _ => .val ⟨31,by decide⟩
 caller := ⟨13,by decide⟩
 timestamp := ⟨53,by decide⟩}
private noncomputable def midTarget (p : PrimTy) : Evm.Machine :=
 {target p with store := Evm.WordStore.write (target p).store (.root 0) 2}
private noncomputable def finalTarget (p : PrimTy) : Evm.Machine :=
 {midTarget p with store := Evm.WordStore.write (Evm.WordStore.write (midTarget p).store (.data (.root 0) 1) 1) (.data (.data (.root 0) 1) 0) 0}
private def firstNumeric (p : PrimTy) := writeWord (FreshMappingHistory.numeric 64 hash (history p)) 0 w2
private def finalNumeric (p : PrimTy) := writeWord (writeWord (firstNumeric p) 24 w0) 9 w1
private def finalStore (p : PrimTy) := write (write (write (FreshMappingHistory.symbolic (history p)) base w2) (cell 1 0) w0) (child 1) w1

/-- Actual nonempty OLD history, then outer allocation and child mutation;
the newly live child is NOT merely an observed empty default. -/
theorem certificate (p : PrimTy) :
 pushAt (middle p) (path p)=some (result p) ∧
 LifecycleNumeric.pushHeader 64 hash base (FreshMappingHistory.numeric 64 hash (history p))=some (firstNumeric p) ∧
 LifecycleNumeric.pushPrimitive 64 hash (child 1) (firstNumeric p)=some (finalNumeric p) ∧
 Evm.run (TargetHeaderPush.code (.root 0) ++ TargetPrimitivePush.code (.data (.root 0) 1)) (target p)=.ok (finalTarget p) 0 ∧
 Represented (result p) ((PrimitivePop.queries indices).map (Query.prefix (path p))) base (finalStore p) ∧
 Transport 64 hash locations (finalStore p) (finalNumeric p) := by
 have agreement : ∀ l (member : l ∈ locations), (target p).store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (FreshMappingHistory.symbolic (history p) l) := by
  intro l member
  change TargetOperations.encodeWord (FreshMappingHistory.symbolic (history p) (Solidity.Storage.ofSlot (TargetOperations.toSlot l _)))=_
  rw [TargetOperations.ofSlot_toSlot]
 obtain ⟨value,first,final,found,outerRun,innerRun,targetRun,owner,transported,_⟩ :=
  complete_numeric run (old p) (middle p) (result p) rfl rfl rfl indices base True.intro (target p) (history p) (historyCovered p) (by decide) (by change child 1 ∈ locations; decide) (by change cell 1 0 ∈ locations; decide) (untouched p) (by change (1:Nat)+1≤lmax; decide) (supported p) (before p) fitting agreement
 have outerExpected : LifecycleNumeric.pushHeader 64 hash base (FreshMappingHistory.numeric 64 hash (history p))=some (firstNumeric p) := rfl
 have firstSame := Option.some.inj (outerRun.symm.trans outerExpected)
 subst first
 have innerExpected : LifecycleNumeric.pushPrimitive 64 hash (child 1) (firstNumeric p)=some (finalNumeric p) := rfl
 have finalSame := Option.some.inj (innerRun.symm.trans innerExpected)
 subst final
 have valueLength : value.length.val=1 := by
  have actual : (result p).find (path p)=some ((Value.dflt (G:=G) (.array (.prim p))).push.getD (Value.dflt (.array (.prim p)))) := rfl
  have same:=Option.some.inj (found.symm.trans actual)
  rw [same]
  rfl
 have word : lengthWord value.length.val value.length.isLt=w1 := by
  apply Subtype.ext
  exact congrArg Int.ofNat valueLength
 rw [word] at owner transported targetRun
 exact ⟨rfl,outerRun,innerRun,targetRun,owner,transported⟩

private def graphView (p : PrimTy) (v : Value G (.array (.array (.prim p)))) :=
 (v.length.val,v.extent.val,((PrimitivePop.queries indices).map (Query.prefix (path p))).map (fun q => q.read v),
  (v.find (path p)).map (fun a => (a.length.val,a.extent.val)),
  ((path p).append (.cons (.index (ix 0)) .nil)).readLive Value.dflt v |>.map (fun x => PrimTy.toWord x.head))
private def numericView (s : WordStore) := [0,8,16,9,24,25,10,63].map s
private def slots : List Evm.Slot := [.root 0,.data (.root 0) 0,.data (.data (.root 0) 0) 0,.data (.root 0) 1,.data (.data (.root 0) 1) 0,.data (.data (.root 0) 1) 1,.data (.root 0) 2,.root 63]
private def targetView (m : Evm.Machine) := slots.map (fun s => m.store.cells s)
private def context (m : Evm.Machine) := (m.stack,m.mem 0,m.bal m.self,m.bal₀ m.self,m.self,m.caller,m.callvalue,m.timestamp,m.accepts m.self m.self)

/-- COMPLETE ordered logical outcomes and raw numeric words across OLD, fresh
empty child and ACTUAL child push. Failed tail observations remain raw99. -/
theorem ordered (p : PrimTy) :
 (graphView p (old p),graphView p (middle p),graphView p (result p),
 numericView (FreshMappingHistory.numeric 64 hash (history p)),numericView (firstNumeric p),numericView (finalNumeric p)) =
 ((1,1,[none,none,none,none,none],none,none),
  (2,2,[some w0,none,none,none,none],some (0,0),none),
  (2,2,[some w1,none,some w0,none,some w0],some (1,1),some w0),
  [w1,w2,encoded p,w0,w87,w99,w7,w0],
  [w2,w2,encoded p,w0,w87,w99,w7,w0],
  [w2,w2,encoded p,w1,w0,w99,w7,w0]) := by cases p <;> rfl

/-- Complete target word/context vectors; the actual primitive reset is
required to clear dirty87, while older raw tail99 and other child survive. -/
theorem target_ordered (p : PrimTy) :
 (targetView (target p),targetView (midTarget p),targetView (finalTarget p),context (midTarget p),context (finalTarget p)) =
 ([TargetOperations.encodeWord w1,TargetOperations.encodeWord w2,TargetOperations.encodeWord (encoded p),TargetOperations.encodeWord w0,TargetOperations.encodeWord w87,TargetOperations.encodeWord w99,TargetOperations.encodeWord w7,TargetOperations.encodeWord w0],
  [TargetOperations.encodeWord w2,TargetOperations.encodeWord w2,TargetOperations.encodeWord (encoded p),TargetOperations.encodeWord w0,TargetOperations.encodeWord w87,TargetOperations.encodeWord w99,TargetOperations.encodeWord w7,TargetOperations.encodeWord w0],
  [TargetOperations.encodeWord w2,TargetOperations.encodeWord w2,TargetOperations.encodeWord (encoded p),TargetOperations.encodeWord w1,TargetOperations.encodeWord w0,TargetOperations.encodeWord w99,TargetOperations.encodeWord w7,TargetOperations.encodeWord w0],context (target p),context (target p)) := by cases p <;> rfl

private def badHistory (p : PrimTy) := history p ++ [(child 1,w2)]
/-- Touching the fresh HEADER defeats default provenance: actual push reads2,
then writes3/clears index2, leaving dirty87 at index0. No oldNone=>zero law. -/
theorem bad_history (p : PrimTy) :
 (LifecycleNumeric.pushPrimitive 64 hash (child 1) (FreshMappingHistory.numeric 64 hash (badHistory p))).map (fun s => [s 9,s 24,s 25,s 26]) = some [w3,w87,w99,w0] ∧
 ¬ Represented (Value.dflt (G:=G) (.array (.prim p))) (PrimitivePop.queries indices) (child 1) (FreshMappingHistory.symbolic (badHistory p)) := by
 refine ⟨rfl,?_⟩
 intro alleged
 have wrong := (alleged (.length .nil) List.mem_cons_self).2.2 w0 rfl
 change w2=w0 at wrong
 have bad:=congrArg (fun w : Semantics.Word => w.val) wrong
 change (2:Int)=0 at bad
 omega

/-- The graph operations preserve parent metadata and the generic certificate
has an inhabited successful inner operation for every primitive kind. -/
theorem total_and_header (p : PrimTy) :
 (∃ value, pushAt (middle p) (path p)=some value) ∧ (result p).head=(middle p).head :=
 ⟨inner_total (old p) (middle p) rfl rfl,outer_header (middle p) (result p) (ix 1) rfl⟩

/-- Actual SLOAD of the newly initialized payload and logical read agree. -/
theorem readback (p : PrimTy) :
 ((PrimitivePop.elementQuery (G:=G) (p:=p) (ix 0)).prefix (path p)).read (result p)=some w0 ∧
 finalNumeric p 24=w0 ∧
 Evm.run (TargetOperations.readCode (.data (.data (.root 0) 1) 0)) (finalTarget p)=
 .ok {finalTarget p with stack := .val (TargetOperations.encodeWord w0) :: (finalTarget p).stack} 0 := by cases p <;> exact ⟨rfl,rfl,rfl⟩

private def full (p : PrimTy) : Value G (.array (.array (.prim p))) :=
 .array ⟨2^256-1,by decide⟩ ⟨2^256-1,by decide⟩ (by decide) (fun _ => .absent)
/-- Original full-word guard fails before inner mutation; no world/catch
rollback or new allocation/profile premise is asserted. -/
theorem outer_failure (p : PrimTy) : operationPush (full p)=none ∧
 Evm.run (TargetHeaderPush.code (.root 0) ++ TargetPrimitivePush.code (.data (.root 0) 1))
 {target p with store := Evm.WordStore.write (target p).store (.root 0) (Evm.W-1)}=.revert := by
 constructor
 · rw [operationPush_failure]
   change 2^256≤2^256-1+1
   have positive : 0<2^256 := by decide
   omega
 · apply Evm.run_append_revert
   rw [TargetHeaderPush.run_current]
   rfl

/-- info: 'Solidity.Backend.StorageOps.FreshArrayHistory.Controls.readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms readback
/-- info: 'Solidity.Backend.StorageOps.FreshArrayHistory.Controls.outer_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms outer_failure
/-- info: 'Solidity.Backend.StorageOps.FreshArrayHistory.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.FreshArrayHistory.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.FreshArrayHistory.Controls.target_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_ordered
/-- info: 'Solidity.Backend.StorageOps.FreshArrayHistory.Controls.bad_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms bad_history
/-- info: 'Solidity.Backend.StorageOps.FreshArrayHistory.Controls.total_and_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms total_and_header
end Solidity.Backend.StorageOps.FreshArrayHistory.Controls
