import Solidity.Backend.StorageOps.NestedPopTransport

/-! Concrete PUBLIC root/child owner and per-run physical transport clients for
actual current-header numeric/target nested pop; failed queries are not zero. -/
namespace Solidity.Backend.StorageOps.NestedPopTransport.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def graph : Schema 0 where
 origin := "v10-target-nested-pop"
 declId := fun i => nomatch i
 declId_injective := by intro i; exact Fin.elim0 i
 name := fun i => nomatch i
 fields := fun i => nomatch i
 rank := fun i => nomatch i
 nonempty := by intro i; exact Fin.elim0 i
 distinct := by intro i; exact Fin.elim0 i
 guarded := by intro i; exact Fin.elim0 i
private def ix (i : Fin 5) : Index := ⟨i.val,by have bound := i.isLt; omega⟩
private def w0 : Semantics.Word := ⟨0,by decide⟩
private def w1 : Semantics.Word := ⟨1,by decide⟩
private def w2 : Semantics.Word := ⟨2,by decide⟩
private def w3 : Semantics.Word := ⟨3,by decide⟩
private def w7 : Semantics.Word := ⟨7,by decide⟩
private def w17 : Semantics.Word := ⟨17,by decide⟩
private def w23 : Semantics.Word := ⟨23,by decide⟩
private def w53 : Semantics.Word := ⟨53,by decide⟩
private def w59 : Semantics.Word := ⟨59,by decide⟩
private def w61 : Semantics.Word := ⟨61,by decide⟩
private def w71 : Semantics.Word := ⟨71,by decide⟩
private def w79 : Semantics.Word := ⟨79,by decide⟩
private def w83 : Semantics.Word := ⟨83,by decide⟩
private def w89 : Semantics.Word := ⟨89,by decide⟩
private def child0 : Value graph (.array (.prim .uint)) :=
 .array ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide)
 (fun i => .present (.prim (if i.val=0 then w7 else if i.val=1 then w17 else if i.val=2 then w23 else w71)))
private def child1 : Value graph (.array (.prim .uint)) :=
 .array ⟨1,by decide⟩ ⟨0,by decide⟩ (by decide) (fun _ => .present (.prim w83))
private def child2 : Value graph (.array (.prim .uint)) :=
 .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide)
 (fun i => .present (.prim (if i.val=0 then w53 else if i.val=1 then w59 else w61)))
private def child3 : Value graph (.array (.prim .uint)) :=
 .array ⟨2,by decide⟩ ⟨1,by decide⟩ (by decide) (fun i => .present (.prim (if i.val=0 then w79 else w89)))
private def old : Value graph (.array (.array (.prim .uint))) :=
 .array ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide)
 (fun i => .present (if i.val=0 then child0 else if i.val=1 then child1 else if i.val=2 then child2 else child3))
private def popped := (recursivePop old).getD old
private def popped2 := (recursivePop popped).getD old
private def popped3 := (recursivePop popped2).getD old
private def w87 : Semantics.Word := ⟨87,by decide⟩
private def w93 : Semantics.Word := ⟨93,by decide⟩
private def w99 : Semantics.Word := ⟨99,by decide⟩
private def indices : List Index := [ix 3,ix 2,ix 0,ix 1,ix 2]
private def base : Solidity.Storage.Loc := .root 0
private def childBase : Solidity.Storage.Loc := .data base 2
private def hash (p : Solidity.Storage.Pre) : Nat := if p=.data 0 then 8 else if p=.data 10 then 24 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 10]
private def locations : List Solidity.Storage.Loc := [base,childBase,.data childBase 0,.data childBase 1,.data childBase 2,.data childBase 3]
private def symbolic : Store := fun l => if l=base then w3 else if l=childBase then w2 else
 if l=.data childBase 0 then w53 else if l=.data childBase 1 then w59 else if l=.data childBase 2 then w61 else
 if l=.data childBase 3 then w93 else if l=.root 7 then w99 else w87
private def numeric : WordStore := fun a => if a=0 then w3 else if a=10 then w2 else if a=24 then w53 else
 if a=25 then w59 else if a=26 then w61 else if a=27 then w93 else if a=7 then w99 else w87
private def outer : Evm.Slot := .root 0
private def child (i : Nat) : Evm.Slot := .data outer i
private def cell (i j : Nat) : Evm.Slot := .data (child i) j
private def rawOpaque : Evm.Slot := .hash ⟨7,by decide⟩ (child 2) 0
private def store : Evm.WordStore := .ofFn fun s =>
 if s=outer then 3 else if s=child 0 then 3 else if s=child 1 then 0 else if s=child 2 then 2 else if s=child 3 then 1 else
 if s=cell 0 0 then 7 else if s=cell 0 1 then 17 else if s=cell 0 2 then 23 else if s=cell 0 3 then 71 else
 if s=cell 1 0 then 83 else if s=cell 2 0 then 53 else if s=cell 2 1 then 59 else if s=cell 2 2 then 61 else
 if s=cell 2 3 then 93 else if s=cell 3 0 then 79 else if s=cell 3 1 then 89 else if s=rawOpaque then 77 else if s=.root 7 then 99 else 87
private def tail : List Evm.Word := [.val ⟨23,by decide⟩,.slot (.root 7)]
private def target : Evm.Machine :=
 {stack := tail,store := store,mem := fun _ => .val ⟨31,by decide⟩,
  bal := fun _ => 19,bal₀ := fun _ => 19,self := ⟨7,by decide⟩,caller := ⟨13,by decide⟩,
  callvalue := ⟨0,by decide⟩,timestamp := ⟨53,by decide⟩,accepts := fun _ _ => false}
private def targetOut := TargetNestedPop.after target outer
private def finalNumeric := TargetClearRepresentation.execute 64 hash childBase (writeWord numeric 0 w2)
private def finalStore := TargetClearRepresentation.afterStore (childValue old) childBase (Representation.write symbolic base w2)
private theorem run : FiniteRun 64 4 1 hash preimages locations := by
 constructor
 · intro p; simp only [hash]; split <;> (try split) <;> decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [base,childBase,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem rootBefore : Represented old [.length .nil] base symbolic := by
 intro query member
 have same := List.mem_singleton.mp member
 subst query
 refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
 intro word found
 change some w3 = some word at found
 cases found
 rfl
private theorem fullChild : Represented (childValue old) (PrimitivePop.queries indices) childBase symbolic := by
 intro query member
 simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl
 · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
   intro word found
   change some w2 = some word at found
   cases found
   rfl
 · refine ⟨⟨by change 3 < lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change none = some word at found
   cases found
 · refine ⟨⟨by change 2 < lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some w61 = some word at found
   cases found
   rw [PrimitivePop.element_location]
   rfl
 · refine ⟨⟨by change 0 < lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some w53 = some word at found
   cases found
   rw [PrimitivePop.element_location]
   rfl
 · refine ⟨⟨by change 1 < lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some w59 = some word at found
   cases found
   rw [PrimitivePop.element_location]
   rfl
 · refine ⟨⟨by change 2 < lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some w61 = some word at found
   cases found
   rw [PrimitivePop.element_location]
   rfl
private theorem childBefore : Represented (childValue old) (TargetClearRepresentation.oldQueries (childValue old) indices) childBase symbolic := by
 intro query member
 apply fullChild query
 simp only [TargetClearRepresentation.oldQueries,PrimitivePop.queries,List.mem_cons,List.mem_map] at member
 rcases member with rfl | ⟨i,inside,rfl⟩
 · exact List.mem_cons_self
 · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,(List.mem_filter.mp inside).1,rfl⟩)
private theorem initial : Transport 64 hash locations symbolic numeric := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem covered : ∀ query ∈ PrimitivePop.queries (G := graph) (p := .uint) indices, query.location childBase ∈ locations := by
 intro query member
 simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> (try rw [PrimitivePop.element_location]) <;> decide
private theorem visited : ∀ j, j < (childValue old).length.val → Solidity.Storage.Loc.data childBase j ∈ locations := by
 intro j inside
 change j < 2 at inside
 have cases : j=0 ∨ j=1 := by omega
 rcases cases with rfl | rfl <;> decide
private theorem fitting : ∀ l ∈ locations, TargetOperations.KeysFit l := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
private theorem targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (symbolic l) := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Every actual successful operation premise is inhabited. -/
theorem bridge :
 execute 64 hash base numeric = some finalNumeric ∧
 Evm.run (TargetNestedPop.code outer) target = .ok targetOut 0 ∧
 Represented (childValue old).clear (PrimitivePop.queries indices) childBase finalStore ∧
 Represented popped (AggregatePop.queries old (PrimitivePop.queries indices)) base finalStore ∧
 Transport 64 hash locations finalStore finalNumeric ∧
 (∀ l (member : l ∈ locations), targetOut.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (finalNumeric (l.word 64 hash))) ∧
 (∀ query ∈ PrimitivePop.queries (G := graph) (p := .uint) indices, ∀ word, query.read (childValue old).clear = some word →
   finalNumeric ((query.location childBase).word 64 hash) = word) :=
 complete run old popped rfl indices base True.intro symbolic numeric target rootBefore childBefore initial (by decide) covered visited fitting targetInitial

private def physicalView (m : WordStore) := [m 0,m 10,m 24,m 25,m 26,m 27,m 7,m 63]
private def symbolicView (s : Store) := [s base,s childBase,s (.data childBase 0),s (.data childBase 1),s (.data childBase 2),s (.data childBase 3),s (.root 7),s (.root 63)]
private def targetSlots := [outer,child 0,child 1,child 2,child 3,cell 0 0,cell 0 1,cell 0 2,cell 0 3,
 cell 1 0,cell 2 0,cell 2 1,cell 2 2,cell 2 3,cell 3 0,cell 3 1,rawOpaque,.root 7,.root 63]
private def targetView (m : Evm.Machine) := targetSlots.map (fun s => m.store s)
private def contextView (m : Evm.Machine) :=
 (m.stack,m.mem 0,m.bal m.self,m.bal₀ m.self,m.self,m.caller,m.callvalue,m.timestamp,m.accepts m.self m.self)
private def path (i : Index) : TypeGraph.Path graph (.array (.array (.prim .uint))) (.array (.prim .uint)) := .cons (.index i) .nil
private def hq (i : Index) : Query graph (.array (.array (.prim .uint))) := .length (path i)
private def wq (i j : Index) : Query graph (.array (.array (.prim .uint))) := .word (.cons (.index i) (.cons (.index j) .nil))
private def graphView (v : Value graph (.array (.array (.prim .uint)))) :=
 (v.length.val,v.extent.val,[(hq (ix 0)).read v,(hq (ix 1)).read v,(hq (ix 2)).read v,(hq (ix 3)).read v,
  (wq (ix 0) (ix 0)).read v,(wq (ix 0) (ix 1)).read v,(wq (ix 0) (ix 2)).read v,(wq (ix 0) (ix 3)).read v,
  (wq (ix 1) (ix 0)).read v,(wq (ix 2) (ix 0)).read v,(wq (ix 2) (ix 1)).read v,(wq (ix 2) (ix 2)).read v,
  (wq (ix 3) (ix 0)).read v,(wq (ix 3) (ix 1)).read v],
  ((path (ix 2)).readLive Value.dflt v).map (fun child => child.length.val))

/-- All recorded graph, symbolic, physical, target and context observations. -/
theorem ordered :
 (graphView old,graphView popped,symbolicView symbolic,symbolicView finalStore,
  physicalView numeric,physicalView finalNumeric,targetView target,targetView targetOut,contextView targetOut) =
 ((3,4,[some w3,some w0,some w2,some w1,some w7,some w17,some w23,some w71,some w83,some w53,some w59,some w61,some w79,some w89],some 2),
  (2,4,[some w3,some w0,some w0,some w1,some w7,some w17,some w23,some w71,some w83,some w0,some w0,some w61,some w79,some w89],none),
  [w3,w2,w53,w59,w61,w93,w99,w87],[w2,w0,w0,w0,w61,w93,w99,w87],
  [w3,w2,w53,w59,w61,w93,w99,w87],[w2,w0,w0,w0,w61,w93,w99,w87],
  [3,3,0,2,1,7,17,23,71,83,53,59,61,93,79,89,77,99,87],
  [2,3,0,0,1,7,17,23,71,83,0,0,61,93,79,89,77,99,87],contextView target) := by rfl
private def wrongNumeric := (execute 64 hash base (writeWord numeric 10 w3)).getD numeric

/-- Mismatching the original represented child header2 with actual3 erases
retained61. Actual outer decrement still succeeds; initial transport matters. -/
theorem wrong_header : physicalView wrongNumeric = [w2,w0,w0,w0,w0,w93,w99,w87] ∧
 wrongNumeric 26 ≠ finalNumeric 26 := by
 exact ⟨rfl,by decide⟩

theorem collision_control : ¬ FiniteRun 64 4 1 (fun _ => 0) preimages locations := by
 intro bad
 have same := bad.word_inj (a := base) (b := .data childBase 0) (by decide) (by decide) rfl
 cases same

theorem boundaries :
 ((PrimitivePop.elementQuery (ix 3)).read (childValue old).clear,
  ((path (ix 2)).readLive Value.dflt popped).map (fun c => c.length.val),
  finalNumeric 27,targetOut.store (cell 2 3),finalNumeric 26,targetOut.store (cell 2 2)) =
 (none,none,w93,93,w61,61) := by rfl

private def emptyNumeric := writeWord numeric 0 w0
private def emptyStore := Representation.write symbolic base w0
private def emptyTarget : Evm.Machine := {target with store := Evm.WordStore.write target.store outer 0}
private theorem emptyBefore : Represented popped3 [.length .nil] base emptyStore := by
 intro query member
 have same := List.mem_singleton.mp member
 subst query
 refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
 intro word found
 change some w0 = some word at found
 cases found
 exact Representation.write_same _ _ _

theorem empty_control : execute 64 hash base emptyNumeric = none ∧
 (execute 64 hash base emptyNumeric = none ↔ recursivePop popped3 = none) ∧
 Evm.run (TargetNestedPop.code outer) emptyTarget = .revert :=
 ⟨rfl,failure_matches popped3 base emptyStore emptyNumeric hash locations emptyBefore
   (transport_write run initial base (by decide) w0) (by decide),
   (TargetNestedPop.run_current outer emptyTarget).trans (by rfl)⟩

private def absentOld : Value graph (.array (.array (.prim .uint))) :=
 .array ⟨1,by decide⟩ ⟨1,by decide⟩ (by decide) (fun _ => .absent)
private def absentResult := (recursivePop absentOld).getD absentOld
private def absentBase : Solidity.Storage.Loc := .data base 0
private def absentHash (p : Solidity.Storage.Pre) : Nat := if p=.data 0 then 8 else if p=.data 8 then 24 else 0
private def absentP : List Solidity.Storage.Pre := [.data 0,.data 8]
private def absentLocations : List Solidity.Storage.Loc := [base,absentBase,.data absentBase 0]
private def absentSymbolic : Store := fun l => if l=base then w1 else if l=absentBase then w0 else w93
private def absentNumeric : WordStore := fun a => if a=0 then w1 else if a=8 then w0 else w93
private def absentTarget : Evm.Machine := {target with store := .ofFn (fun s => if s=outer then 1 else if s=child 0 then 0 else 93)}
private def absentFinal := TargetClearRepresentation.execute 64 absentHash absentBase (writeWord absentNumeric 0 w0)
private def absentStoreOut := TargetClearRepresentation.afterStore (childValue absentOld) absentBase (Representation.write absentSymbolic base w0)
private theorem absentRun : FiniteRun 64 4 1 absentHash absentP absentLocations := by
 constructor
 · intro p; simp only [absentHash]; split <;> (try split) <;> decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [absentLocations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl <;> simp only [absentBase,base,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [absentLocations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl <;> decide
private theorem absentRootBefore : Represented absentOld [.length .nil] base absentSymbolic := by
 intro query member
 have same := List.mem_singleton.mp member; subst query
 refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
 intro word found
 change some w1 = some word at found
 cases found
 rfl
private theorem absentChildBefore : Represented (childValue absentOld)
 (TargetClearRepresentation.oldQueries (childValue absentOld) []) absentBase absentSymbolic := by
 intro query member
 have same : query = .length .nil := List.mem_singleton.mp member
 subst query
 refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
 intro word found
 change some w0 = some word at found
 cases found
 rfl
private theorem absentInitial : Transport 64 absentHash absentLocations absentSymbolic absentNumeric := by
 intro l member
 simp only [absentLocations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl <;> rfl
private theorem absentFits : ∀ l ∈ absentLocations, TargetOperations.KeysFit l := by
 intro l member
 simp only [absentLocations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl <;> trivial
private theorem absentTargetInitial : ∀ l (member : l ∈ absentLocations),
 absentTarget.store.cells (TargetOperations.toSlot l (absentFits l member)) = TargetOperations.encodeWord (absentSymbolic l) := by
 intro l member
 simp only [absentLocations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl <;> rfl

/-- Main certificate instantiated also for an ABSENT selected slot, with a
covered nonzero raw payload. It clears no fictitious default child payload. -/
theorem absent_bridge :
 execute 64 absentHash base absentNumeric = some absentFinal ∧
 Evm.run (TargetNestedPop.code outer) absentTarget = .ok (TargetNestedPop.after absentTarget outer) 0 ∧
 Represented absentResult (AggregatePop.queries absentOld (PrimitivePop.queries [])) base absentStoreOut ∧
 Transport 64 absentHash absentLocations absentStoreOut absentFinal ∧
 ((PrimitivePop.elementQuery (ix 0)).read (childValue absentOld).clear,
   absentFinal 0,absentFinal 8,absentFinal 24,(TargetNestedPop.after absentTarget outer).store (cell 0 0)) =
 (none,w0,w0,w93,93) := by
 have certificate := complete absentRun absentOld absentResult rfl [] base True.intro absentSymbolic absentNumeric absentTarget
   absentRootBefore absentChildBefore absentInitial (by decide)
   (by intro query member; have same : query = .length .nil := List.mem_singleton.mp member; subst query; decide)
   (by intro j inside; change j < 0 at inside; omega) absentFits absentTargetInitial
 exact ⟨certificate.1,certificate.2.1,certificate.2.2.2.1,certificate.2.2.2.2.1,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.NestedPopTransport.Controls.bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms bridge
/-- info: 'Solidity.Backend.StorageOps.NestedPopTransport.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.NestedPopTransport.Controls.wrong_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_header
/-- info: 'Solidity.Backend.StorageOps.NestedPopTransport.Controls.collision_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms collision_control
/-- info: 'Solidity.Backend.StorageOps.NestedPopTransport.Controls.boundaries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms boundaries
/-- info: 'Solidity.Backend.StorageOps.NestedPopTransport.Controls.empty_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_control
/-- info: 'Solidity.Backend.StorageOps.NestedPopTransport.Controls.absent_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms absent_bridge
end Solidity.Backend.StorageOps.NestedPopTransport.Controls
