import Solidity.Backend.StorageOps.NumericRetainedCycle

/-! Actual numeric/target retained-cycle controls with an inhabited finite run
and a physically colliding counterexample. No new Source or world evaluator. -/
namespace Solidity.Backend.StorageOps.NumericRetainedCycle.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
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
private def w87 : Semantics.Word := ⟨87,by decide⟩
private def w93 : Semantics.Word := ⟨93,by decide⟩
private def w99 : Semantics.Word := ⟨99,by decide⟩
private def w91 : Semantics.Word := ⟨91,by decide⟩
private def w97 : Semantics.Word := ⟨97,by decide⟩
private def base : Solidity.Storage.Loc := .root 0
private def cb (i : Nat) : Solidity.Storage.Loc := .data base i
private def dataLoc (i j : Nat) : Solidity.Storage.Loc := .data (cb i) j
private def childBase := cb 2
private def hash (p : Solidity.Storage.Pre) : Nat := if p=.data 0 then 16 else if p=.data 16 then 48 else
 if p=.data 17 then 64 else if p=.data 18 then 80 else if p=.data 19 then 96 else if p=.data 20 then 112 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 16,.data 17,.data 18,.data 19,.data 20]
private def locations : List Solidity.Storage.Loc := [base,cb 0,cb 1,cb 2,cb 3,cb 4,
 dataLoc 0 0,dataLoc 0 1,dataLoc 0 2,dataLoc 0 3,dataLoc 1 0,dataLoc 1 1,
 dataLoc 2 0,dataLoc 2 1,dataLoc 2 2,dataLoc 2 3,dataLoc 3 0,dataLoc 3 1,dataLoc 4 0]
private def numeric : WordStore := fun a =>
 if a=0 then w3 else if a=16 then w3 else if a=17 then w0 else if a=18 then w2 else if a=19 then w1 else if a=20 then w91 else if a=48 then w7 else if a=49 then w17 else if a=50 then w23 else if a=51 then w71 else if a=64 then w83 else if a=65 then w93 else if a=80 then w53 else if a=81 then w59 else if a=82 then w61 else if a=83 then w93 else if a=96 then w79 else if a=97 then w89 else if a=112 then w97 else if a=7 then w99 else w87
private def outer : Evm.Slot := .root 0
private def child (i : Nat) : Evm.Slot := .data outer i
private def cell (i j : Nat) : Evm.Slot := .data (child i) j
private def rawOpaque : Evm.Slot := .hash ⟨7,by decide⟩ (child 2) 0
private def store : Evm.WordStore := .ofFn fun s =>
 if s=outer then 3 else if s=child 0 then 3 else if s=child 1 then 0 else if s=child 2 then 2 else if s=child 3 then 1 else
 if s=cell 0 0 then 7 else if s=cell 0 1 then 17 else if s=cell 0 2 then 23 else if s=cell 0 3 then 71 else
 if s=cell 1 0 then 83 else if s=cell 2 0 then 53 else if s=cell 2 1 then 59 else if s=cell 2 2 then 61 else
 if s=child 4 then 91 else if s=cell 4 0 then 97 else if s=cell 1 1 then 93 else if s=cell 2 3 then 93 else if s=cell 3 0 then 79 else if s=cell 3 1 then 89 else if s=rawOpaque then 77 else if s=.root 7 then 99 else 87
private def tail : List Evm.Word := [.val ⟨23,by decide⟩,.slot (.root 7)]
private def target : Evm.Machine :=
 {stack := tail,store := store,mem := fun _ => .val ⟨31,by decide⟩,
  bal := fun _ => 19,bal₀ := fun _ => 19,self := ⟨7,by decide⟩,caller := ⟨13,by decide⟩,
  callvalue := ⟨0,by decide⟩,timestamp := ⟨53,by decide⟩,accepts := fun _ _ => false}
private def popTarget := TargetNestedPop.after target outer
private def popNumeric := TargetClearRepresentation.execute 256 hash childBase (writeWord numeric 0 w2)
private theorem run : FiniteRun 256 8 1 hash preimages locations := by
 constructor
 · intro p; simp only [hash]; split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [base,cb,dataLoc,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem fitting : ∀ l ∈ locations, TargetOperations.KeysFit l := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
private def numericView (m : WordStore) := [m 0,m 16,m 17,m 18,m 19,m 20,m 48,m 49,m 50,m 51,m 64,m 65,m 80,m 81,m 82,m 83,m 96,m 97,m 112,m 7,m 255]
private def targets : List Evm.Slot := [.root 0,child 0,child 1,child 2,child 3,child 4,cell 0 0,cell 0 1,cell 0 2,cell 0 3,cell 1 0,cell 1 1,cell 2 0,cell 2 1,cell 2 2,cell 2 3,cell 3 0,cell 3 1,cell 4 0,rawOpaque,.root 7,.root 255]
private def targetView (m : Evm.Machine) := targets.map (fun s => m.store s)

private def grown := writeWord popNumeric 0 w3
private def result := (popRegrowPop 256 hash base numeric).getD numeric
private def targetGrown := TargetHeaderPush.incremented outer popTarget
private def targetResult := TargetNestedPop.after targetGrown outer
private def machineContext (m : Evm.Machine) :=
 (m.stack,m.mem 0,m.bal m.self,m.bal₀ m.self,m.self,m.caller,m.callvalue,m.timestamp,m.accepts m.self m.self)
private theorem visited (j : Nat) (live : j < LifecycleNumeric.headerLength 256 hash
 (.data base (LifecycleNumeric.headerLength 256 hash base numeric-1))
 (writeWord numeric (base.word 256 hash) (lengthWord (LifecycleNumeric.headerLength 256 hash base numeric-1) (by decide)))) :
 Solidity.Storage.Loc.data (.data base (LifecycleNumeric.headerLength 256 hash base numeric-1)) j ∈ locations := by
 change j < 2 at live
 have cases : j=0 ∨ j=1 := by omega
 rcases cases with rfl | rfl <;> decide

/-- The initial finite run derives the two actual middle words. -/
theorem headers : popNumeric 0 = w2 ∧ popNumeric 18 = w0 :=
 popped_headers run base numeric popNumeric rfl (by decide) (by decide) visited

theorem executions : popRegrowPop 256 hash base numeric = some popNumeric ∧
 reuse 256 hash base popNumeric = some popNumeric ∧
 Evm.run (TargetRetainedCycle.popRegrowPop outer) target = .ok popTarget 0 ∧
 Evm.run (TargetRetainedCycle.code outer) popTarget = .ok popTarget 0 := by
 have paired := paired_reuse 256 hash base popNumeric popTarget True.intro (by decide) rfl rfl rfl
 refine ⟨(outcome run base numeric (by decide) (by decide) visited).trans (by rfl),
   paired.1,
   (TargetRetainedCycle.run_pop_regrow_pop target outer).trans (by rfl),
   paired.2⟩

/-- Inhabited actual numeric and target executions agree at ALL covered words. -/
theorem paired_agreement : ∀ l (member : l ∈ locations),
 targetResult.store.cells (TargetOperations.toSlot l (fitting l member)) =
 TargetOperations.encodeWord (result (l.word 256 hash)) := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem ordered : (numericView numeric,numericView popNumeric,numericView grown,numericView result,
 targetView target,targetView popTarget,targetView targetGrown,targetView targetResult,
 machineContext popTarget,machineContext targetGrown,machineContext targetResult) =
 ([w3,w3,w0,w2,w1,w91,w7,w17,w23,w71,w83,w93,w53,w59,w61,w93,w79,w89,w97,w99,w87],
  [w2,w3,w0,w0,w1,w91,w7,w17,w23,w71,w83,w93,w0,w0,w61,w93,w79,w89,w97,w99,w87],
  [w3,w3,w0,w0,w1,w91,w7,w17,w23,w71,w83,w93,w0,w0,w61,w93,w79,w89,w97,w99,w87],
  [w2,w3,w0,w0,w1,w91,w7,w17,w23,w71,w83,w93,w0,w0,w61,w93,w79,w89,w97,w99,w87],
  [3,3,0,2,1,91,7,17,23,71,83,93,53,59,61,93,79,89,97,77,99,87],
  [2,3,0,0,1,91,7,17,23,71,83,93,0,0,61,93,79,89,97,77,99,87],
  [3,3,0,0,1,91,7,17,23,71,83,93,0,0,61,93,79,89,97,77,99,87],
  [2,3,0,0,1,91,7,17,23,71,83,93,0,0,61,93,79,89,97,77,99,87],
  machineContext target,machineContext target,machineContext target) := by rfl

private def uncleared := (reuse 256 hash base numeric).getD numeric
theorem uncleared_negative : numericView uncleared =
 [w3,w3,w0,w2,w0,w91,w7,w17,w23,w71,w83,w93,w53,w59,w61,w93,w0,w89,w97,w99,w87] ∧
 uncleared ≠ numeric := by
 refine ⟨rfl,?_⟩
 intro same
 have observed := congrFun same 96
 change w0 = w79 at observed
 exact (by decide : w0 ≠ w79) observed

private def badHash (p : Solidity.Storage.Pre) : Nat := if p=.data 18 then 0 else hash p
private def badFirst := (NestedPopTransport.execute 256 badHash base numeric).getD numeric
private def badResult := (popRegrowPop 256 badHash base numeric).getD numeric
/-- Missing per-run separation allows an inner write to erase the root header,
then regrowth selects another live child. Actual operation results discriminate it. -/
theorem collision_negative :
 ¬ FiniteRun 256 8 1 badHash preimages locations ∧
 (numericView badFirst,numericView badResult) =
 ([w0,w3,w0,w0,w1,w91,w7,w17,w23,w71,w83,w93,w53,w59,w61,w93,w79,w89,w97,w99,w87],
  [w0,w0,w0,w0,w1,w91,w0,w0,w0,w71,w83,w93,w53,w59,w61,w93,w79,w89,w97,w99,w87]) ∧
 badResult ≠ badFirst := by
 constructor
 · intro alleged
   have impossible : base = dataLoc 2 0 := alleged.word_inj (by decide) (by decide) (by rfl)
   cases impossible
 refine ⟨rfl,?_⟩
 intro same
 have observed := congrFun same 48
 change w0 = w7 at observed
 exact (by decide : w0 ≠ w7) observed

private def full := writeWord numeric 0 (lengthWord (2^256-1) (by decide))
private def empty := writeWord numeric 0 w0
theorem failures : reuse 256 hash base full = none ∧
 popRegrowPop 256 hash base empty = none :=
 ⟨capacity_failure 256 hash base full (by decide),rfl⟩

/-- info: 'Solidity.Backend.StorageOps.NumericRetainedCycle.Controls.headers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms headers
/-- info: 'Solidity.Backend.StorageOps.NumericRetainedCycle.Controls.executions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms executions
/-- info: 'Solidity.Backend.StorageOps.NumericRetainedCycle.Controls.paired_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms paired_agreement
/-- info: 'Solidity.Backend.StorageOps.NumericRetainedCycle.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.NumericRetainedCycle.Controls.uncleared_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms uncleared_negative
/-- info: 'Solidity.Backend.StorageOps.NumericRetainedCycle.Controls.collision_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms collision_negative
/-- info: 'Solidity.Backend.StorageOps.NumericRetainedCycle.Controls.failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failures
end Solidity.Backend.StorageOps.NumericRetainedCycle.Controls
