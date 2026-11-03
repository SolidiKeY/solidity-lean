import Solidity.Backend.StorageOps.TargetNestedPop

/-! Actual target nested-pop controls and independent intrinsic graph reads.
These concrete readbacks are not a general represented/numeric/Source bridge. -/
namespace Solidity.Backend.StorageOps.TargetNestedPop.Controls
open TypeGraph Solidity.Storage.Representation.Graph
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
private def outer : Evm.Slot := .root 0
private def child (i : Nat) : Evm.Slot := .data outer i
private def cell (i j : Nat) : Evm.Slot := .data (child i) j
private def rawOpaque : Evm.Slot := .hash ⟨7,by decide⟩ (child 2) 0
private def store : Evm.WordStore := .ofFn fun s =>
 if s=outer then 3 else if s=child 0 then 3 else if s=child 1 then 0 else if s=child 2 then 2 else if s=child 3 then 1 else
 if s=cell 0 0 then 7 else if s=cell 0 1 then 17 else if s=cell 0 2 then 23 else if s=cell 0 3 then 71 else
 if s=cell 1 0 then 83 else if s=cell 2 0 then 53 else if s=cell 2 1 then 59 else if s=cell 2 2 then 61 else
 if s=cell 3 0 then 79 else if s=cell 3 1 then 89 else if s=rawOpaque then 77 else if s=.root 9 then 99 else 87
private def tail : List Evm.Word := [.val ⟨23,by decide⟩,.slot (.root 9)]
private def target : Evm.Machine :=
 {stack := tail,store := store,mem := fun _ => .val ⟨31,by decide⟩,
  bal := fun _ => 19,bal₀ := fun _ => 19,self := ⟨7,by decide⟩,caller := ⟨13,by decide⟩,
  callvalue := ⟨0,by decide⟩,timestamp := ⟨53,by decide⟩,accepts := fun _ _ => false}
private def out1 := after target outer
private def out2 := after out1 outer
private def out3 := after out2 outer
private def slots := [outer,child 0,child 1,child 2,child 3,cell 0 0,cell 0 1,cell 0 2,cell 0 3,
 cell 1 0,cell 2 0,cell 2 1,cell 2 2,cell 3 0,cell 3 1,rawOpaque,.root 9,.root 77]
private def view (m : Evm.Machine) := slots.map (fun s => m.store s)
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

theorem executions : Evm.run (code outer) target = .ok out1 0 ∧
 Evm.run (code outer) out1 = .ok out2 0 ∧ Evm.run (code outer) out2 = .ok out3 0 ∧
 Evm.run (code outer) out3 = .revert := by
 constructor
 · exact (run_current outer target).trans (by rfl)
 constructor
 · exact (run_current outer out1).trans (by rfl)
 constructor
 · exact (run_current outer out2).trans (by rfl)
 exact (run_current outer out3).trans (by rfl)

/-- Complete ordered target words and non-store contexts for every pop. -/
theorem ordered : (view target,view out1,view out2,view out3,
 contextView out1,contextView out2,contextView out3) =
 ([3,3,0,2,1,7,17,23,71,83,53,59,61,79,89,77,99,87],
  [2,3,0,0,1,7,17,23,71,83,0,0,61,79,89,77,99,87],
  [1,3,0,0,1,7,17,23,71,83,0,0,61,79,89,77,99,87],
  [0,0,0,0,1,0,0,0,71,83,0,0,61,79,89,77,99,87],
  contextView target,contextView target,contextView target) := by rfl

theorem graph_observations :
 (graphView old,graphView popped,graphView popped2,graphView popped3) =
 ((3,4,[some w3,some w0,some w2,some w1,some w7,some w17,some w23,some w71,some w83,some w53,some w59,some w61,some w79,some w89],some 2),
  (2,4,[some w3,some w0,some w0,some w1,some w7,some w17,some w23,some w71,some w83,some w0,some w0,some w61,some w79,some w89],none),
  (1,4,[some w3,some w0,some w0,some w1,some w7,some w17,some w23,some w71,some w83,some w0,some w0,some w61,some w79,some w89],none),
  (0,4,[some w0,some w0,some w0,some w1,some w0,some w0,some w0,some w71,some w83,some w0,some w0,some w61,some w79,some w89],none)) := by rfl

theorem graph_connection :
 (out1.store outer = popped.length.val ∧ popped.extent = old.extent) ∧
 (Evm.run (code outer) out3 = .revert ↔ recursivePop popped3 = none) :=
 ⟨graph_outer_header old popped rfl outer target rfl,failure_matches popped3 outer out3 rfl⟩

private def wrongCode := selectCode outer ++ (TargetArrayClear.code ++ TargetPrimitivePop.headerCode outer)
private def wrongChild := TargetArrayClear.afterClear target target.stack (child 3)
private def wrongOut := decremented wrongChild outer

/-- Selecting from OLD outer length clears the older child3 instead of last
live child2. The actual wrong program still decrements the outer header. -/
theorem wrong_order : Evm.run wrongCode target = .ok wrongOut 0 ∧
 view wrongOut = [2,3,0,2,0,7,17,23,71,83,53,59,61,0,89,77,99,87] ∧
 view wrongOut ≠ view out1 := by
 constructor
 · unfold wrongCode
   rw [Evm.run_append_ok (run_select outer target)]
   change Evm.run (TargetArrayClear.code ++ TargetPrimitivePop.headerCode outer)
     {target with stack := .slot (child 3) :: target.stack} = _
   rw [Evm.run_append_ok (TargetArrayClear.run_current target target.stack (child 3)),TargetPrimitivePop.run_header]
   rfl
 exact ⟨rfl,by decide⟩

theorem all_other_children (i j : Nat) (other : i ≠ 2) :
 out1.store (child i) = target.store (child i) ∧ out1.store (cell i j) = target.store (cell i j) :=
 ⟨other_child_header outer target i other,other_child_data outer target i j other⟩

private def absentOld : Value graph (.array (.array (.prim .uint))) :=
 .array ⟨1,by decide⟩ ⟨1,by decide⟩ (by decide) (fun _ => .absent)
private def absentPopped := (recursivePop absentOld).getD absentOld
private def absentTarget : Evm.Machine := {target with store := .ofFn (fun s => if s=outer then 1 else if s=child 0 then 0 else 93)}
private def absentOut := after absentTarget outer

/-- Absent child defaults are logical; its zero live header does not license
clearing any retained raw payload or treating failed graph reads as zero. -/
theorem absence_boundary : Evm.run (code outer) absentTarget = .ok absentOut 0 ∧
 ((hq (ix 0)).read absentPopped,(wq (ix 0) (ix 0)).read absentPopped,
   absentOut.store outer,absentOut.store (child 0),absentOut.store (cell 0 0),absentOut.store (child 3)) =
 (some w0,none,0,0,93,93) := by
 exact ⟨(run_current outer absentTarget).trans (by rfl),rfl⟩

/-- Opaque hashed raw cells are framed by the ACTUAL symbolic access shape;
this is not a claim that primitive elements admit mapping-typed children. -/
theorem opaque_frame : out1.store rawOpaque = target.store rawOpaque :=
 outside outer target rawOpaque (by intro same; cases same) (by intro same; cases same)
   (by intro j _ same; cases same)

/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.Controls.executions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms executions
/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.Controls.ordered' does not depend on any axioms -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.Controls.graph_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms graph_observations
/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.Controls.graph_connection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms graph_connection
/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.Controls.wrong_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_order
/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.Controls.all_other_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms all_other_children
/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.Controls.absence_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms absence_boundary
/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.Controls.opaque_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms opaque_frame
end Solidity.Backend.StorageOps.TargetNestedPop.Controls
