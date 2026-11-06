import Solidity.Backend.StorageOps.GraphRetainedCycle

/-! Inhabited exact graph-cycle controls. Raw slot presence and defaulted reads
are distinct; these are not numeric/target/Source/world lifecycle certificates. -/
namespace Solidity.Backend.StorageOps.GraphRetainedCycle.Controls
open TypeGraph
private def z : Fin 1 := ⟨0, by decide⟩
private def fs : List (Name × TypeGraph.Ty 1) :=
  [("flag", .prim .bool), ("children", .array (.node z)),
   ("memo", .mapping .bool (.prim .bool))]
private def graph : Schema 1 where
  origin := "v10-clear-operation-controls"
  declId := fun _ => 0
  declId_injective := by intro i j _; apply Fin.ext; omega
  name := fun _ => "MemoNode"
  fields := fun _ => fs
  rank := fun _ => 1
  nonempty := fun _ => rfl
  distinct := fun _ => rfl
  guarded := by
    intro i f hf
    simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> exact Nat.zero_lt_succ 0

private def zero : Index := ⟨0, by decide⟩
private abbrev Map := Value graph (.mapping .bool (.prim .bool))
private abbrev Nodes := Value graph (.array (.node z))
private abbrev Node := Value graph (.node z)
private def oldMemo : Map := .mapping (fun _ => .present (.prim true))
private def srcMemo : Map := .mapping (fun _ => .present (.prim false))
private def empty : Nodes := Value.dflt _
private def node (flag : Bool) (children : Nodes) (memo : Map) : Node :=
  .node (fun p => match p with
    | .here => .prim flag
    | .there .here => children
    | .there (.there .here) => memo
    | .there (.there (.there q)) => nomatch q)
private def one (v : Node) : Nodes :=
  .array ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide) (fun _ => .present v)

private def tree (width : Nat → Index) : Nat → Nodes
  | 0 => .array ⟨(width 0).val, by have h := (width 0).isLt; omega⟩ (width 0) (Nat.le_refl _)
      (fun _ => .present (node true empty oldMemo))
  | d+1 => .array ⟨(width (d+1)).val, by have h := (width (d+1)).isLt; omega⟩ (width (d+1)) (Nat.le_refl _)
      (fun _ => .present (node true (tree width d) oldMemo))
private def deep : Nat → TypeGraph.Path graph (.array (.node z)) (.prim .bool)
  | 0 => .cons (.index zero) (.cons (.field .here) .nil)
  | d+1 => .cons (.index zero) (.cons (.field (.there .here)) (deep d))
private def deepMemo : Nat → TypeGraph.Path graph (.array (.node z)) (.mapping .bool (.prim .bool))
  | 0 => .cons (.index zero) (.cons (.field (.there (.there .here))) .nil)
  | d+1 => .cons (.index zero) (.cons (.field (.there .here)) (deepMemo d))

private def i1 : Index := ⟨1, by decide⟩
private def i2 : Index := ⟨2, by decide⟩
private def ids : List Index := [zero, i1, i2]
private def flag (i : Index) : TypeGraph.Path graph (.array (.node z)) (.prim .bool) :=
  .cons (.index i) (.cons (.field .here) .nil)
private def child (i : Index) : TypeGraph.Path graph (.array (.node z)) (.array (.node z)) :=
  .cons (.index i) (.cons (.field (.there .here)) .nil)
private def memo (i : Index) (key : Bool) : TypeGraph.Path graph (.array (.node z)) (.prim .bool) :=
  .cons (.index i) (.cons (.field (.there (.there .here))) (.cons (.key key) .nil))
private def inner : Nodes := .array ⟨2, by decide⟩ i1 (by decide)
  (fun _ => .present (node true empty oldMemo))
private def slots : Fin 3 → Slot graph (.node z) := fun _ => .present (node true inner oldMemo)
private def old : Nodes := .array ⟨3, by decide⟩ i2 (by decide) slots
private def retained : Nodes := .array ⟨3, by decide⟩ zero (by decide) slots
private def bit (b : Bool) : Nat := if b then 1 else 0
private def word (v : Nodes) (p : TypeGraph.Path graph (.array (.node z)) (.prim .bool)) : Option Nat :=
  (v.observe p).map bit

/-- Ordered complete fixture view: header; then for indices0,1,2: scalar,
both mapping keys, child header, both child slots' scalar/both keys/empty-array
header, and outer/inner0/inner1 live-read availability. No fixture field omitted. -/
private def nodeObservations (v : Nodes) (i : Index) : List (Option Nat) :=
  [word v (flag i), word v (memo i true), word v (memo i false),
   ((v.find (child i)).map (fun a => a.length.val)), ((v.find (child i)).map (fun a => a.extent.val)),
   word v ((child i).append (flag zero)), word v ((child i).append (memo zero true)), word v ((child i).append (memo zero false)),
   (v.find ((child i).append (child zero))).map (fun a => a.length.val),
   (v.find ((child i).append (child zero))).map (fun a => a.extent.val),
   word v ((child i).append (flag i1)), word v ((child i).append (memo i1 true)), word v ((child i).append (memo i1 false)),
   (v.find ((child i).append (child i1))).map (fun a => a.length.val),
   (v.find ((child i).append (child i1))).map (fun a => a.extent.val),
   some (bit ((flag i).readLive Value.dflt v).isSome),
   some (bit (((child i).append (flag zero)).readLive Value.dflt v).isSome),
   some (bit (((child i).append (flag i1)).readLive Value.dflt v).isSome)]
private def observations (v : Nodes) : List (Option Nat) :=
  [some v.length.val, some v.extent.val] ++ ids.flatMap (nodeObservations v)
private def nodeExpected (cleared live : Bool) : List (Option Nat) :=
  [some (if cleared then 0 else 1), some 1, some 1, some (if cleared then 0 else 1), some 2,
   some (if cleared then 0 else 1), some 1, some 1, some 0, some 0,
   some 1, some 1, some 1, some 0, some 0,
   some (bit live), some (bit (live && !cleared)), some 0]
private def oldExpected := [some 2, some 3] ++ nodeExpected false true ++ nodeExpected false true ++ nodeExpected false false
private def clearExpected := [some 0, some 3] ++ nodeExpected true false ++ nodeExpected true false ++ nodeExpected false false
private def popExpected := [some 1, some 3] ++ nodeExpected false true ++ nodeExpected true false ++ nodeExpected false false
private def regrowExpected := [some 2, some 3] ++ nodeExpected false true ++ nodeExpected true true ++ nodeExpected false false


private def popped := (recursivePop old).getD old
private def grown := (operationPush popped).getD old
private def final := (execute old).getD old

theorem executions : recursivePop old=some popped ∧ operationPush popped=some grown ∧
 recursivePop grown=some popped ∧ execute old=some popped := by
 refine ⟨rfl,rfl,cycle old popped grown rfl rfl rfl,?_⟩
 exact (outcome old rfl).trans (by rfl)

/-- COMPLETE ordered fixture observations from the existing bool node schema;
all three outer slots, both inner slots, mapping keys, headers/extents/liveness. -/
theorem ordered : [observations old,observations popped,observations grown,observations final] =
 [oldExpected,popExpected,regrowExpected,popExpected] := by rfl

private def branchRoot (width : Nat → Index) (d : Nat) : Nodes :=
 one (node true (tree width d) oldMemo)
private def childPrefix : TypeGraph.Path graph (.array (.node z)) (.array (.node z)) := child zero

/-- Every finite stored recursive depth with independently varying runtime
widths is inhabited, and the ACTUAL cycle equals the first pop on that value. -/
theorem arbitrary_runtime_depth (width : Nat → Index) (positive : ∀ d, 0 < (width d).val) (d : Nat) :
 execute (branchRoot width d)=recursivePop (branchRoot width d) ∧
 (branchRoot width d).find (childPrefix.append (deep d))=some (.prim true) ∧
 ((execute (branchRoot width d)).bind (fun v => v.find (childPrefix.append (deep d))))=some (.prim false) ∧
 ((execute (branchRoot width d)).bind (fun v => v.find (childPrefix.append (deepMemo d))))=some oldMemo := by
 refine ⟨outcome _ rfl,?_,?_,?_⟩
 · change (tree width d).find (deep d)=some (.prim true)
   induction d with
   | zero =>
     simp only [tree,deep,Value.find,TypeGraph.Path.read,Step.get,zero,dif_pos (positive 0),Slot.getD,Option.bind_some,node,Fields.get]
   | succ d ih =>
     simp only [tree,deep,Value.find,TypeGraph.Path.read,Step.get,zero,dif_pos (positive (d+1)),Slot.getD,Option.bind_some,node,Fields.get]
     exact ih
 · rw [outcome _ rfl]
   change (recursiveClear (tree width d)).find (deep d)=some (.prim false)
   rw [recursiveClear_eq_clear]
   induction d with
   | zero =>
     simp only [tree,deep,Value.find,TypeGraph.Path.read,Step.get,Value.clear,zero,dif_pos (positive 0),Slot.clear,Slot.getD,if_pos (positive 0),Option.bind_some,node,Fields.get]
     rfl
   | succ d ih =>
     simp only [tree,deep,Value.find,TypeGraph.Path.read,Step.get,Value.clear,zero,dif_pos (positive (d+1)),Slot.clear,Slot.getD,if_pos (positive (d+1)),Option.bind_some,node,Fields.get]
     exact ih
 · rw [outcome _ rfl]
   change (recursiveClear (tree width d)).find (deepMemo d)=some oldMemo
   rw [recursiveClear_mapping_read]
   induction d with
   | zero =>
     simp only [tree,deepMemo,Value.find,TypeGraph.Path.read,Step.get,zero,dif_pos (positive 0),Slot.getD,Option.bind_some,node,Fields.get]
   | succ d ih =>
     simp only [tree,deepMemo,Value.find,TypeGraph.Path.read,Step.get,zero,dif_pos (positive (d+1)),Slot.getD,Option.bind_some,node,Fields.get]
     exact ih

private def missing : Nodes := .array ⟨1,by decide⟩ i1 (by decide) (fun _ => .absent)
private def missingPop : Nodes := .array ⟨1,by decide⟩ zero (by decide) (fun _ => .absent)
theorem absent_and_empty : execute missing=some missingPop ∧ execute missingPop=none ∧
 missingPop.slots ⟨0,by decide⟩=.absent :=
 by
 have popped : recursivePop missing=some missingPop := by
  simp only [recursivePop,missing,missingPop,Value.length,Value.extent,Value.slots]
  apply congrArg some
  congr 1
  funext i
  simp only [recursiveClearSlot,ite_self]
 exact ⟨(outcome missing rfl).trans popped,(outcome missingPop rfl).trans (by rfl),rfl⟩

private def scalar : Value graph (.array (.prim .bool)) :=
 .array ⟨2,by decide⟩ i1 (by decide) (fun _ => .present (.prim true))
private def scalarPop := (recursivePop scalar).getD scalar
private def scalarFinal := (execute scalar).getD scalar
private def rawPresent {E : TypeGraph.Ty 1} (v : Value graph (.array E)) : Bool :=
 if inside : 0 < v.extent.val then
   match v.slots ⟨0,inside⟩ with
   | .absent => false
   | .present _ => true
 else false
private def scalarPath (i : Index) : TypeGraph.Path graph (.array (.prim .bool)) (.prim .bool) :=
 .cons (.index i) .nil
/-- Scalar reuse resets a PRESENT cleared zero to ABSENT. Full Value identity
is false while every supported retained/defaulted read here remains equal. -/
theorem primitive_negative : scalarFinal ≠ scalarPop ∧
 (rawPresent scalarPop,rawPresent scalarFinal,
  scalarPop.observe (scalarPath zero),scalarFinal.observe (scalarPath zero),
  scalarPop.observe (scalarPath i1),scalarFinal.observe (scalarPath i1),
  scalarPop.length.val,scalarFinal.length.val,scalarPop.extent.val,scalarFinal.extent.val,
  ((scalarPath zero).readLive Value.dflt scalarPop).isSome,
  ((scalarPath zero).readLive Value.dflt scalarFinal).isSome) =
 (true,false,some false,some false,some true,some true,0,0,2,2,false,false) := by
 constructor
 · intro same
   have impossible := congrArg rawPresent same
   change false=true at impossible
   cases impossible
 · rfl

private def maps : Value graph (.array (.mapping .bool (.prim .bool))) :=
 .array ⟨2,by decide⟩ i1 (by decide) (fun _ => .present oldMemo)
private def fixed : Value graph (.array (.fixed (.prim .bool) ⟨2,by decide⟩)) :=
 .array ⟨2,by decide⟩ i1 (by decide) (fun _ => .present (.fixed (fun _ => .present (.prim true))))
private def mapResult := (execute maps).getD maps
private def fixedResult := (execute fixed).getD fixed
private def mp (i : Index) (key : Bool) : TypeGraph.Path graph (.array (.mapping .bool (.prim .bool))) (.prim .bool) :=
 .cons (.index i) (.cons (.key key) .nil)
private def fp (i j : Index) : TypeGraph.Path graph (.array (.fixed (.prim .bool) ⟨2,by decide⟩)) (.prim .bool) :=
 .cons (.index i) (.cons (.fixed j) .nil)
theorem aggregate_families : execute maps=recursivePop maps ∧ execute fixed=recursivePop fixed ∧
 (mapResult.length.val,mapResult.extent.val,fixedResult.length.val,fixedResult.extent.val,
  mapResult.observe (mp zero true),mapResult.observe (mp zero false),mapResult.observe (mp i1 true),mapResult.observe (mp i1 false),
  fixedResult.observe (fp zero zero),fixedResult.observe (fp zero i1),fixedResult.observe (fp i1 zero),fixedResult.observe (fp i1 i1),
  rawPresent mapResult,rawPresent fixedResult,mapResult.observe (mp i2 true),fixedResult.observe (fp i2 zero),
  ((mp zero true).readLive Value.dflt mapResult).isSome,((fp zero zero).readLive Value.dflt fixedResult).isSome) =
 (0,2,0,2,some true,some true,some true,some true,some false,some false,some true,some true,true,true,none,none,false,false) :=
 ⟨outcome maps rfl,outcome fixed rfl,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.GraphRetainedCycle.Controls.executions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms executions
/-- info: 'Solidity.Backend.StorageOps.GraphRetainedCycle.Controls.ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.GraphRetainedCycle.Controls.arbitrary_runtime_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms arbitrary_runtime_depth
/-- info: 'Solidity.Backend.StorageOps.GraphRetainedCycle.Controls.absent_and_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms absent_and_empty
/-- info: 'Solidity.Backend.StorageOps.GraphRetainedCycle.Controls.primitive_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms primitive_negative
/-- info: 'Solidity.Backend.StorageOps.GraphRetainedCycle.Controls.aggregate_families' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms aggregate_families
end Solidity.Backend.StorageOps.GraphRetainedCycle.Controls
