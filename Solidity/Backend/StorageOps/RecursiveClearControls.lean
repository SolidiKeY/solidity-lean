import Solidity.Backend.StorageOps.RecursiveLifecycleFacts
import Solidity.Backend.StorageOps.RecursiveProgress

/-! Ordered operation observations and every-depth/runtime-width clear controls.
Only intrinsic graph behavior is tested, not numeric storage or world rollback. -/
namespace Solidity.Backend.StorageOps.RecursiveClearControls
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

/-- Positive widths only inhabit this selected retained observation; clear
itself accepts every constructor, including every empty array. -/
theorem varying_clear_depth (width : Nat → Index) (positive : ∀ d, 0 < (width d).val) (d : Nat) :
    (tree width d).find (deep d) = some (.prim true) ∧
    (recursiveClear (tree width d)).find (deep d) = some (.prim false) := by
  rw [recursiveClear_eq_clear]
  induction d with
  | zero =>
    simp only [tree, deep, Value.find, TypeGraph.Path.read, TypeGraph.Step.get, Value.clear,
      zero, dif_pos (positive 0), Slot.clear, Slot.getD, if_pos (positive 0), Option.bind_some, node, Fields.get]
    exact ⟨True.intro, rfl⟩
  | succ d ih =>
    simp only [tree, deep, Value.find, TypeGraph.Path.read, TypeGraph.Step.get, Value.clear,
      zero, dif_pos (positive (d+1)), Slot.clear, Slot.getD, if_pos (positive (d+1)), Option.bind_some, node, Fields.get]
    exact ih

theorem mapping_all_depth (width : Nat → Index) (positive : ∀ d, 0 < (width d).val) (d : Nat) :
    (recursiveClear (tree width d)).find (deepMemo d) = some oldMemo := by
  rw [recursiveClear_mapping_read]
  induction d with
  | zero =>
    simp only [tree, deepMemo, Value.find, TypeGraph.Path.read, TypeGraph.Step.get,
      zero, dif_pos (positive 0), Slot.getD, Option.bind_some, node, Fields.get]
  | succ d ih =>
    simp only [tree, deepMemo, Value.find, TypeGraph.Path.read, TypeGraph.Step.get,
      zero, dif_pos (positive (d+1)), Slot.getD, Option.bind_some, node, Fields.get]
    exact ih

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

/-- Positive before/after values are fully observed, including older shadows. -/
theorem ordered_clear : [observations old, observations (recursiveClear old)] = [oldExpected, clearExpected] := rfl

private def cycle : Option (List (List (Option Nat))) := do
  let shrunk ← popAt old .nil
  let regrown ← pushAt shrunk .nil
  let deleted ← deleteAt regrown .nil
  pure [observations old, observations shrunk, observations regrown, observations deleted]

/-- Complete ordered pop/regrow/delete sequence distinguishes the removed
slot, live versus retained aliases, nested tails and both mapping keys. -/
theorem ordered_cycle : cycle = some [oldExpected, popExpected, regrowExpected, clearExpected] := rfl

private def pre : TypeGraph.Path graph (.mapping .bool (.array (.node z))) (.array (.node z)) := .cons (.key true) .nil
private def outside : TypeGraph.Path graph (.mapping .bool (.array (.node z))) (.array (.node z)) := .cons (.key false) .nil
private def root : Value graph (.mapping .bool (.array (.node z))) := .mapping (fun _ => .present old)

theorem delete_nonempty_prefix : (deleteAt root pre).map
    (fun result => ((result.find pre).map observations, (result.find outside).map observations)) =
    some (some clearExpected, some oldExpected) := rfl

theorem pop_nonempty_prefix : (popAt root pre).map
    (fun result => ((result.find pre).map observations, (result.find outside).map observations)) =
    some (some popExpected, some oldExpected) := rfl

/-- Deleting an empty array must retain EVERY old shadow verbatim. -/
theorem empty_retained_delete : (deleteAt retained .nil).map observations =
    some ([some 0, some 3] ++ nodeExpected false false ++ nodeExpected false false ++ nodeExpected false false) := rfl

theorem empty_pop_fails : popAt retained .nil = none := rfl

theorem prefix_observations :
    (clearArrayPrefix slots 1 ⟨0, by decide⟩).getD (Value.dflt _) = recursiveClear (node true inner oldMemo) ∧
    clearArrayPrefix slots 1 ⟨1, by decide⟩ = slots ⟨1, by decide⟩ ∧
    clearArrayPrefix slots 2 ⟨2, by decide⟩ = slots ⟨2, by decide⟩ := by
  constructor
  · rfl
  · constructor <;> rfl

private def wrongExtentClear : Nodes := .array ⟨3, by decide⟩ zero (by decide) (clearArrayPrefix slots 3)
/-- Wrong extent clearing destroys the observable old shadow. -/
theorem wrong_extent_negative : observations wrongExtentClear =
    [some 0, some 3] ++ nodeExpected true false ++ nodeExpected true false ++ nodeExpected true false ∧
    (recursiveClear old).observe (flag i2) = some true ∧ wrongExtentClear.observe (flag i2) = some false := by
  constructor
  · rfl
  · constructor <;> rfl

private def wrongPopSlot : Nodes := .array ⟨3, by decide⟩ i1 (by decide)
  (fun i => if i.val = 0 then recursiveClearSlot (slots i) else slots i)
/-- Clearing the first slot instead of the last gives a different FULL view. -/
theorem wrong_pop_negative : observations wrongPopSlot =
    [some 1, some 3] ++ nodeExpected true true ++ nodeExpected false false ++ nodeExpected false false ∧
    (recursivePop old).map observations = some popExpected := by constructor <;> rfl

private def erased : Nodes := .array ⟨3, by decide⟩ zero (by decide)
  (fun _ => .present (node false empty (Value.dflt _)))
theorem mapping_erasure_negative : (recursiveClear old).observe (memo zero true) = some true ∧
    erased.observe (memo zero true) = some false := by constructor <;> rfl

theorem absent_present : recursiveClearSlot (Slot.absent : Slot graph (.node z)) = .absent ∧
    recursiveClearSlot (.present (node true inner oldMemo)) = .present (recursiveClear (node true inner oldMemo)) := by
  constructor <;> rfl

theorem fixed_node_array : (recursiveClear (Value.fixed (m := ⟨1, by decide⟩) (fun _ => .present old))).find
    (.cons (.fixed zero) .nil) = some (recursiveClear old) := rfl

theorem fixed_ordered : ((recursiveClear (Value.fixed (m := ⟨1, by decide⟩) (fun _ => .present old))).find
    (.cons (.fixed zero) .nil)).map observations = some clearExpected := rfl

private def i3 : Index := ⟨3, by decide⟩
theorem malformed_delete_pop : deleteAt old (child i3) = none ∧ popAt old (child i3) = none := by
  constructor <;> rfl

theorem array_absent_present :
    (recursiveClear (Value.array ⟨2, by decide⟩ i2 (by decide)
      (fun i => if i.val = 0 then .absent else .present (node true inner oldMemo)))).slots
      ⟨0, by decide⟩ = .absent ∧
    (recursiveClear (Value.array ⟨2, by decide⟩ i2 (by decide)
      (fun i => if i.val = 0 then .absent else .present (node true inner oldMemo)))).slots
      ⟨1, by decide⟩ = .present (recursiveClear (node true inner oldMemo)) := by
  constructor <;> rfl

/-- info: 'Solidity.Backend.StorageOps.RecursiveClearControls.varying_clear_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms varying_clear_depth
/-- info: 'Solidity.Backend.StorageOps.RecursiveClearControls.mapping_all_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mapping_all_depth
/-- info: 'Solidity.Backend.StorageOps.RecursiveClearControls.ordered_cycle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ordered_cycle
end Solidity.Backend.StorageOps.RecursiveClearControls
