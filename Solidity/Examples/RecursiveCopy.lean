import Solidity.Examples.RecursiveStorage
import Solidity.Semantics.RecursiveStorage.Admission
import Solidity.Semantics.RecursiveStorage.Legacy
import Solidity.Semantics.RecursiveStorage.Observations

/-! Copy and ordinary-storage compatibility regressions. These are kernel
statements for the primary to check; they do not assert that solc_import or
Stmt/State has migrated to graph-indexed types. -/

namespace Solidity.TypeGraph.Examples.Copy

private def z : Fin 1 := ⟨0, by decide⟩
private def i0 : Index := ⟨0, by decide⟩
private def i1 : Index := ⟨1, by decide⟩
private def uint (n : Nat) : PrimTy.uint.Denote := ⟨(n % 2 ^ 256 : Nat), by
  simp only [PrimTy.inRange, decide_eq_true_eq]
  have h : n % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt n (by decide)
  omega⟩

private abbrev Node := Value arraySchema (.node z)
private abbrev Nodes := Value arraySchema (.array (.node z))
private def emptyChildren : Nodes := Value.dflt _
private def node (value : Nat) (children : Nodes := emptyChildren) : Node :=
  .node (fun p => match p with
    | .here => .prim (uint value)
    | .there .here => children
    | .there (.there q) => nomatch q)
private def one (v : Node) : Nodes :=
  .array ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide) (fun _ => .present v)
private def two (a b : Node) : Nodes :=
  .array ⟨2, by decide⟩ ⟨2, by decide⟩ (by decide)
    (fun i => if i.val = 0 then .present a else .present b)
private def shadow (v : Node) : Nodes :=
  .array ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide) (fun _ => .present v)
private def scalar : Path arraySchema (.node z) (.prim .uint) := .cons (.field .here) .nil
private def children : Path arraySchema (.node z) (.array (.node z)) :=
  .cons (.field (.there .here)) .nil
private def child (i : Index) : Path arraySchema (.node z) (.node z) :=
  .cons (.field (.there .here)) (.cons (.index i) .nil)
private def atScalar (i : Index) : Path arraySchema (.node z) (.prim .uint) :=
  (child i).append scalar

private def source : Node := node 5 (one (node 7 (one (node 9))))
private def destination : Node := node 11 (two (node 13) (node 15 (one (node 19))))

/-- `dst = src` copies a populated recursive storage tree. -/
example : (destination.overlay source).observe scalar = some (uint 5) := rfl
example : (destination.overlay source).observe (atScalar i0) = some (uint 7) := rfl
example : (destination.overlay source).observe ((child i0).append (atScalar i0)) =
    some (uint 9) := rfl
/-- A retained alias to the shortened live destination sees cleared contents. -/
example : (destination.overlay source).observe (atScalar i1) = some (uint 0) := rfl
example : ((destination.overlay source).find ((child i1).append children)).map Value.length =
    some ⟨0, by decide⟩ := rfl
example : ((atScalar i1).readLive Value.dflt (destination.overlay source)) = none := rfl
/-- Copy retains destination extent; it is not raw equality with the source. -/
example : ((destination.overlay source).find children).map Value.extent =
    some ⟨2, by decide⟩ := rfl
example : source.observe children ≠ (destination.overlay source).observe children := by
  intro equal
  have impossible :=
    congrArg (fun observed : Option (Index × Extent) => observed.map (fun pair => pair.2.val)) equal
  change (some 1 : Option Nat) = some 2 at impossible
  cases impossible

/-- Source-only shadows are not transferred to a new destination. -/
example : (emptyChildren.overlay (shadow (node 17))).push.bind
    (fun v => v.find (.cons (.index i0) scalar)) = some (.prim (uint 0)) := rfl
/-- An older destination shadow survives copy and becomes live again on push. -/
example : ((shadow (node 13)).overlay emptyChildren).push.bind
    (fun v => v.find (.cons (.index i0) scalar)) = some (.prim (uint 13)) := rfl
/-- A missing source live child copies the default, clearing the old child. -/
example : ((one (node 21)).overlay
    (.array ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide) (fun _ => .absent))).find
      (.cons (.index i0) scalar) = some (.prim (uint 0)) := rfl
/-- Copying from a descendant captures it before the ancestor is replaced. -/
example : (source.copyAt .nil (child i0)).map (fun v => v.observe scalar) =
    some (some (uint 7)) := rfl
example : (source.copyAt .nil (child i0)).map (fun v => v.observe (atScalar i0)) =
    some (some (uint 9)) := rfl

/-- Mapping-freedom follows recursive edges, not the inline layout rank. -/
private def treePermit : CopyPermit arraySchema (.node z) :=
  CopyPermit.checked (fun _ => true) (by decide)
example : (CopyPermit.check arraySchema (.node z) (fun _ => true)).isSome = true := by decide
example : (CopyPermit.check mappingSchema (.node z) (fun _ => true)).isSome = false := by decide
example : (CopyPermit.check arraySchema (.node z) (fun _ => false)).isSome = false := by decide
example : source.assignAt .nil (child i0) treePermit = source.copyAt .nil (child i0) := rfl

private def mapScalar : Path mappingSchema (.node z) (.prim .uint) := .cons (.field .here) .nil
private def mapNext : Path mappingSchema (.node z) (.prim .uint) :=
  .cons (.field (.there .here)) (.cons (.key (uint 1)) mapScalar)
private def mapped : Value mappingSchema (.node z) :=
  match (Value.dflt (.node z) : Value mappingSchema _).save mapNext (.prim (uint 23)) with
  | some v => v
  | none => Value.dflt _
/-- The internal algebra preserves a mapping even for an implicit source
child. Such whole-struct assignments are rejected by source copy admission. -/
example : (mapped.overlay (Value.dflt _)).observe mapNext = some (uint 23) := rfl

open Legacy
private def scalarLayout : Layout arraySchema Solidity.Ty.uint (.prim .uint) := .prim .uint
private def boolMapLayout : Layout arraySchema
    (.ref (.mapping .bool Solidity.Ty.uint)) (.mapping .bool (.prim .uint)) :=
  .mapping .bool scalarLayout
private def ordinaryMap : SVal (.ref (.mapping .bool Solidity.Ty.uint)) :=
  .map (.cons true (.prim (uint 7)) .nil) (.prim (uint 9))
/-- Written and unwritten ordinary mapping keys retain their actual values. -/
example : (boolMapLayout.encode ordinaryMap).observe (.cons (.key true) .nil) =
    some (uint 7) := by
  let key : KeyPath boolMapLayout scalarLayout := .key .bool true .nil
  change (boolMapLayout.encode ordinaryMap).observe key.graph = _
  rw [key.observe_encode]
  simp only [key, KeyPath.legacy, ordinaryMap, SVal.find_key,
    SMap.toList_cons, SMap.toList_nil, Semantics.lookupBy]
  rfl
example : (boolMapLayout.encode ordinaryMap).observe (.cons (.key false) .nil) =
    some (uint 9) := by
  let key : KeyPath boolMapLayout scalarLayout := .key .bool false .nil
  change (boolMapLayout.encode ordinaryMap).observe key.graph = _
  rw [key.observe_encode]
  simp only [key, KeyPath.legacy, ordinaryMap, SVal.find_key,
    SMap.toList_cons, SMap.toList_nil, Semantics.lookupBy]
  rfl
example : (boolMapLayout.encode ordinaryMap).find (.cons (.key false) .nil) =
    (ordinaryMap.find (.key false .nil)).map scalarLayout.encode :=
  scalarLayout.read_key .bool _ _ false

private def nestedLayout : Layout arraySchema
    (.ref (.mapping .bool (.ref (.mapping .bool Solidity.Ty.uint))))
    (.mapping .bool (.mapping .bool (.prim .uint))) := .mapping .bool boolMapLayout
private def nestedOrdinary : SVal
    (.ref (.mapping .bool (.ref (.mapping .bool Solidity.Ty.uint)))) :=
  .map (.cons true ordinaryMap .nil) (.map .nil (.prim (uint 61)))
private def outerFallback : KeyPath nestedLayout scalarLayout :=
  .key .bool false (.key .bool true .nil)
private def innerFallback : KeyPath nestedLayout scalarLayout :=
  .key .bool true (.key .bool false .nil)
/-- Noncanonical fallbacks survive both branches of the inductive bridge. -/
example : (nestedLayout.encode nestedOrdinary).find outerFallback.graph =
    (nestedOrdinary.find outerFallback.legacy).map scalarLayout.encode :=
  outerFallback.find_encode nestedOrdinary
example : (nestedLayout.encode nestedOrdinary).observe outerFallback.graph =
    some (uint 61) := by
  rw [outerFallback.observe_encode]
  simp only [outerFallback, KeyPath.legacy, nestedOrdinary, ordinaryMap,
    SVal.find_key, SMap.toList_cons, SMap.toList_nil, Semantics.lookupBy]
  rfl
example : (nestedLayout.encode nestedOrdinary).find innerFallback.graph =
    (nestedOrdinary.find innerFallback.legacy).map scalarLayout.encode :=
  innerFallback.find_encode nestedOrdinary
example : (nestedLayout.encode nestedOrdinary).observe innerFallback.graph =
    some (uint 9) := by
  rw [innerFallback.observe_encode]
  simp only [innerFallback, KeyPath.legacy, nestedOrdinary, ordinaryMap,
    SVal.find_key, SMap.toList_cons, SMap.toList_nil, Semantics.lookupBy, if_true, if_false, Option.some_bind, scalarLayout,
    Layout.encode, Value.head, SVal.find, SVal.view]
  rfl

/-- Ordinary interpreter values can be assigned into a recursive root. -/
example : (writeLegacy source scalar scalarLayout (.prim (uint 31))).map
    (fun v => v.observe scalar) = some (some (uint 31)) := rfl
example : (writeLegacy source ((child i0).append scalar) scalarLayout (.prim (uint 37))).map
    (fun v => v.observe ((child i0).append scalar)) = some (some (uint 37)) := rfl
example : (assignLegacy source scalar
    (CopyPermit.checked (fun _ => false) (by decide)) scalarLayout (.prim (uint 31))).map
      (fun v => v.observe scalar) = some (some (uint 31)) := rfl
/-- Existing retained/live array reads agree on a concrete legacy shadow. -/
private def ordinaryArray : SVal (.ref (.array Solidity.Ty.uint)) :=
  .array (.cons (.prim (uint 3)) .nil) (.cons (.prim (uint 41)) .nil) (by decide)
private def arrayLayout : Layout arraySchema (.ref (.array Solidity.Ty.uint))
    (.array (.prim .uint)) := .array scalarLayout
example : (arrayLayout.encode ordinaryArray).find (.cons (.index i1) .nil) =
    (ordinaryArray.find (.at (uint 1) .nil)).map scalarLayout.encode := by
  simp only [arrayLayout, ordinaryArray, Layout.encode, SVal.view_array,
    SVec.toList_cons, SVec.toList_nil, SList.toList_cons, SList.toList_nil,
    SVal.find_at]
  rfl
example : (.cons (.index i1) .nil : Path arraySchema (.array (.prim .uint)) (.prim .uint)).readLive
    Value.dflt (arrayLayout.encode ordinaryArray) = none := rfl
private def size2 : FixedSize := ⟨2, by decide⟩
private def ordinaryFixed : SVal (.ref (.fixed Solidity.Ty.uint 2)) :=
  .fixed (.cons (.prim (uint 43)) (.cons (.prim (uint 47)) .nil))
example : ((Layout.fixed scalarLayout size2).encode ordinaryFixed).observe
    (.cons (.fixed i1) .nil) = some (uint 47) := by
  simp only [ordinaryFixed, Layout.encode, SVal.view,
    SVec.toList_cons, SVec.toList_nil]
  rfl

private def tokenSchema : Schema 1 where
  origin := "legacy-copy-example"
  declId := fun _ => 1
  declId_injective := by intro i j _; apply Fin.ext; omega
  name := fun _ => "Token"
  fields := fun _ => [("value", .prim .uint)]
  rank := fun _ => 1
  nonempty := fun _ => rfl
  distinct := fun _ => rfl
  guarded := by
    intro i f h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst f
    exact Nat.zero_lt_succ 0
private def tokenLayout : Layout tokenSchema (.ref (.struct "Token")) (.node z) :=
  .node (.cons (.prim .uint) .nil)
/-- Ordered struct-field compatibility uses the ordinary SFields family. -/
example : (tokenLayout.encode (.struct (.cons (.prim (uint 53)) .nil))).observe
    (.cons (.field .here) .nil) = some (uint 53) := rfl

#print axioms CopyPermit.no_mapping_path
#print axioms Value.overlay_dflt
#print axioms Value.find_copyAt
#print axioms Value.overlay_tail
#print axioms Legacy.KeyPath.find_encode
#print axioms Value.ObsEq.at

end Solidity.TypeGraph.Examples.Copy
