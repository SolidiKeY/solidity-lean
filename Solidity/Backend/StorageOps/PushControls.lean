import Solidity.Backend.StorageOps.PushPaths
import Solidity.Backend.StorageOps.RecursiveClearControls

/-! Independent push observations. Every bounded fixture field/header, both
mapping keys, retained slot and live availability is observed in fixed order. -/
namespace Solidity.Backend.StorageOps.PushControls
open TypeGraph
private def z : Fin 1 := ⟨0, by decide⟩
private def fs : List (Name × TypeGraph.Ty 1) :=
  [("flag", .prim .bool), ("children", .array (.node z)),
   ("memo", .mapping .bool (.prim .bool))]
private def graph : Schema 1 where
  origin := "v10-independent-push-controls"
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

private def i1 : Index := ⟨1, by decide⟩
private def i2 : Index := ⟨2, by decide⟩
private def flag (i : Index) : TypeGraph.Path graph (.array (.node z)) (.prim .bool) :=
  .cons (.index i) (.cons (.field .here) .nil)
private def memo (i : Index) (key : Bool) : TypeGraph.Path graph (.array (.node z)) (.prim .bool) :=
  .cons (.index i) (.cons (.field (.there (.there .here))) (.cons (.key key) .nil))
private def child (i : Index) : TypeGraph.Path graph (.array (.node z)) (.array (.node z)) :=
  .cons (.index i) (.cons (.field (.there .here)) .nil)
private def bit (b : Bool) : Nat := if b then 1 else 0
private def item (v : Nodes) (i : Index) : List (Option Nat) :=
  [(v.observe (flag i)).map bit, (v.observe (memo i true)).map bit, (v.observe (memo i false)).map bit,
   (v.find (child i)).map (fun x => x.length.val), (v.find (child i)).map (fun x => x.extent.val),
   some (bit ((flag i).readLive Value.dflt v).isSome)]
private def observations (v : Nodes) : List (Option Nat) :=
  [some v.length.val, some v.extent.val] ++ item v zero ++ item v i1
private def retained : Nodes := .array ⟨2, by decide⟩ zero (by decide)
  (fun _ => .present (node true empty oldMemo))
private def before := [some 0, some 2, some 1, some 1, some 1, some 0, some 0, some 0,
  some 1, some 1, some 1, some 0, some 0, some 0]
private def reused := [some 1, some 2, some 1, some 1, some 1, some 0, some 0, some 1,
  some 1, some 1, some 1, some 0, some 0, some 0]
private def fresh := [some 1, some 1, some 0, some 0, some 0, some 0, some 0, some 1,
  none, none, none, none, none, some 0]

/-- Aggregate reuse keeps retained scalar AND both mapping keys; fresh
allocation reads published defaults and leaves the second index unavailable. -/
theorem fresh_reuse_ordered :
    [some (observations retained), (operationPush retained).map observations,
      (operationPush empty).map observations] = [some before, some reused, some fresh] := rfl

private def pre : TypeGraph.Path graph (.mapping .bool (.array (.node z))) (.array (.node z)) := .cons (.key true) .nil
private def other : TypeGraph.Path graph (.mapping .bool (.array (.node z))) (.array (.node z)) := .cons (.key false) .nil
private def root : Value graph (.mapping .bool (.array (.node z))) := .mapping (fun _ => .present retained)

theorem nested_push_outside : (pushAt root pre).map
    (fun result => ((result.find pre).map observations, (result.find other).map observations)) =
    some (some reused, some before) := rfl

private def scalars : Value graph (.array (.prim .bool)) := .array ⟨2, by decide⟩ zero (by decide)
  (fun _ => .present (.prim true))
private def scalarPath (i : Index) : TypeGraph.Path graph (.array (.prim .bool)) (.prim .bool) := .cons (.index i) .nil
private def scalarObservations (v : Value graph (.array (.prim .bool))) : List (Option Nat) :=
  [some v.length.val, some v.extent.val, (v.observe (scalarPath zero)).map bit, (v.observe (scalarPath i1)).map bit,
   some (bit ((scalarPath zero).readLive Value.dflt v).isSome), some (bit ((scalarPath i1).readLive Value.dflt v).isSome)]

/-- Primitive reuse resets only the newly live scalar; an older shadow stays. -/
theorem scalar_reset_ordered : [some (scalarObservations scalars), (operationPush scalars).map scalarObservations] =
    [some [some 0, some 2, some 1, some 1, some 0, some 0],
     some [some 1, some 2, some 0, some 1, some 1, some 0]] := rfl

private def wrongReset : Nodes := .array ⟨2, by decide⟩ i1 (by decide)
  (fun i => if i.val = 0 then .present (Value.dflt _) else .present (node true empty oldMemo))
private def wrongExpected := [some 1, some 2, some 0, some 0, some 0, some 0, some 0, some 1,
  some 1, some 1, some 1, some 0, some 0, some 0]
/-- Incorrectly resetting an aggregate at the SAME extent/header loses payload
and mappings. Compare actual wrong and correct FULL operation observations. -/
theorem wrong_aggregate_reset : observations wrongReset = wrongExpected ∧
    (operationPush retained).map observations = some reused ∧ wrongExpected ≠ reused := by
  constructor
  · rfl
  · constructor
    · rfl
    · decide

private def near : Nodes := .array ⟨2 ^ 256 - 2, by decide⟩ ⟨2 ^ 256 - 2, by decide⟩ (by decide) (fun _ => .absent)
private def full : Nodes := .array ⟨2 ^ 256 - 1, by decide⟩ ⟨2 ^ 256 - 1, by decide⟩ (by decide) (fun _ => .absent)
/-- Existing graph capacity is not a new admitted-source limit or Panic code. -/
theorem capacity_boundary :
    (operationPush near).map (fun v => (v.length.val, v.extent.val)) = some (2 ^ 256 - 1, 2 ^ 256 - 1) ∧
    operationPush full = none := by constructor <;> rfl

private def bad : TypeGraph.Path graph (.array (.node z)) (.array (.node z)) := child i2
theorem unavailable_path : pushAt retained bad = none := rfl

/-- Late failure is Option.none; no externally visible world rollback asserted. -/
theorem pop_then_empty_failure : ((popAt (one (node true empty oldMemo)) .nil).bind
    (fun result => popAt result .nil)) = none := rfl

/-- info: 'Solidity.Backend.StorageOps.PushControls.fresh_reuse_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fresh_reuse_ordered
/-- info: 'Solidity.Backend.StorageOps.PushControls.scalar_reset_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scalar_reset_ordered
/-- info: 'Solidity.Backend.StorageOps.PushControls.capacity_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms capacity_boundary
end Solidity.Backend.StorageOps.PushControls
