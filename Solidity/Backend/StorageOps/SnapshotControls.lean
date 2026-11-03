import Solidity.Backend.StorageOps.SnapshotCommutation

/-! Complete ordered views of real successive-root snapshot copies. -/
namespace Solidity.Backend.StorageOps.SnapshotControls
open TypeGraph
private def z : Fin 1 := ⟨0, by decide⟩
private def fields : List (Name × TypeGraph.Ty 1) :=
  [("flag", .prim .bool), ("children", .array (.node z))]
private def graph : Schema 1 where
  origin := "v10-snapshot-commutation-controls"
  declId := fun _ => 0
  declId_injective := by intro i j _; apply Fin.ext; omega
  name := fun _ => "Node"
  fields := fun _ => fields
  rank := fun _ => 1
  nonempty := fun _ => rfl
  distinct := fun _ => rfl
  guarded := by
    intro i f hf
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> exact Nat.zero_lt_succ 0


private def k0 : PrimTy.uint.Denote := ⟨0, by decide⟩
private def k1 : PrimTy.uint.Denote := ⟨1, by decide⟩
private def k2 : PrimTy.uint.Denote := ⟨2, by decide⟩
private def zero : Index := ⟨0, by decide⟩
private def one : Index := ⟨1, by decide⟩
private def two : Extent := ⟨2, by decide⟩
private abbrev Bits := Value graph (.array (.prim .bool))
private abbrev Root := Value graph (.mapping .uint (.array (.prim .bool)))
private def old : Bits := .array two one (by decide) (fun _ => .present (.prim true))
private def source : Bits := .array ⟨1, by decide⟩ one (by decide) (fun _ => .present (.prim false))
private def slots (k : PrimTy.uint.Denote) : Slot graph (.array (.prim .bool)) := .present (if k = k2 then source else old)
private def root : Root := .mapping slots
private def path (k : PrimTy.uint.Denote) : TypeGraph.Path graph (.mapping .uint (.array (.prim .bool))) (.array (.prim .bool)) := .cons (.key k) .nil
private def bitpath (i : Index) : TypeGraph.Path graph (.array (.prim .bool)) (.prim .bool) := .cons (.index i) .nil
private def bit (b : Bool) : Nat := if b then 1 else 0
private def view (v : Bits) : List (Option Nat) :=
  [some v.length.val, some v.extent.val, (v.observe (bitpath zero)).map bit,
   (v.observe (bitpath one)).map bit,
   some (bit ((bitpath zero).readLive Value.dflt v).isSome),
   some (bit ((bitpath one).readLive Value.dflt v).isSome)]
private def observations (v : Root) : List (Option (List (Option Nat))) :=
  [((v.find (path k0)).map view), ((v.find (path k1)).map view), ((v.find (path k2)).map view)]
private def oldView := [some 1, some 2, some 1, some 1, some 1, some 0]
private def copiedView := [some 1, some 2, some 0, some 1, some 1, some 0]
private def sourceView := [some 1, some 1, some 0, none, some 1, some 0]
private def left (v : Root) := recursiveCopyAt v (path k0) (path k2)
private def right (v : Root) := recursiveCopyAt v (path k1) (path k2)

/-- Shared source read/read is safe, both targets CHANGE, retained shadows and
source header/data/unavailable/live outcomes are all pinned in order. -/
theorem shared_source_ordered :
    [some (observations root), ((left root).bind right).map observations,
      ((right root).bind left).map observations] =
    [some [some oldView, some oldView, some sourceView],
     some [some copiedView, some copiedView, some sourceView],
     some [some copiedView, some copiedView, some sourceView]] := rfl

theorem shared_source_certificate : (left root).bind right = (right root).bind left :=
  actual_mapping_copies_commute slots k0 k2 k1 k2 (by decide) (by decide) (by decide) .nil .nil .nil .nil

/-- A malformed source suffix fails in BOTH orders, even if the other copy
succeeds first. This is Option failure, not a world rollback theorem. -/
private def malformed (v : Root) : Option Root := recursiveCopyAt v
  (.cons (.key k0) (bitpath ⟨3, by decide⟩)) (.cons (.key k2) (bitpath ⟨3, by decide⟩))
theorem source_failure_orders : (malformed root).bind right = none ∧ (right root).bind malformed = none := by
  constructor <;> rfl

private def badDestination (v : Root) : Option Root := recursiveCopyAt v
  (.cons (.key k0) (bitpath ⟨3, by decide⟩)) (.cons (.key k2) (bitpath zero))
theorem destination_failure_orders : (badDestination root).bind right = none ∧ (right root).bind badDestination = none := by
  constructor <;> rfl

/-- Cross-dependency is excluded for a reason: the second operation captures a
new value if the first operation overwrites its source. FULL views differ. -/
private def dependent (v : Root) := recursiveCopyAt v (path k1) (path k0)
theorem cross_dependency_negative :
    ((left root).bind dependent).map observations = some [some copiedView, some copiedView, some sourceView] ∧
    ((dependent root).bind left).map observations = some [some copiedView, some oldView, some sourceView] := by
  constructor <;> rfl

private def node (flag : Bool) (children : Value graph (.array (.node z))) : Value graph (.node z) :=
  .node (fun p => match p with
    | .here => .prim flag
    | .there .here => children
    | .there (.there q) => nomatch q)
private def tree (flag : Bool) : Nat → Value graph (.array (.node z))
  | 0 => .array ⟨1, by decide⟩ one (by decide) (fun _ => .present (node flag (Value.dflt _)))
  | d+1 => .array ⟨1, by decide⟩ one (by decide) (fun _ => .present (node flag (tree flag d)))
private def deep : Nat → TypeGraph.Path graph (.array (.node z)) (.prim .bool)
  | 0 => .cons (.index zero) (.cons (.field .here) .nil)
  | d+1 => .cons (.index zero) (.cons (.field (.there .here)) (deep d))
private def recursiveSlots (d : Nat) (k : PrimTy.uint.Denote) : Slot graph (.array (.node z)) :=
  .present (tree (if k = k2 then false else true) d)

theorem all_depth_reads (d : Nat) : (tree true d).find (deep d) = some (.prim true) ∧
    (tree false d).find (deep d) = some (.prim false) := by
  induction d with
  | zero => constructor <;> rfl
  | succ d ih => exact ih

/-- Actual arbitrary-depth captures, without successful-read hypotheses. The
separate inhabited read controls show this class is not vacuous. -/
theorem all_depth_commutes (d : Nat) :
    (recursiveCopyAt (.mapping (recursiveSlots d)) (.cons (.key k0) (deep d)) (.cons (.key k2) (deep d))).bind
      (fun v => recursiveCopyAt v (.cons (.key k1) (deep d)) (.cons (.key k2) (deep d))) =
    (recursiveCopyAt (.mapping (recursiveSlots d)) (.cons (.key k1) (deep d)) (.cons (.key k2) (deep d))).bind
      (fun v => recursiveCopyAt v (.cons (.key k0) (deep d)) (.cons (.key k2) (deep d))) :=
  actual_mapping_copies_commute (recursiveSlots d) k0 k2 k1 k2 (by decide) (by decide) (by decide) (deep d) (deep d) (deep d) (deep d)

/-- Every finite-depth actual copy succeeds and changes the selected payload. -/
theorem all_depth_actual_success (d : Nat) : ∃ result,
    recursiveCopyAt (.mapping (recursiveSlots d)) (.cons (.key k0) (deep d)) (.cons (.key k2) (deep d)) = some result ∧
    result.find (.cons (.key k0) (deep d)) = some (.prim false) := by
  obtain ⟨value, saved⟩ := prefix_save_exists (deep d) (tree true d) (.prim true) (.prim false) (all_depth_reads d).1
  have effect : copyEffect (tree false d) (deep d) (deep d) (tree true d) = some value := by
    simp only [copyEffect, (all_depth_reads d).1, (all_depth_reads d).2, Option.bind_eq_bind, Option.bind_some]
    exact saved
  have op : copySibling (recursiveSlots d) k0 k2 (deep d) (deep d) =
      some (Slots.write (recursiveSlots d) k0 value) := by
    change (copyEffect (tree false d) (deep d) (deep d) (tree true d)).map _ = _
    rw [effect]
    rfl
  have copied : recursiveCopyAt (.mapping (recursiveSlots d)) (.cons (.key k0) (deep d)) (.cons (.key k2) (deep d)) =
      some (.mapping (Slots.write (recursiveSlots d) k0 value)) := by
    rw [copySibling_eq_actual, op]
    rfl
  refine ⟨_, copied, ?_⟩
  exact recursiveCopyAt_readback (.mapping (recursiveSlots d)) _ (.cons (.key k0) (deep d)) (.cons (.key k2) (deep d))
    (.prim true) (.prim false) (all_depth_reads d).1 (all_depth_reads d).2 copied

private def outer : Value graph (.mapping .bool (.mapping .uint (.array (.prim .bool)))) :=
  .mapping (fun _ => .present root)
private def pre : TypeGraph.Path graph (.mapping .bool (.mapping .uint (.array (.prim .bool))))
    (.mapping .uint (.array (.prim .bool))) := .cons (.key true) .nil
private def prefixLeft (v : Value graph (.mapping .bool (.mapping .uint (.array (.prim .bool))))) :=
  recursiveCopyAt v (pre.append (path k0)) (pre.append (path k2))
private def prefixRight (v : Value graph (.mapping .bool (.mapping .uint (.array (.prim .bool))))) :=
  recursiveCopyAt v (pre.append (path k1)) (pre.append (path k2))
theorem nonempty_prefix_ordered : ((prefixLeft outer).bind prefixRight).map
    (fun result => ((result.find pre).map observations,
      (result.find (.cons (.key false) .nil)).map observations)) =
    some (some [some copiedView, some copiedView, some sourceView],
      some [some oldView, some oldView, some sourceView]) := rfl

theorem nonempty_prefix_certificate : (prefixLeft outer).bind prefixRight = (prefixRight outer).bind prefixLeft :=
  common_prefix_copies_commute outer pre k0 k2 k1 k2 (by decide) (by decide) (by decide) .nil .nil .nil .nil

/-- info: 'Solidity.Backend.StorageOps.SnapshotControls.shared_source_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms shared_source_ordered
/-- info: 'Solidity.Backend.StorageOps.actual_mapping_copies_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms actual_mapping_copies_commute
/-- info: 'Solidity.Backend.StorageOps.SnapshotControls.all_depth_commutes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms all_depth_commutes

/-- info: 'Solidity.Backend.StorageOps.SnapshotControls.all_depth_actual_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms all_depth_actual_success
end Solidity.Backend.StorageOps.SnapshotControls
