import Solidity.Backend.StorageOps.LifecyclePaths

/-! Typed path readback and retained/live behavior for independently implemented
clear and pop. These Option laws are not transaction/world rollback. -/
namespace Solidity.Backend.StorageOps
open TypeGraph

theorem deleteAt_saved {n : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A T) (old : Value G T)
    (read : root.find pre = some old) (deleted : deleteAt root pre = some result) :
    root.save pre (recursiveClear old) = some result := by
  simpa only [deleteAt, modifyAt, read, Option.bind_eq_bind, Option.bind_some] using deleted

theorem deleteAt_readback {n : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A T) (old : Value G T)
    (read : root.find pre = some old) (deleted : deleteAt root pre = some result) :
    result.find pre = some (recursiveClear old) :=
  root.find_save result pre _ (deleteAt_saved root result pre old read deleted)

theorem deleteAt_mapping_read {n : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
    {K : PrimTy} {V : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A T)
    (suffix : TypeGraph.Path G T (.mapping K V)) (old : Value G T)
    (read : root.find pre = some old) (deleted : deleteAt root pre = some result) :
    result.find (pre.append suffix) = root.find (pre.append suffix) := by
  have after := deleteAt_readback root result pre old read deleted
  simp only [Value.find, TypeGraph.Path.read_append]
  change (result.find pre).bind (fun v => v.find suffix) = (root.find pre).bind (fun v => v.find suffix)
  simp only [read, after, Option.bind_some, recursiveClear_mapping_read]

/-- Before-live prefix is preserved; every array index below the deleted array
is nonlive afterward, even though retained logical reads can still succeed. -/
theorem deleteAt_invalidates_live {n : Nat} {G : Schema n} {A E B : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A (.array E)) (old : Value G (.array E))
    (live : pre.readLive Value.dflt root = some old) (deleted : deleteAt root pre = some result)
    (i : Index) (suffix : TypeGraph.Path G E B) :
    (pre.append (.cons (.index i) suffix)).readLive Value.dflt result = none := by
  have read := prefix_live_find pre root old live
  have saved := deleteAt_saved root result pre old read deleted
  have after := prefix_live_save pre root result old (recursiveClear old) live saved
  simp only [live_read_append, after, Option.bind_some, TypeGraph.Path.readLive]
  cases old
  simp only [recursiveClear, TypeGraph.Step.getLive, Nat.not_lt_zero, if_false, Option.bind_none]

theorem popAt_operational_readback {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A (.array E))
    (popped : popAt root pre = some result) : ∃ old value,
      root.find pre = some old ∧ recursivePop old = some value ∧
      root.save pre value = some result ∧ result.find pre = some value ∧
      value.length.val + 1 = old.length.val ∧ value.extent = old.extent := by
  obtain ⟨old, value, read, changed, saved⟩ := modifyAt_success root result pre recursivePop popped
  exact ⟨old, value, read, changed, saved, root.find_save result pre value saved,
    recursivePop_header old value changed⟩

/-- All suffix outcomes at every other retained index are preserved. This
includes failed suffix reads, without a bound/live premise on the index. -/
theorem popAt_other_path {n : Nat} {G : Schema n} {A E B : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A (.array E))
    (old : Value G (.array E)) (read : root.find pre = some old)
    (popped : popAt root pre = some result) (i : Index)
    (other : i.val ≠ old.length.val - 1) (suffix : TypeGraph.Path G E B) :
    result.find (pre.append (.cons (.index i) suffix)) =
      root.find (pre.append (.cons (.index i) suffix)) := by
  obtain ⟨actual, value, found, changed, saved, after, _⟩ := popAt_operational_readback root result pre popped
  rw [read] at found
  cases found
  simp only [Value.find, TypeGraph.Path.read_append]
  change (result.find pre).bind (fun v => (TypeGraph.Step.get Value.dflt (.index i) v).bind (suffix.read Value.dflt)) =
    (root.find pre).bind (fun v => (TypeGraph.Step.get Value.dflt (.index i) v).bind (suffix.read Value.dflt))
  simp only [read, after, Option.bind_some, recursivePop_other old value changed i other]

/-- info: 'Solidity.Backend.StorageOps.deleteAt_saved' does not depend on any axioms -/
#guard_msgs in #print axioms deleteAt_saved
/-- info: 'Solidity.Backend.StorageOps.deleteAt_readback' depends on axioms: [propext] -/
#guard_msgs in #print axioms deleteAt_readback
/-- info: 'Solidity.Backend.StorageOps.deleteAt_mapping_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms deleteAt_mapping_read
/-- info: 'Solidity.Backend.StorageOps.deleteAt_invalidates_live' depends on axioms: [propext] -/
#guard_msgs in #print axioms deleteAt_invalidates_live
/-- info: 'Solidity.Backend.StorageOps.popAt_operational_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms popAt_operational_readback
/-- info: 'Solidity.Backend.StorageOps.popAt_other_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms popAt_other_path
end Solidity.Backend.StorageOps
