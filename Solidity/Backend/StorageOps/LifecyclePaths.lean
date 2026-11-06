import Solidity.Backend.StorageOps.LivePrefix
import Solidity.Backend.StorageOps.RecursivePop
import Solidity.Backend.StorageOps.OperationPush

/-! Executable typed graph lifecycle operations through existing paths.
No source admission/representation/target allocation or world rollback claim.
The graph's own capacity test is preserved, not imposed as a source cap. -/
namespace Solidity.Backend.StorageOps
open TypeGraph

def pushAt {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root : Value G A) (pre : TypeGraph.Path G A (.array E)) : Option (Value G A) :=
  modifyAt root pre operationPush

def popAt {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root : Value G A) (pre : TypeGraph.Path G A (.array E)) : Option (Value G A) :=
  modifyAt root pre recursivePop

/-- This deletion adapter realizes delAt through independent recursive clear. -/
def deleteAt {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root : Value G A) (pre : TypeGraph.Path G A E) : Option (Value G A) :=
  modifyAt root pre (fun value => some (recursiveClear value))

theorem deleteAt_eq_delAt {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root : Value G A) (pre : TypeGraph.Path G A E) : deleteAt root pre = root.delAt pre := by
  simp only [deleteAt, modifyAt, recursiveClear_eq_clear, Value.delAt, Option.bind_eq_bind, Option.bind_some]

/-- No extra save failure follows a readable typed prefix and successful local
effect. This law concerns Option results, not externally visible world rollback. -/
theorem modifyAt_failure {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (root : Value G A) (pre : TypeGraph.Path G A B)
    (effect : Value G B → Option (Value G B)) :
    modifyAt root pre effect = none ↔ (root.find pre).bind effect = none := by
  cases read : root.find pre with
  | none => simp only [modifyAt, Option.bind_eq_bind, read, Option.bind_none]
  | some old =>
    cases changed : effect old with
    | none => simp only [modifyAt, Option.bind_eq_bind, read, Option.bind_some, changed, Option.bind_none]
    | some value =>
      obtain ⟨result, saved⟩ := prefix_save_exists pre root old value read
      simp only [modifyAt, Option.bind_eq_bind, read, Option.bind_some, changed, saved, reduceCtorEq]

/-- Nested push capacity failure is exactly the existing graph check. -/
theorem pushAt_fails_found {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root : Value G A) (pre : TypeGraph.Path G A (.array E)) (old : Value G (.array E))
    (read : root.find pre = some old) : pushAt root pre = none ↔ 2 ^ 256 ≤ old.length.val + 1 := by
  simp only [pushAt, modifyAt_failure, read, Option.bind_some, operationPush_eq_push, push_fails_iff]

theorem popAt_fails_found {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root : Value G A) (pre : TypeGraph.Path G A (.array E)) (old : Value G (.array E))
    (read : root.find pre = some old) : popAt root pre = none ↔ old.length.val = 0 := by
  simp only [popAt, modifyAt_failure, read, Option.bind_some, recursivePop_eq_pop, pop_fails_iff]

theorem deleteAt_failure {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root : Value G A) (pre : TypeGraph.Path G A E) : deleteAt root pre = none ↔ root.find pre = none := by
  cases read : root.find pre <;> simp only [deleteAt, modifyAt_failure, read,
    Option.bind_none, Option.bind_some, reduceCtorEq]

/-- A successful modification exposes its actual old value, effect result and
save. It does not assume any of these results as a preservation premise. -/
theorem modifyAt_success {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A B)
    (effect : Value G B → Option (Value G B))
    (modified : modifyAt root pre effect = some result) : ∃ old value,
      root.find pre = some old ∧ effect old = some value ∧ root.save pre value = some result := by
  simp only [modifyAt, Option.bind_eq_bind] at modified
  obtain ⟨old, read, changed⟩ := Option.bind_eq_some_iff.mp modified
  obtain ⟨value, effectOK, saved⟩ := Option.bind_eq_some_iff.mp changed
  exact ⟨old, value, read, effectOK, saved⟩

theorem pushAt_result {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A (.array E)) (old : Value G (.array E))
    (read : root.find pre = some old) (pushed : pushAt root pre = some result) : ∃ value,
      old.push = some value ∧ root.save pre value = some result ∧ result.find pre = some value ∧
      value.length.val = old.length.val + 1 ∧ old.extent.val ≤ value.extent.val := by
  have semantic : modifyAt root pre Value.push = some result := by
    simpa only [pushAt, modifyAt, operationPush_eq_push] using pushed
  obtain ⟨actual, value, found, changed, saved⟩ := modifyAt_success root result pre Value.push semantic
  rw [read] at found
  cases found
  exact ⟨value, changed, saved, Value.find_save root result pre value saved,
    old.push_length value changed, old.push_extent value changed⟩

theorem popAt_result {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A (.array E)) (old : Value G (.array E))
    (read : root.find pre = some old) (popped : popAt root pre = some result) : ∃ value,
      old.pop = some value ∧ root.save pre value = some result ∧ result.find pre = some value ∧
      value.length.val + 1 = old.length.val ∧ value.extent = old.extent := by
  have semantic : modifyAt root pre Value.pop = some result := by
    simpa only [popAt, modifyAt, recursivePop_eq_pop] using popped
  obtain ⟨actual, value, found, changed, saved⟩ := modifyAt_success root result pre Value.pop semantic
  rw [read] at found
  cases found
  have lengths := old.pop_length value changed
  exact ⟨value, changed, saved, Value.find_save root result pre value saved, lengths⟩

/-- A retained aggregate alias and every suffix observation keep their identity
across a nested push, without pretending that a retained prefix is live. -/
theorem pushAt_reused_alias {n : Nat} {G : Schema n} {A E B : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A (.array E)) (old : Value G (.array E))
    (read : root.find pre = some old) (pushed : pushAt root pre = some result)
    (i : Index) (aggregate : E.isPrimitive = false) (retained : i.val < old.extent.val)
    (suffix : TypeGraph.Path G E B) :
    result.find (pre.append (.cons (.index i) suffix)) =
      root.find (pre.append (.cons (.index i) suffix)) := by
  obtain ⟨value, changed, saved, found, _, _⟩ := pushAt_result root result pre old read pushed
  change pre.read Value.dflt root = some old at read
  change pre.read Value.dflt result = some value at found
  simp only [Value.find, TypeGraph.Path.read_append, read, found, Option.bind_some,
    TypeGraph.Path.read]
  rw [push_reused_reference old value i aggregate retained changed]

/-- Removing the last element invalidates every live suffix alias, transported
through a prefix that was itself live before the actual pop. -/
theorem popAt_invalidates_live {n : Nat} {G : Schema n} {A E B : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A (.array E)) (old : Value G (.array E))
    (live : pre.readLive Value.dflt root = some old) (popped : popAt root pre = some result)
    (i : Index) (last : i.val + 1 = old.length.val) (suffix : TypeGraph.Path G E B) :
    (pre.append (.cons (.index i) suffix)).readLive Value.dflt result = none := by
  have read := prefix_live_find pre root old live
  obtain ⟨value, changed, saved, _, _, _⟩ := popAt_result root result pre old read popped
  have liveAfter := prefix_live_save pre root result old value live saved
  simp only [live_read_append, liveAfter, Option.bind_some, TypeGraph.Path.readLive,
    pop_invalidates_live old value i last changed, Option.bind_none]

/-- A push revives its retained aggregate slot at the old live length. Every
inner live suffix now sees exactly that retained value's suffix observation. -/
theorem pushAt_revives_live {n : Nat} {G : Schema n} {A E B : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A (.array E)) (old : Value G (.array E))
    (live : pre.readLive Value.dflt root = some old) (pushed : pushAt root pre = some result)
    (aggregate : E.isPrimitive = false) (retained : old.length.val < old.extent.val)
    (suffix : TypeGraph.Path G E B) :
    (pre.append (.cons (.index old.length) suffix)).readLive Value.dflt result =
      (TypeGraph.Step.get Value.dflt (.index old.length) old).bind (suffix.readLive Value.dflt) := by
  have read := prefix_live_find pre root old live
  obtain ⟨value, changed, saved, _, lengthEq, _⟩ := pushAt_result root result pre old read pushed
  have liveAfter := prefix_live_save pre root result old value live saved
  have kept := push_reused_reference old value old.length aggregate retained changed
  have nowLive : TypeGraph.Step.getLive Value.dflt (.index old.length) value =
      TypeGraph.Step.get Value.dflt (.index old.length) old := by
    cases value with
    | array extent length le slots =>
      change length.val = old.length.val + 1 at lengthEq
      have inside : old.length.val < length.val := by omega
      simpa only [TypeGraph.Step.getLive, if_pos inside] using kept
  simp only [live_read_append, liveAfter, Option.bind_some, TypeGraph.Path.readLive, nowLive]

end Solidity.Backend.StorageOps
