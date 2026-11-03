import Solidity.Backend.StorageOps.OutputRootComposition

/-! Exact failed observations beyond the independent copy result extent.
These operation-side laws reuse existing typed paths/queries. A failed query
places NO physical-cell/default/frame or world rollback constraint on a store. -/
namespace Solidity.Backend.StorageOps.AbsentRootQueries
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

theorem find_missing {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old source : Value G (.array E)) (i : Index)
    (outside : max old.extent.val source.length.val ≤ i.val) :
    (old.overlay source).find (.cons (.index i) .nil) = none := by
  cases old with
  | array oe ol oh os =>
    cases source with
    | array ne nl nh ns =>
      change max oe.val nl.val ≤ i.val at outside
      simp only [Value.overlay,Value.find,TypeGraph.Path.read,Step.get,
        dif_neg (Nat.not_lt_of_ge outside),Option.bind_none]

theorem find_suffix {n : Nat} {G : Schema n} {E U : TypeGraph.Ty n}
    (old source : Value G (.array E)) (i : Index) (suffix : TypeGraph.Path G E U)
    (outside : max old.extent.val source.length.val ≤ i.val) :
    (old.overlay source).find ((.cons (.index i) .nil : TypeGraph.Path G (.array E) E).append suffix) = none := by
  unfold Value.find
  rw [TypeGraph.Path.read_append]
  change ((old.overlay source).find (.cons (.index i) .nil)).bind _ = none
  rw [find_missing old source i outside]
  rfl

theorem observe_suffix {n : Nat} {G : Schema n} {E U : TypeGraph.Ty n}
    (old source : Value G (.array E)) (i : Index) (suffix : TypeGraph.Path G E U)
    (outside : max old.extent.val source.length.val ≤ i.val) :
    (old.overlay source).observe ((.cons (.index i) .nil : TypeGraph.Path G (.array E) E).append suffix) = none := by
  rw [Value.observe_append,find_missing old source i outside,Option.bind_none]

theorem query_missing {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old source : Value G (.array E)) (i : Index) (q : Query G E)
    (outside : max old.extent.val source.length.val ≤ i.val) :
    (q.prefix (.cons (.index i) .nil)).read (old.overlay source) = none ∧
    (q.prefix (.cons (.index i) .nil)).compatible (old.overlay source) := by
  cases q with
  | word suffix =>
    simp only [Query.prefix,Query.read,Query.compatible,observe_suffix old source i suffix outside,Option.map_none,and_self]
  | length suffix =>
    simp only [Query.prefix,Query.read,Query.compatible,observe_suffix old source i suffix outside,Option.map_none,and_self]

/-- Deliberately only the PUBLIC logical observation relation: arbitrary store
and location, because None never specifies a raw word. Explicit query support
is preserved. The actual operation's target/numeric contract is separate. -/
theorem represented_missing {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old source : Value G (.array E)) (i : Index) (queries : List (Query G E))
    (outside : max old.extent.val source.length.val ≤ i.val)
    (supported : ∀ q ∈ queries, (q.prefix (.cons (.index i) .nil)).supported)
    (location : Solidity.Storage.Loc) (store : Store) :
    Represented (old.overlay source) (queries.map (Query.prefix (.cons (.index i) .nil))) location store := by
  intro q member
  rcases List.mem_map.mp member with ⟨q,inside,rfl⟩
  have failed := query_missing old source i q outside
  refine ⟨supported q inside,failed.2,?_⟩
  intro word observed
  rw [failed.1] at observed
  cases observed

/-- info: 'Solidity.Backend.StorageOps.AbsentRootQueries.find_missing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms find_missing
/-- info: 'Solidity.Backend.StorageOps.AbsentRootQueries.find_suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms find_suffix
/-- info: 'Solidity.Backend.StorageOps.AbsentRootQueries.observe_suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms observe_suffix
/-- info: 'Solidity.Backend.StorageOps.AbsentRootQueries.query_missing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms query_missing
/-- info: 'Solidity.Backend.StorageOps.AbsentRootQueries.represented_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_missing
end Solidity.Backend.StorageOps.AbsentRootQueries
