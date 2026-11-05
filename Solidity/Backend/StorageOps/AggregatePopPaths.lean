import Solidity.Backend.StorageOps.AggregatePopFrames
import Solidity.Backend.StorageOps.PathRepresentation

/-! Actual outer-root aggregate pop through existing typed capture/save paths.
The numeric operation remains graph-guided and does not discover the path/shape
from machine state or assert ordinary Source/emitted-code/world closure. -/
namespace Solidity.Backend.StorageOps.AggregatePopPaths
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- A successful root operation supplies its actual old array and save. -/
theorem captured {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A (.array E))
    (popped : popAt root pre = some result) :
    ∃ old child, root.find pre = some old ∧ recursivePop old = some child ∧
      root.save pre child = some result ∧ result.find pre = some child := by
  obtain ⟨old,child,found,changed,saved⟩ := modifyAt_success root result pre recursivePop popped
  exact ⟨old,child,found,changed,saved,Value.find_save root result pre child saved⟩

/-- Both Option outcomes at an actually captured root path. Missing path
validation is separate from this current-header operation certificate. -/
theorem failure_at {n N : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root : Value G A) (pre : TypeGraph.Path G A (.array E)) (old : Value G (.array E))
    (found : root.find pre = some old) (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    (hash : Solidity.Storage.Pre → Nat) (locations : List Solidity.Storage.Loc)
    (before : Represented root (([.length .nil] : List (Query G (.array E))).map (Query.prefix pre)) base store)
    (initial : Transport N hash locations store machine) (covered : pathLoc pre base ∈ locations) :
    AggregatePop.execute (N := N) old hash (pathLoc pre base) machine = none ↔ popAt root pre = none := by
  have focused := PathRepresentation.focus root old pre found [.length .nil] base store before
  exact (AggregatePop.failure_matches old (pathLoc pre base) store machine hash locations focused initial covered).trans
    ((recursivePop_failure old).trans (popAt_fails_found root pre old found).symm)

/-- The actual captured child operation plus C41 changed/context representation
lifts through ANY finite outer prefix. OLD ROOT owner evidence supplies support
and child relations; desired ROOT preservation is not a premise. -/
theorem complete_at {n N L R : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A (.array E)) (old : Value G (.array E))
    (found : root.find pre = some old) (popped : popAt root pre = some result)
    (selected : List (Query G E)) (groups : List (Index × List (Query G E)))
    (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (before : Represented root
      ((AggregatePop.queries old selected ++ AggregatePopFrames.contexts groups).map (Query.prefix pre)) base store)
    (initial : Transport N hash locations store machine) (headerCovered : pathLoc pre base ∈ locations)
    (targetCovered : ∀ q ∈ selected, q.location (AggregatePop.childBase old (pathLoc pre base)) ∈ locations)
    (contextCovered : ∀ q ∈ AggregatePopFrames.contexts groups, q.location (pathLoc pre base) ∈ locations)
    (writesCovered : ∀ d ∈ ClearDemands.slotDemands (AggregatePop.lastSlot old),
      d.location (AggregatePop.childBase old (pathLoc pre base)) ∈ locations)
    (separate : ∀ q ∈ selected, ∀ d ∈ ClearDemands.slotDemands (AggregatePop.lastSlot old),
      d.location (AggregatePop.childBase old (pathLoc pre base)) =
        q.location (AggregatePop.childBase old (pathLoc pre base)) → d = q)
    (headerSeparate : ∀ q ∈ selected, q.location (AggregatePop.childBase old (pathLoc pre base)) ≠ pathLoc pre base)
    (other : ∀ group ∈ groups, group.1.val ≠ old.length.val - 1)
    (nonalias : ∀ q ∈ AggregatePopFrames.contexts groups,
      ∀ op ∈ AggregatePop.updates old (pathLoc pre base), q.location (pathLoc pre base) ≠ op.1) :
    ∃ child final, recursivePop old = some child ∧ result.find pre = some child ∧
      AggregatePop.execute (N := N) old hash (pathLoc pre base) machine = some final ∧
      let after := (AggregatePop.updates old (pathLoc pre base)).foldl (fun w op => write w op.1 op.2) store
      Represented result
        ((AggregatePop.queries old selected ++ AggregatePopFrames.contexts groups).map (Query.prefix pre)) base after ∧
      Transport N hash locations after final := by
  obtain ⟨actual,child,read,changed,saved,readback⟩ := captured root result pre popped
  rw [found] at read
  cases read
  have focused := PathRepresentation.focus root old pre found
    (AggregatePop.queries old selected ++ AggregatePopFrames.contexts groups) base store before
  obtain ⟨final,executed,represented,transported⟩ := AggregatePopFrames.complete_all old child changed selected groups
    (pathLoc pre base) store machine run
    (by intro q member; exact focused q (List.mem_append.mpr (Or.inl member)))
    (by intro q member; exact focused q (List.mem_append.mpr (Or.inr member)))
    initial headerCovered targetCovered contextCovered writesCovered separate headerSeparate other nonalias
  have first : (Query.length (.nil : TypeGraph.Path G (.array E) (.array E))) ∈
      AggregatePop.queries old selected ++ AggregatePopFrames.contexts groups :=
    List.mem_append.mpr (Or.inl List.mem_cons_self)
  have rootFirst := before ((Query.length .nil).prefix pre) (List.mem_map.mpr ⟨_,first,rfl⟩)
  have supported : PathSupported pre := ((Query.supported_prefix pre (.length .nil)).mp rootFirst.1).1
  exact ⟨child,final,changed,readback,executed,Represented.prefix pre readback supported represented,transported⟩

/-- info: 'Solidity.Backend.StorageOps.AggregatePopPaths.captured' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms captured
/-- info: 'Solidity.Backend.StorageOps.AggregatePopPaths.failure_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms failure_at
/-- info: 'Solidity.Backend.StorageOps.AggregatePopPaths.complete_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete_at
end Solidity.Backend.StorageOps.AggregatePopPaths
