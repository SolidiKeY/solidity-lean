import Solidity.Storage.Representation.GraphRepresentation
import Solidity.Storage.HashedSeparation

/-! Operation-side header separation for existing typed path/query accesses.
Generalized-index recursors preserve G0. Symbolic depth monotonicity does not
assert typed-query injectivity or global numeric/hash separation. -/
namespace Solidity.Backend.StorageOps.OperationDepth
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

theorem step_depth {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (step : TypeGraph.Step G A B) (l : Solidity.Storage.Loc) : l.depth ≤ (stepLoc step l).depth :=
  @TypeGraph.Step.rec n G (fun _ _ s => ∀ l, l.depth ≤ (stepLoc s l).depth)
    (fun {_ _} position l => by simp only [stepLoc,Solidity.Storage.Loc.depth_add]; exact Nat.le_refl _)
    (fun {_} i l => by change l.depth ≤ l.depth + 1; omega)
    (fun {_ _} i l => by simp only [stepLoc,Solidity.Storage.Loc.depth_add]; exact Nat.le_refl _)
    (fun {_ _} key l => by change l.depth ≤ l.depth + 1; omega) A B step l

theorem path_depth {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (path : TypeGraph.Path G A B) (l : Solidity.Storage.Loc) : l.depth ≤ (pathLoc path l).depth :=
  @TypeGraph.Path.rec n G (fun _ _ p => ∀ l, l.depth ≤ (pathLoc p l).depth)
    (fun {_} _l => Nat.le_refl _)
    (fun {_ _ _} step _ ih l => Nat.le_trans (step_depth step l) (ih (stepLoc step l))) A B path l

theorem query_depth {n : Nat} {G : Schema n} {A : TypeGraph.Ty n}
    (q : Query G A) (l : Solidity.Storage.Loc) : l.depth ≤ (q.location l).depth := by
  cases q with
  | word path => exact path_depth path l
  | length path => exact path_depth path l

/-- Every query below a dynamic-array index is symbolically distinct from
that array header, even when its logical read fails. Numeric separation still
requires the published finite-run coverage/region premise. -/
theorem indexed_ne_header {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (q : Query G E) (i : Index) (base : Solidity.Storage.Loc) :
    (q.prefix (.cons (.index i) .nil)).location base ≠ base := by
  have deeper := query_depth q (Solidity.Storage.Loc.data base (i.val * inlineSize G E))
  intro same
  rw [Query.location_prefix] at same
  change q.location (Solidity.Storage.Loc.data base (i.val * inlineSize G E)) = base at same
  rw [same] at deeper
  change base.depth + 1 ≤ base.depth at deeper
  omega

/-- info: 'Solidity.Backend.StorageOps.OperationDepth.step_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_depth
/-- info: 'Solidity.Backend.StorageOps.OperationDepth.path_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms path_depth
/-- info: 'Solidity.Backend.StorageOps.OperationDepth.query_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms query_depth
/-- info: 'Solidity.Backend.StorageOps.OperationDepth.indexed_ne_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms indexed_ne_header
end Solidity.Backend.StorageOps.OperationDepth
