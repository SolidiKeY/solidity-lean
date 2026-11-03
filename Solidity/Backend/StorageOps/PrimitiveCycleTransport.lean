import Solidity.Backend.StorageOps.GraphRetainedCycle
import Solidity.Backend.StorageOps.TargetPrimitivePopPush

/-! Primitive pop/regrow/pop transport uses the PUBLISHED Query/Represented
relation. Raw slot/value identity is not asserted; PRESENT zero and ABSENT
remain distinct. No new state/relation/evaluator or Source profile restriction. -/
namespace Solidity.Backend.StorageOps.PrimitiveCycleTransport
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

theorem headers {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
 (old middle grown result : Value G (.array E))
 (popped : recursivePop old=some middle) (pushed : operationPush middle=some grown)
 (second : recursivePop grown=some result) :
 result.length=middle.length ∧ result.extent=middle.extent := by
 have firstHeader := recursivePop_header old middle popped
 have growHeader := PopPush.headers old middle grown popped pushed
 have secondHeader := recursivePop_header grown result second
 exact ⟨Fin.ext (by omega),secondHeader.2.trans (growHeader.2.trans firstHeader.2.symm)⟩

/-- Every requested primitive word outcome, including retained and failed reads. -/
theorem element_read {n : Nat} {G : Schema n} {p : PrimTy}
 (old middle grown result : Value G (.array (.prim p)))
 (popped : recursivePop old=some middle) (pushed : operationPush middle=some grown)
 (second : recursivePop grown=some result) (i : Index) :
 (PrimitivePop.elementQuery i).read result=(PrimitivePop.elementQuery i).read middle := by
 have lengths := (PopPush.headers old middle grown popped pushed).1
 by_cases last : i.val=old.length.val-1
 · rw [PrimitivePop.last_read old middle popped i last]
   exact PrimitivePop.last_read grown result second i (by rw [lengths]; exact last)
 · rw [PrimitivePop.other_read old middle popped i last,
     PrimitivePop.other_read grown result second i (by rw [lengths]; exact last),
     TargetPrimitivePopPush.element_read old middle grown popped pushed i,if_neg last]

/-- All arbitrary finite requested PUBLIC primitive query outcomes are preserved. -/
theorem query_read {n : Nat} {G : Schema n} {p : PrimTy}
 (old middle grown result : Value G (.array (.prim p)))
 (popped : recursivePop old=some middle) (pushed : operationPush middle=some grown)
 (second : recursivePop grown=some result) (indices : List Index)
 (query : Query G (.array (.prim p))) (member : query ∈ PrimitivePop.queries indices) :
 query.read result=query.read middle := by
 simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
 rcases member with rfl | ⟨i,_,rfl⟩
 · have lengths := (headers old middle grown result popped pushed second).1
   cases middle
   cases result
   cases lengths
   rfl
 · exact element_read old middle grown result popped pushed second i

/-- Compatibility is derived from unchanged actual headers/extents, not supplied
as a post-premise or turned into a new source length cap. -/
theorem query_compatible {n : Nat} {G : Schema n} {p : PrimTy}
 (old middle grown result : Value G (.array (.prim p)))
 (popped : recursivePop old=some middle) (pushed : operationPush middle=some grown)
 (second : recursivePop grown=some result) (indices : List Index)
 (query : Query G (.array (.prim p))) (member : query ∈ PrimitivePop.queries indices) :
 query.compatible result=query.compatible middle := by
 simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
 rcases member with rfl | ⟨i,_,rfl⟩
 · have h := headers old middle grown result popped pushed second
   cases middle
   cases result
   cases h.1
   cases h.2
   rfl
 · rfl

/-- Reuse the existing owner relation at the SAME symbolic store. This does not
identify raw values, invent a quotient, or assume desired preservation. -/
theorem represented_iff {n : Nat} {G : Schema n} {p : PrimTy}
 (old middle grown result : Value G (.array (.prim p)))
 (popped : recursivePop old=some middle) (pushed : operationPush middle=some grown)
 (second : recursivePop grown=some result) (indices : List Index)
 (base : Solidity.Storage.Loc) (store : Store) :
 Represented result (PrimitivePop.queries indices) base store ↔
 Represented middle (PrimitivePop.queries indices) base store := by
 constructor
 · intro owner query member
   obtain ⟨supported,compatible,observed⟩ := owner query member
   refine ⟨supported,?_,?_⟩
   · rwa [query_compatible old middle grown result popped pushed second indices query member] at compatible
   · intro word found
     exact observed word ((query_read old middle grown result popped pushed second indices query member).trans found)
 · intro owner query member
   obtain ⟨supported,compatible,observed⟩ := owner query member
   refine ⟨supported,?_,?_⟩
   · rw [query_compatible old middle grown result popped pushed second indices query member]
     exact compatible
   · intro word found
     exact observed word ((query_read old middle grown result popped pushed second indices query member).symm.trans found)

/-- OLD PUBLIC representation derives FIRST-pop ownership then actual cycle
ownership. No intermediate or final owner is a premise. -/
theorem complete {n : Nat} {G : Schema n} {p : PrimTy}
 (old middle grown result : Value G (.array (.prim p)))
 (popped : recursivePop old=some middle) (pushed : operationPush middle=some grown)
 (second : recursivePop grown=some result) (indices : List Index)
 (base : Solidity.Storage.Loc) (store : Store)
 (before : Represented old (PrimitivePop.queries indices) base store) :
 GraphRetainedCycle.execute old=some result ∧
 Represented result (PrimitivePop.queries indices) base
  (Representation.write (Representation.write store (.data base (old.length.val-1)) ClearDemands.zero)
   base (lengthWord middle.length.val middle.length.isLt)) := by
 have owner := PrimitivePop.represented old middle popped indices base store before
 refine ⟨?_,(represented_iff old middle grown result popped pushed second indices base _).mpr owner⟩
 unfold GraphRetainedCycle.execute
 rw [popped]
 change (do let value ← operationPush middle; recursivePop value)=some result
 rw [pushed]
 exact second

/-- BOTH exact Option outcomes and the complete ordered requested query vector.
This does not equate the underlying raw Value or discard any failed read. -/
theorem outcome_queries {n : Nat} {G : Schema n} {p : PrimTy}
 (old : Value G (.array (.prim p))) (indices : List Index) :
 (GraphRetainedCycle.execute old).map (fun value => (PrimitivePop.queries indices).map (fun query => query.read value)) =
 (recursivePop old).map (fun value => (PrimitivePop.queries indices).map (fun query => query.read value)) := by
 cases popped : recursivePop old with
 | none =>
   unfold GraphRetainedCycle.execute
   rw [popped]
   rfl
 | some middle =>
   obtain ⟨grown,pushed⟩ := NestedPopRegrow.push_exists old middle popped
   have firstHeader := recursivePop_header old middle popped
   have growHeader := PopPush.headers old middle grown popped pushed
   cases second : recursivePop grown with
   | none =>
     have empty := (recursivePop_failure grown).mp second
     omega
   | some result =>
     have executed : GraphRetainedCycle.execute old=some result := by
       unfold GraphRetainedCycle.execute
       rw [popped]
       change (do let value ← operationPush middle; recursivePop value)=some result
       rw [pushed]
       exact second
     rw [executed]
     apply congrArg some
     apply List.map_congr_left
     intro query member
     exact query_read old middle grown result popped pushed second indices query member

/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleTransport.headers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms headers
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleTransport.element_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms element_read
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleTransport.query_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms query_read
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleTransport.query_compatible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms query_compatible
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleTransport.represented_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_iff
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleTransport.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleTransport.outcome_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms outcome_queries
end Solidity.Backend.StorageOps.PrimitiveCycleTransport
