import Solidity.Backend.StorageOps.CopyCompatibility
import Solidity.Backend.StorageOps.CopyReadCapture

/-! Actual recursive numeric copy root-header agreement. Arbitrary intrinsic
aggregate elements are retained. This is not general inner payload preservation
or machine-discovered loop realization. -/
namespace Solidity.Backend.StorageOps.CopyHeaders
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Header-last execution reads its value from the captured INITIAL source,
even when preceding nested writes physically overlap either header. -/
theorem numeric_header {n N : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old src : Value G (.array E)) (dst source : Solidity.Storage.Loc)
    (hash : Solidity.Storage.Pre → Nat) (initial : WordStore) :
    CopyWrites.numericCopy (N := N) old src dst source hash initial (dst.word N hash) =
      initial (source.word N hash) := by
  cases old with
  | array oe ol oh os =>
    cases src with
    | array ne nl nh ns =>
      simp only [CopyWrites.numericCopy,CopyWrites.updates,CopyWrites.queryWrites,
        List.map_append,List.foldl_append,List.map_cons,List.map_nil,
        List.foldl_cons,List.foldl_nil,Query.location,pathLoc,writeWord,ite_true]

/-- The independent recursive operation retains exactly the source root length. -/
theorem graph_header {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old src : Value G (.array E)) :
    (Query.length .nil).read (recursiveCopy old src) = (Query.length .nil).read src := by
  cases old with
  | array oe ol oh os =>
    cases src with
    | array ne nl nh ns => rfl

/-- Header compatibility follows from the ORIGINAL two root-header bounds.
No bound on an unobserved child or source admission cap is introduced. -/
theorem graph_header_compatible {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old src : Value G (.array E))
    (oldBound : (Query.length .nil).compatible old)
    (srcBound : (Query.length .nil).compatible src) :
    (Query.length .nil).compatible (recursiveCopy old src) := by
  cases old with
  | array oe ol oh os =>
    cases src with
    | array ne nl nh ns =>
      change ol.val ≤ lmax ∧ oe.val ≤ lmax at oldBound
      change nl.val ≤ lmax ∧ ne.val ≤ lmax at srcBound
      change nl.val ≤ lmax ∧ max oe.val nl.val ≤ lmax
      exact ⟨srcBound.1,Nat.max_le.mpr ⟨oldBound.2,srcBound.1⟩⟩

/-- Actual numeric header agrees with the independent operation read using
only the PUBLIC selected SOURCE header relation and initial finite transport. -/
theorem header_agreement {n N : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old src : Value G (.array E)) (dst source : Solidity.Storage.Loc)
    (store : Store) (initial : WordStore) (hash : Solidity.Storage.Pre → Nat)
    (locations : List Solidity.Storage.Loc)
    (beforeSrc : Represented src [.length .nil] source store)
    (transported : Transport N hash locations store initial)
    (sourceCovered : source ∈ locations) :
    ∀ word, (Query.length .nil).read (recursiveCopy old src) = some word →
      CopyWrites.numericCopy (N := N) old src dst source hash initial (dst.word N hash) = word := by
  intro word observed
  rw [numeric_header,transported source sourceCovered]
  apply (beforeSrc (.length .nil) (by exact List.mem_singleton_self _)).2.2 word
  rwa [graph_header] at observed

/-- PUBLIC post root-header representation and actual generated numeric
Transport derive together. Every nested write is generated, not supplied.
Other selected queries and complete payload representation are separate. -/
theorem represented_header {n N L R : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old src : Value G (.array E)) (dst source : Solidity.Storage.Loc)
    (store : Store) (initial : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (beforeDst : Represented old [.length .nil] dst store)
    (beforeSrc : Represented src [.length .nil] source store)
    (before : Transport N hash locations store initial)
    (dstCovered : dst ∈ locations) (sourceCovered : source ∈ locations)
    (writesCovered : ∀ q ∈ CopyDemands.demands old src, q.location dst ∈ locations) :
    let log := CopyWrites.updates (N := N) old src dst source hash initial
    let after := log.foldl (fun w op => write w op.1 op.2) store
    Represented (recursiveCopy old src) [.length .nil] dst after ∧
    Transport N hash locations after (CopyWrites.numericCopy (N := N) old src dst source hash initial) := by
  dsimp only
  have transported := transport_sequence run before
    (CopyWrites.updates (N := N) old src dst source hash initial) (by
      intro op inside
      obtain ⟨q,member,same⟩ := CopyWrites.generated old src dst source hash initial op inside
      rw [same]
      exact writesCovered q member)
  refine ⟨?_,transported⟩
  intro q inside
  have same := List.mem_singleton.mp inside
  subst q
  refine ⟨True.intro,graph_header_compatible old src
    (beforeDst (.length .nil) (List.mem_singleton_self _)).2.1
    (beforeSrc (.length .nil) (List.mem_singleton_self _)).2.1,?_⟩
  intro word observed
  exact (transported dst dstCovered).symm.trans
    (header_agreement old src dst source store initial hash locations beforeSrc before sourceCovered word observed)

/-- info: 'Solidity.Backend.StorageOps.CopyHeaders.numeric_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms numeric_header
/-- info: 'Solidity.Backend.StorageOps.CopyHeaders.graph_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms graph_header
/-- info: 'Solidity.Backend.StorageOps.CopyHeaders.graph_header_compatible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms graph_header_compatible
/-- info: 'Solidity.Backend.StorageOps.CopyHeaders.header_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms header_agreement
/-- info: 'Solidity.Backend.StorageOps.CopyHeaders.represented_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms represented_header

end Solidity.Backend.StorageOps.CopyHeaders
