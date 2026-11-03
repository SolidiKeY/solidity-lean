import Solidity.Storage.Representation.GraphRepresentation
import Solidity.Backend.StorageOps.RecursiveCopy
import Solidity.Backend.StorageOps.RecursiveLifecycleFacts

/-! Operation-side applications of the PUBLIC owner's representation relation.
No replacement representation/encoder is introduced. Successful source graph
operations determine the written word; source frames and finite-run numeric
transport reuse the published theorems with all their explicit premises. -/
namespace Solidity.Backend.StorageOps.RepresentedOperations
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Actual successful scalar path replacement updates its represented word and
frames every explicitly apart, symbolically nonaliasing observation demand. -/
theorem scalar_save {n : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy}
    (root result : Value G A) (dst : TypeGraph.Path G A (.prim p)) (value : p.Denote)
    (queries : List (Query G A)) (base : Solidity.Storage.Loc) (store : Store)
    (represented : Represented root queries base store) (supported : PathSupported dst)
    (saved : root.save dst (.prim value) = some result)
    (apart : ∀ q ∈ queries, q.apart dst)
    (nonalias : ∀ q ∈ queries, q.location base ≠ pathLoc dst base) :
    Represented result (.word dst :: queries) base
      (write store (pathLoc dst base) (PrimTy.toWord value)) := by
  have frame := represented.write_frame dst (.prim value) saved (PrimTy.toWord value) apart nonalias
  have read : (Query.word dst).read result = some (PrimTy.toWord value) := by
    simp only [Query.read, Value.observe, root.find_save result dst (.prim value) saved,
      Option.map_some, Value.head]
  intro q member
  rcases List.mem_cons.mp member with equal | later
  · subst q
    refine ⟨supported, True.intro, ?_⟩
    intro word observed
    have same : word = PrimTy.toWord value := Option.some.inj (observed.symm.trans read)
    subst word
    exact write_same store (pathLoc dst base) (PrimTy.toWord value)
  · exact frame q later

/-- The new word is extracted from the ACTUAL effect result and actual save,
not supplied as a desired preservation premise. -/
theorem modifyAt_scalar {n : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy}
    (root result : Value G A) (dst : TypeGraph.Path G A (.prim p))
    (effect : Value G (.prim p) → Option (Value G (.prim p)))
    (performed : modifyAt root dst effect = some result)
    (queries : List (Query G A)) (base : Solidity.Storage.Loc) (store : Store)
    (represented : Represented root queries base store) (supported : PathSupported dst)
    (apart : ∀ q ∈ queries, q.apart dst)
    (nonalias : ∀ q ∈ queries, q.location base ≠ pathLoc dst base) :
    ∃ before after : p.Denote, root.find dst = some (.prim before) ∧
      effect (.prim before) = some (.prim after) ∧
      Represented result (.word dst :: queries) base
        (write store (pathLoc dst base) (PrimTy.toWord after)) := by
  obtain ⟨old, value, read, changed, saved⟩ := modifyAt_success root result dst effect performed
  cases old with
  | prim before =>
    cases value with
    | prim after =>
      exact ⟨before, after, read, changed, scalar_save root result dst after queries base store represented supported saved apart nonalias⟩

/-- Scalar-endpoint snapshot copy preserves the published relation after its
source was read from the original graph, including overlapping/self paths. -/
theorem copyAt_scalar {n : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy}
    (root result : Value G A) (dst src : TypeGraph.Path G A (.prim p)) (value : p.Denote)
    (source : root.find src = some (.prim value))
    (performed : recursiveCopyAt root dst src = some result)
    (queries : List (Query G A)) (base : Solidity.Storage.Loc) (store : Store)
    (represented : Represented root queries base store) (supported : PathSupported dst)
    (apart : ∀ q ∈ queries, q.apart dst)
    (nonalias : ∀ q ∈ queries, q.location base ≠ pathLoc dst base) :
    Represented result (.word dst :: queries) base
      (write store (pathLoc dst base) (PrimTy.toWord value)) := by
  simp only [recursiveCopyAt, source, Option.bind_eq_bind, Option.bind_some] at performed
  cases read : root.find dst with
  | none => simp only [read, Option.bind_none] at performed; cases performed
  | some old =>
    simp only [read, Option.bind_some] at performed
    cases old with
    | prim before =>
      exact scalar_save root result dst value queries base store represented supported performed apart nonalias

/-- Independent recursiveClear is used by actual deleteAt; the primitive
default word is the existing PrimTy normalization, not a fresh default model. -/
theorem deleteAt_scalar {n : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy}
    (root result : Value G A) (dst : TypeGraph.Path G A (.prim p))
    (performed : deleteAt root dst = some result)
    (queries : List (Query G A)) (base : Solidity.Storage.Loc) (store : Store)
    (represented : Represented root queries base store) (supported : PathSupported dst)
    (apart : ∀ q ∈ queries, q.apart dst)
    (nonalias : ∀ q ∈ queries, q.location base ≠ pathLoc dst base) :
    Represented result (.word dst :: queries) base
      (write store (pathLoc dst base) (PrimTy.toWord p.dflt)) := by
  cases read : root.find dst with
  | none => simp only [deleteAt, modifyAt, read, Option.bind_eq_bind, Option.bind_none] at performed; cases performed
  | some old =>
    have saved := deleteAt_saved root result dst old read performed
    cases old with
    | prim before =>
      exact scalar_save root result dst p.dflt queries base store represented supported saved apart nonalias

/-- Numeric preservation consumes the exact owner FiniteRun and Transport:
all bounds, recursive preimages and per-run regions remain explicit. -/
theorem scalar_save_numeric {n N L R : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy}
    {H : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R H P locations) (store : Store) (machine : WordStore)
    (transport : Transport N H locations store machine)
    (root result : Value G A) (dst : TypeGraph.Path G A (.prim p)) (value : p.Denote)
    (queries : List (Query G A)) (base : Solidity.Storage.Loc)
    (represented : Represented root queries base store) (supported : PathSupported dst)
    (saved : root.save dst (.prim value) = some result)
    (apart : ∀ q ∈ queries, q.apart dst)
    (nonalias : ∀ q ∈ queries, q.location base ≠ pathLoc dst base)
    (covered : pathLoc dst base ∈ locations) :
    let afterStore := write store (pathLoc dst base) (PrimTy.toWord value)
    let afterMachine := writeWord machine ((pathLoc dst base).word N H) (PrimTy.toWord value)
    Represented result (.word dst :: queries) base afterStore ∧
    Transport N H locations afterStore afterMachine :=
  ⟨scalar_save root result dst value queries base store represented supported saved apart nonalias,
    transport_write run transport (pathLoc dst base) covered (PrimTy.toWord value)⟩

/-- Concrete numeric operation over the owner's existing WordStore: read the
CURRENT source word before the target write, including self-aliasing. -/
def numericCopy (machine : WordStore) (dst src : Nat) : WordStore :=
  writeWord machine dst (machine src)

/-- The actual numeric source read is obtained from the owner's relation and
the actual intrinsic source find, not assumed equal to a selected target word. -/
theorem scalar_read_numeric {n N : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy}
    {H : Solidity.Storage.Pre → Nat} {locations : List Solidity.Storage.Loc}
    (root : Value G A) (src : TypeGraph.Path G A (.prim p)) (value : p.Denote)
    (queries : List (Query G A)) (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    (represented : Represented root queries base store) (member : Query.word src ∈ queries)
    (transport : Transport N H locations store machine) (covered : pathLoc src base ∈ locations)
    (source : root.find src = some (.prim value)) :
    machine ((pathLoc src base).word N H) = PrimTy.toWord value := by
  apply represented.numeric transport (.word src) member covered
  simp only [Query.read, Value.observe, source, Option.map_some, Value.head]

/-- Primitive snapshot copy relates the ACTUAL graph operation to the concrete
numeric read/write operation. Full output query coverage is explicit, as are
all owner per-run bounds/preimages/regions in FiniteRun. Not an EVM run theorem. -/
theorem copyAt_scalar_numeric {n N L R : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy}
    {H : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R H P locations) (store : Store) (machine : WordStore)
    (transport : Transport N H locations store machine)
    (root result : Value G A) (dst src : TypeGraph.Path G A (.prim p)) (value : p.Denote)
    (source : root.find src = some (.prim value)) (performed : recursiveCopyAt root dst src = some result)
    (queries : List (Query G A)) (base : Solidity.Storage.Loc)
    (represented : Represented root (.word src :: queries) base store) (supported : PathSupported dst)
    (apart : ∀ q ∈ queries, q.apart dst)
    (nonalias : ∀ q ∈ queries, q.location base ≠ pathLoc dst base)
    (sourceCovered : pathLoc src base ∈ locations) (targetCovered : pathLoc dst base ∈ locations)
    (queryCovered : ∀ q ∈ queries, q.location base ∈ locations) :
    let afterStore := write store (pathLoc dst base) (PrimTy.toWord value)
    let afterMachine := numericCopy machine ((pathLoc dst base).word N H) ((pathLoc src base).word N H)
    Represented result (.word dst :: queries) base afterStore ∧
    Transport N H locations afterStore afterMachine ∧
    ∀ q ∈ (.word dst :: queries), ∀ word, q.read result = some word →
      afterMachine ((q.location base).word N H) = word := by
  have beforeFrame : Represented root queries base store :=
    fun q member => represented q (List.mem_cons_of_mem _ member)
  have representedAfter := copyAt_scalar root result dst src value source performed queries base store beforeFrame supported apart nonalias
  have numericSource := scalar_read_numeric root src value (.word src :: queries) base store machine
    represented List.mem_cons_self transport sourceCovered source
  have transportedAfter : Transport N H locations
      (write store (pathLoc dst base) (PrimTy.toWord value))
      (numericCopy machine ((pathLoc dst base).word N H) ((pathLoc src base).word N H)) := by
    simp only [numericCopy, numericSource]
    exact transport_write run transport (pathLoc dst base) targetCovered (PrimTy.toWord value)
  refine ⟨representedAfter, transportedAfter, ?_⟩
  intro q member word observed
  have covered : q.location base ∈ locations := by
    rcases List.mem_cons.mp member with equal | later
    · subst q; exact targetCovered
    · exact queryCovered q later
  exact representedAfter.numeric transportedAfter q member covered word observed

/-- info: 'Solidity.Backend.StorageOps.RepresentedOperations.scalar_read_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms scalar_read_numeric
/-- info: 'Solidity.Backend.StorageOps.RepresentedOperations.copyAt_scalar_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copyAt_scalar_numeric
/-- info: 'Solidity.Backend.StorageOps.RepresentedOperations.scalar_save' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms scalar_save
/-- info: 'Solidity.Backend.StorageOps.RepresentedOperations.modifyAt_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms modifyAt_scalar
/-- info: 'Solidity.Backend.StorageOps.RepresentedOperations.copyAt_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copyAt_scalar
/-- info: 'Solidity.Backend.StorageOps.RepresentedOperations.deleteAt_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms deleteAt_scalar
/-- info: 'Solidity.Backend.StorageOps.RepresentedOperations.scalar_save_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms scalar_save_numeric
end Solidity.Backend.StorageOps.RepresentedOperations
