import Solidity.Backend.StorageOps.CopyReadCapture
import Solidity.Backend.StorageOps.NumericCopyCommutation

/-! Actual recursive numeric copy commutation with fixed typed graph captures.
Read/write sets are operation-generated, with shared read-only sources allowed.
This does not assert ordinary Source or emitted-loop/world correctness. -/
namespace Solidity.Backend.StorageOps.RecursiveNumericCommutation
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

noncomputable def writeSet {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (dst : Solidity.Storage.Loc) : List Solidity.Storage.Loc :=
  (CopyDemands.demands old src).map (fun q => q.location dst)
noncomputable def readSet {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (src : Value G T) (source : Solidity.Storage.Loc) : List Solidity.Storage.Loc :=
  (ClearDemands.demands src).map (fun q => q.location source)

/-- One actual recursive copy frames every separately covered source read.
The region hypothesis is the existing finite per-run premise. -/
theorem read_frame {n N L R : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (dst source : Solidity.Storage.Loc) (initial : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations) (reads : List Solidity.Storage.Loc)
    (writesCovered : ∀ a ∈ writeSet old src dst, a ∈ locations)
    (readsCovered : ∀ a ∈ reads, a ∈ locations)
    (separate : ∀ a ∈ writeSet old src dst, ∀ r ∈ reads, a ≠ r) :
    ∀ r ∈ reads, CopyWrites.numericCopy (N := N) old src dst source hash initial (r.word N hash) =
      initial (r.word N hash) := by
  intro r member
  apply CopyWrites.numeric_outside
  intro q inside same
  have written : q.location dst ∈ writeSet old src dst := List.mem_map.mpr ⟨q,inside,rfl⟩
  exact separate (q.location dst) written r member
    (run.word_inj (writesCovered _ written) (readsCovered _ member) same.symm)

/-- After another copy's writes, actual captured-source write generation is
unchanged when those writes do not affect its finite SOURCE read set. -/
theorem source_stable {na nb N L R : Nat} {GA : Schema na} {GB : Schema nb}
    {A : TypeGraph.Ty na} {B : TypeGraph.Ty nb}
    (oldA srcA : Value GA A) (oldB srcB : Value GB B)
    (dstA sourceA dstB sourceB : Solidity.Storage.Loc) (initial : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (writesCovered : ∀ a ∈ writeSet oldA srcA dstA, a ∈ locations)
    (readsCovered : ∀ r ∈ readSet srcB sourceB, r ∈ locations)
    (separate : ∀ a ∈ writeSet oldA srcA dstA, ∀ r ∈ readSet srcB sourceB, a ≠ r) :
    CopyWrites.updates (N := N) oldB srcB dstB sourceB hash
      (CopyWrites.numericCopy (N := N) oldA srcA dstA sourceA hash initial) =
      CopyWrites.updates (N := N) oldB srcB dstB sourceB hash initial := by
  apply CopyReadCapture.updates_eq_of_reads
  intro address member
  obtain ⟨q,inside,same⟩ := List.mem_map.mp member
  subst address
  exact read_frame oldA srcA dstA sourceA initial run (readSet srcB sourceB) writesCovered readsCovered separate
    (q.location sourceB) (List.mem_map.mpr ⟨q,inside,rfl⟩)

/-- Heterogeneous recursive copies commute as ACTUAL WordStore functions.
Both graph captures are fixed; only the current numeric source words are read.
Read/read sharing is unrestricted. No desired preservation relation is assumed. -/
theorem copy_copy {na nb N L R : Nat} {GA : Schema na} {GB : Schema nb}
    {A : TypeGraph.Ty na} {B : TypeGraph.Ty nb}
    (oldA srcA : Value GA A) (oldB srcB : Value GB B)
    (dstA sourceA dstB sourceB : Solidity.Storage.Loc) (initial : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (waCovered : ∀ a ∈ writeSet oldA srcA dstA, a ∈ locations)
    (wbCovered : ∀ b ∈ writeSet oldB srcB dstB, b ∈ locations)
    (raCovered : ∀ a ∈ readSet srcA sourceA, a ∈ locations)
    (rbCovered : ∀ b ∈ readSet srcB sourceB, b ∈ locations)
    (ab : ∀ a ∈ writeSet oldA srcA dstA, ∀ b ∈ writeSet oldB srcB dstB, a ≠ b)
    (aReadB : ∀ b ∈ writeSet oldB srcB dstB, ∀ a ∈ readSet srcA sourceA, b ≠ a)
    (bReadA : ∀ a ∈ writeSet oldA srcA dstA, ∀ b ∈ readSet srcB sourceB, a ≠ b) :
    CopyWrites.numericCopy (N := N) oldB srcB dstB sourceB hash
      (CopyWrites.numericCopy (N := N) oldA srcA dstA sourceA hash initial) =
    CopyWrites.numericCopy (N := N) oldA srcA dstA sourceA hash
      (CopyWrites.numericCopy (N := N) oldB srcB dstB sourceB hash initial) := by
  have stableB := source_stable oldA srcA oldB srcB dstA sourceA dstB sourceB initial run
    waCovered rbCovered bReadA
  have stableA := source_stable oldB srcB oldA srcA dstB sourceB dstA sourceA initial run
    wbCovered raCovered aReadB
  change (CopyWrites.updates (N := N) oldB srcB dstB sourceB hash
    (CopyWrites.numericCopy (N := N) oldA srcA dstA sourceA hash initial)).foldl _ _ =
    (CopyWrites.updates (N := N) oldA srcA dstA sourceA hash
      (CopyWrites.numericCopy (N := N) oldB srcB dstB sourceB hash initial)).foldl _ _
  rw [stableB,stableA]
  apply NumericCopyCommutation.write_logs_commute
  intro a aMember b bMember equal
  obtain ⟨qa,qaInside,qaSame⟩ := CopyWrites.generated oldA srcA dstA sourceA hash initial a aMember
  obtain ⟨qb,qbInside,qbSame⟩ := CopyWrites.generated oldB srcB dstB sourceB hash initial b bMember
  have qaMember : qa.location dstA ∈ writeSet oldA srcA dstA := List.mem_map.mpr ⟨qa,qaInside,rfl⟩
  have qbMember : qb.location dstB ∈ writeSet oldB srcB dstB := List.mem_map.mpr ⟨qb,qbInside,rfl⟩
  rw [qaSame,qbSame] at equal
  exact ab _ qaMember _ qbMember (run.word_inj (waCovered _ qaMember) (wbCovered _ qbMember) equal)

/-- The same actual commutation holds for finite materialized source capture. -/
theorem finite_copy_copy {na nb N L R : Nat} {GA : Schema na} {GB : Schema nb}
    {A : TypeGraph.Ty na} {B : TypeGraph.Ty nb}
    (oldA srcA : Value GA A) (oldB srcB : Value GB B)
    (dstA sourceA dstB sourceB : Solidity.Storage.Loc) (initial : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (waCovered : ∀ a ∈ writeSet oldA srcA dstA, a ∈ locations)
    (wbCovered : ∀ b ∈ writeSet oldB srcB dstB, b ∈ locations)
    (raCovered : ∀ a ∈ readSet srcA sourceA, a ∈ locations)
    (rbCovered : ∀ b ∈ readSet srcB sourceB, b ∈ locations)
    (ab : ∀ a ∈ writeSet oldA srcA dstA, ∀ b ∈ writeSet oldB srcB dstB, a ≠ b)
    (aReadB : ∀ b ∈ writeSet oldB srcB dstB, ∀ a ∈ readSet srcA sourceA, b ≠ a)
    (bReadA : ∀ a ∈ writeSet oldA srcA dstA, ∀ b ∈ readSet srcB sourceB, a ≠ b) :
    CopyReadCapture.finiteCopy (N := N) oldB srcB dstB sourceB hash
      (CopyReadCapture.finiteCopy (N := N) oldA srcA dstA sourceA hash initial) =
    CopyReadCapture.finiteCopy (N := N) oldA srcA dstA sourceA hash
      (CopyReadCapture.finiteCopy (N := N) oldB srcB dstB sourceB hash initial) := by
  simp only [CopyReadCapture.finiteCopy_eq]
  exact copy_copy oldA srcA oldB srcB dstA sourceA dstB sourceB initial run waCovered wbCovered raCovered rbCovered ab aReadB bReadA

/-- Ordered two-copy execution transports ACTUAL generated writes. Only the
first-write/second-read separation is needed; write/write overlap is allowed. -/
theorem sequence_transport {na nb N L R : Nat} {GA : Schema na} {GB : Schema nb}
    {A : TypeGraph.Ty na} {B : TypeGraph.Ty nb}
    (oldA srcA : Value GA A) (oldB srcB : Value GB B)
    (dstA sourceA dstB sourceB : Solidity.Storage.Loc) (store : Store) (initial : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations) (before : Transport N hash locations store initial)
    (waCovered : ∀ a ∈ writeSet oldA srcA dstA, a ∈ locations)
    (wbCovered : ∀ b ∈ writeSet oldB srcB dstB, b ∈ locations)
    (rbCovered : ∀ b ∈ readSet srcB sourceB, b ∈ locations)
    (bReadA : ∀ a ∈ writeSet oldA srcA dstA, ∀ b ∈ readSet srcB sourceB, a ≠ b) :
    let aLog := CopyWrites.updates (N := N) oldA srcA dstA sourceA hash initial
    let middle := CopyWrites.numericCopy (N := N) oldA srcA dstA sourceA hash initial
    let bLog := CopyWrites.updates (N := N) oldB srcB dstB sourceB hash middle
    Transport N hash locations
      (bLog.foldl (fun w op => write w op.1 op.2) (aLog.foldl (fun w op => write w op.1 op.2) store))
      (CopyWrites.numericCopy (N := N) oldB srcB dstB sourceB hash middle) := by
  have stable := source_stable oldA srcA oldB srcB dstA sourceA dstB sourceB initial run waCovered rbCovered bReadA
  have afterA := transport_sequence run before
    (CopyWrites.updates (N := N) oldA srcA dstA sourceA hash initial) (by
      intro op member
      obtain ⟨q,inside,same⟩ := CopyWrites.generated oldA srcA dstA sourceA hash initial op member
      rw [same]
      exact waCovered _ (List.mem_map.mpr ⟨q,inside,rfl⟩))
  apply transport_sequence run afterA
  intro op member
  rw [stable] at member
  obtain ⟨q,inside,same⟩ := CopyWrites.generated oldB srcB dstB sourceB hash initial op member
  rw [same]
  exact wbCovered _ (List.mem_map.mpr ⟨q,inside,rfl⟩)

/-- info: 'Solidity.Backend.StorageOps.RecursiveNumericCommutation.writeSet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms writeSet
/-- info: 'Solidity.Backend.StorageOps.RecursiveNumericCommutation.readSet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms readSet
/-- info: 'Solidity.Backend.StorageOps.RecursiveNumericCommutation.read_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms read_frame
/-- info: 'Solidity.Backend.StorageOps.RecursiveNumericCommutation.source_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_stable
/-- info: 'Solidity.Backend.StorageOps.RecursiveNumericCommutation.copy_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_copy
/-- info: 'Solidity.Backend.StorageOps.RecursiveNumericCommutation.finite_copy_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms finite_copy_copy
/-- info: 'Solidity.Backend.StorageOps.RecursiveNumericCommutation.sequence_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms sequence_transport

end Solidity.Backend.StorageOps.RecursiveNumericCommutation
