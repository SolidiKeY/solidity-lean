import Solidity.Backend.StorageOps.CopyTransport

/-! Actual current-header numeric copy read/write footprints and commutation.
Read/read sharing is permitted. The finite write log is the owner's existing
Loc×Word update interface, derived from the UNCHANGED runtime loop, not a new
source AST/IR/value/state or an independent specification defined by its target. -/
namespace Solidity.Backend.StorageOps.NumericCopyCommutation
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def readSet (N : Nat) (hash : Solidity.Storage.Pre → Nat) (dst src : Solidity.Storage.Loc) (initial : WordStore) :
    List Solidity.Storage.Loc :=
  [dst,src] ++ (List.range (LifecycleNumeric.headerLength N hash src initial)).map (Solidity.Storage.Loc.data src)

def writeSet (N : Nat) (hash : Solidity.Storage.Pre → Nat) (dst src : Solidity.Storage.Loc) (initial : WordStore) :
    List Solidity.Storage.Loc :=
  dst :: (List.range (max (LifecycleNumeric.headerLength N hash dst initial)
    (LifecycleNumeric.headerLength N hash src initial))).map (Solidity.Storage.Loc.data dst)

def touches (N : Nat) (hash : Solidity.Storage.Pre → Nat) (dst src : Solidity.Storage.Loc) (initial : WordStore) :
    List Solidity.Storage.Loc := readSet N hash dst src initial ++ writeSet N hash dst src initial

/-- Actual numeric reads determine payloads; this is a finite target write
certificate over the PUBLIC update API, not replacement source semantics. -/
def writeLog (N : Nat) (hash : Solidity.Storage.Pre → Nat) (dst src : Solidity.Storage.Loc) (initial : WordStore) :
    List (Solidity.Storage.Loc × Semantics.Word) :=
  let live := LifecycleNumeric.headerLength N hash src initial
  let count := max (LifecycleNumeric.headerLength N hash dst initial) live
  (List.range count).map (fun i => (.data dst i,
    if i < live then initial ((Solidity.Storage.Loc.data src i).word N hash) else ClearDemands.zero)) ++
      [(dst, initial (src.word N hash))]

private theorem prefix_fold (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (location : Nat → Solidity.Storage.Loc) (payload : Nat → Semantics.Word) (count : Nat) (initial : WordStore) :
    ((List.range count).map (fun i => (location i,payload i))).foldl
      (fun m op => writeWord m (op.1.word N hash) op.2) initial =
    NumericTraversal.writePrefix (fun i => (location i).word N hash) payload count initial := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [List.range_succ, List.map_append, List.map_singleton, List.foldl_append,
      List.foldl_cons, List.foldl_nil, NumericTraversal.writePrefix, ih]

/-- Equality to the ACTUAL loop is derived by its Nat recursion. The numeric
algorithm remains the independently implemented NumericTraversal.copy. -/
theorem copy_log (N : Nat) (hash : Solidity.Storage.Pre → Nat) (dst src : Solidity.Storage.Loc) (initial : WordStore) :
    NumericTraversal.copy N hash dst src initial =
      (writeLog N hash dst src initial).foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial := by
  simp only [writeLog, List.foldl_append, List.foldl_cons, List.foldl_nil, prefix_fold, NumericTraversal.copy]

theorem log_write_member (N : Nat) (hash : Solidity.Storage.Pre → Nat) (dst src : Solidity.Storage.Loc)
    (initial : WordStore) (op : Solidity.Storage.Loc × Semantics.Word) (inside : op ∈ writeLog N hash dst src initial) :
    op.1 ∈ writeSet N hash dst src initial := by
  simp only [writeLog, List.mem_append, List.mem_singleton] at inside
  rcases inside with element | rfl
  · obtain ⟨i,member,rfl⟩ := List.mem_map.mp element
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,member,rfl⟩)
  · exact List.mem_cons_self

/-- Agreement at every ACTUAL read derives both access sets and every write
payload. This is an operational noninterference proof, not a desired result
preservation hypothesis; the commutation theorem derives this agreement. -/
theorem reads_determine {N : Nat} (hash : Solidity.Storage.Pre → Nat) (dst src : Solidity.Storage.Loc)
    (before after : WordStore)
    (agree : ∀ l ∈ readSet N hash dst src before, after (l.word N hash) = before (l.word N hash)) :
    readSet N hash dst src after = readSet N hash dst src before ∧
      writeSet N hash dst src after = writeSet N hash dst src before ∧
      writeLog N hash dst src after = writeLog N hash dst src before := by
  have dstRead := agree dst (List.mem_append.mpr (Or.inl List.mem_cons_self))
  have srcRead := agree src (List.mem_append.mpr (Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)))
  have dstLength : LifecycleNumeric.headerLength N hash dst after = LifecycleNumeric.headerLength N hash dst before := by
    simp only [LifecycleNumeric.headerLength,dstRead]
  have srcLength : LifecycleNumeric.headerLength N hash src after = LifecycleNumeric.headerLength N hash src before := by
    simp only [LifecycleNumeric.headerLength,srcRead]
  refine ⟨?_,?_,?_⟩
  · simp only [readSet,srcLength]
  · simp only [writeSet,dstLength,srcLength]
  · dsimp only [writeLog]
    simp only [dstLength,srcLength,srcRead]
    apply congrArg (fun front => front ++ [(dst,before (src.word N hash))])
    apply List.map_congr_left
    intro i member
    by_cases live : i < LifecycleNumeric.headerLength N hash src before
    · have covered : Solidity.Storage.Loc.data src i ∈ readSet N hash dst src before :=
        List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨i,List.mem_range.mpr live,rfl⟩))
      simp only [if_pos live,agree _ covered]
    · simp only [if_neg live]

private theorem one_commute (m : WordStore) (a b : Nat) (va vb : Semantics.Word) (different : a ≠ b) :
    writeWord (writeWord m a va) b vb = writeWord (writeWord m b vb) a va := by
  funext k
  by_cases hitA : k = a
  · subst k
    simp only [writeWord,if_neg different,if_true]
  · by_cases hitB : k = b
    · subst k
      simp only [writeWord,if_neg hitA,if_true]
    · simp only [writeWord,if_neg hitA,if_neg hitB]

private theorem one_fold (N : Nat) (hash : Solidity.Storage.Pre → Nat) (updates : List (Solidity.Storage.Loc × Semantics.Word))
    (a : Solidity.Storage.Loc) (value : Semantics.Word) (initial : WordStore)
    (separate : ∀ op ∈ updates, a.word N hash ≠ op.1.word N hash) :
    updates.foldl (fun m op => writeWord m (op.1.word N hash) op.2) (writeWord initial (a.word N hash) value) =
      writeWord (updates.foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial) (a.word N hash) value := by
  induction updates generalizing initial with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.foldl_cons]
    rw [one_commute initial _ _ value op.2 (separate op List.mem_cons_self)]
    exact ih _ (fun next member => separate next (List.mem_cons_of_mem _ member))

/-- Finite PUBLIC write logs commute under physical cross-write separation. -/
theorem write_logs_commute (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (left right : List (Solidity.Storage.Loc × Semantics.Word)) (initial : WordStore)
    (separate : ∀ a ∈ left, ∀ b ∈ right, a.1.word N hash ≠ b.1.word N hash) :
    right.foldl (fun m op => writeWord m (op.1.word N hash) op.2)
      (left.foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial) =
    left.foldl (fun m op => writeWord m (op.1.word N hash) op.2)
      (right.foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial) := by
  induction left generalizing initial with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun next member => separate next (List.mem_cons_of_mem _ member))]
    rw [one_fold N hash right op.1 op.2 initial (separate op List.mem_cons_self)]

/-- Actual numeric copy frames arbitrary covered observers disjoint from
its generated WRITE set. Shared read-only source locations are not excluded. -/
theorem copy_frames {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (dst src : Solidity.Storage.Loc) (initial : WordStore)
    (observers : List Solidity.Storage.Loc)
    (covered : ∀ l ∈ writeSet N hash dst src initial ++ observers, l ∈ locations)
    (separate : ∀ w ∈ writeSet N hash dst src initial, ∀ r ∈ observers, w ≠ r) :
    ∀ r ∈ observers, NumericTraversal.copy N hash dst src initial (r.word N hash) = initial (r.word N hash) := by
  intro r observed
  rw [copy_log]
  apply sequence_outside_frame
  intro op member equal
  have written := log_write_member N hash dst src initial op member
  exact separate op.1 written r observed (run.word_inj
    (covered op.1 (List.mem_append.mpr (Or.inl written)))
    (covered r (List.mem_append.mpr (Or.inr observed))) equal.symm)

/-- Two ACTUAL current-header copies commute with separate write/write and
write/read conditions. Read/read overlaps are permitted, including one shared
source. No desired preservation/read-stability premise is assumed. -/
theorem copy_copy {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations)
    (aDst aSrc bDst bSrc : Solidity.Storage.Loc) (initial : WordStore)
    (covered : ∀ l ∈ touches N hash aDst aSrc initial ++ touches N hash bDst bSrc initial, l ∈ locations)
    (writeWrite : ∀ a ∈ writeSet N hash aDst aSrc initial, ∀ b ∈ writeSet N hash bDst bSrc initial, a ≠ b)
    (aWriteBRead : ∀ a ∈ writeSet N hash aDst aSrc initial, ∀ r ∈ readSet N hash bDst bSrc initial, a ≠ r)
    (bWriteARead : ∀ b ∈ writeSet N hash bDst bSrc initial, ∀ r ∈ readSet N hash aDst aSrc initial, b ≠ r) :
    NumericTraversal.copy N hash bDst bSrc (NumericTraversal.copy N hash aDst aSrc initial) =
      NumericTraversal.copy N hash aDst aSrc (NumericTraversal.copy N hash bDst bSrc initial) := by
  have raCovered : ∀ l ∈ readSet N hash aDst aSrc initial, l ∈ locations := by
    intro l member; exact covered l (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl member))))
  have waCovered : ∀ l ∈ writeSet N hash aDst aSrc initial, l ∈ locations := by
    intro l member; exact covered l (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr member))))
  have rbCovered : ∀ l ∈ readSet N hash bDst bSrc initial, l ∈ locations := by
    intro l member; exact covered l (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl member))))
  have wbCovered : ∀ l ∈ writeSet N hash bDst bSrc initial, l ∈ locations := by
    intro l member; exact covered l (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr member))))
  have frameB := copy_frames run aDst aSrc initial (readSet N hash bDst bSrc initial)
    (by intro l member; rcases List.mem_append.mp member with written | observed
        · exact waCovered l written
        · exact rbCovered l observed) aWriteBRead
  have frameA := copy_frames run bDst bSrc initial (readSet N hash aDst aSrc initial)
    (by intro l member; rcases List.mem_append.mp member with written | observed
        · exact wbCovered l written
        · exact raCovered l observed) bWriteARead
  have bLog := (reads_determine hash bDst bSrc initial (NumericTraversal.copy N hash aDst aSrc initial) frameB).2.2
  have aLog := (reads_determine hash aDst aSrc initial (NumericTraversal.copy N hash bDst bSrc initial) frameA).2.2
  calc
    NumericTraversal.copy N hash bDst bSrc (NumericTraversal.copy N hash aDst aSrc initial) =
        (writeLog N hash bDst bSrc initial).foldl (fun m op => writeWord m (op.1.word N hash) op.2)
          ((writeLog N hash aDst aSrc initial).foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial) := by
      rw [copy_log N hash bDst bSrc, bLog, copy_log N hash aDst aSrc]
    _ = (writeLog N hash aDst aSrc initial).foldl (fun m op => writeWord m (op.1.word N hash) op.2)
          ((writeLog N hash bDst bSrc initial).foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial) := by
      apply write_logs_commute
      intro a insideA b insideB same
      have wa := log_write_member N hash aDst aSrc initial a insideA
      have wb := log_write_member N hash bDst bSrc initial b insideB
      exact writeWrite a.1 wa b.1 wb (run.word_inj (waCovered a.1 wa) (wbCovered b.1 wb) same)
    _ = NumericTraversal.copy N hash aDst aSrc (NumericTraversal.copy N hash bDst bSrc initial) := by
      rw [copy_log N hash aDst aSrc, aLog, copy_log N hash bDst bSrc]

private theorem fold_original (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (updates : List (Solidity.Storage.Loc × Semantics.Word)) (initial : WordStore)
    (original : ∀ op ∈ updates, op.2 = initial (op.1.word N hash)) :
    updates.foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial = initial := by
  induction updates with
  | nil => rfl
  | cons op rest ih =>
    have one : writeWord initial (op.1.word N hash) op.2 = initial := by
      funext a
      by_cases equal : a = op.1.word N hash
      · simp only [writeWord,equal,if_true,original op List.mem_cons_self]
      · simp only [writeWord,if_neg equal]
    simp only [List.foldl_cons,one]
    exact ih (fun next member => original next (List.mem_cons_of_mem _ member))

/-- Exact alias identity for the ACTUAL numeric store, without assuming hash
separation. Every source read is the same physical destination word, so this
also holds when several symbolic locations alias. No source raw-metadata/world
identity is inferred from this numeric statement. -/
theorem copy_self (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (initial : WordStore) :
    NumericTraversal.copy N hash base base initial = initial := by
  rw [copy_log]
  apply fold_original
  intro op member
  simp only [writeLog,Nat.max_self,List.mem_append,List.mem_singleton] at member
  rcases member with element | rfl
  · obtain ⟨i,inside,rfl⟩ := List.mem_map.mp element
    simp only [if_pos (List.mem_range.mp inside)]
  · rfl

/-- Transport the actual generated numeric copy writes via the owner's
existing finite update API. This is a write certificate, NOT a definition of
Source evaluation; independent graph postrepresentation remains C20's theorem. -/
theorem generated_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (dst src : Solidity.Storage.Loc)
    (store : Store) (initial : WordStore) (before : Transport N hash locations store initial)
    (covered : ∀ l ∈ writeSet N hash dst src initial, l ∈ locations) :
    Transport N hash locations
      ((writeLog N hash dst src initial).foldl (fun w op => Representation.write w op.1 op.2) store)
      (NumericTraversal.copy N hash dst src initial) := by
  rw [copy_log]
  apply transport_sequence run before
  intro op member
  exact covered op.1 (log_write_member N hash dst src initial op member)

/-- A two-copy actual schedule transports its generated writes using ONLY
initial access coverage and the first-write/second-read condition. Read stability
and second access coverage are derived; write/write disjointness is unnecessary
for ordered execution (it is needed by commutation). -/
theorem sequence_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations)
    (aDst aSrc bDst bSrc : Solidity.Storage.Loc) (store : Store) (initial : WordStore)
    (before : Transport N hash locations store initial)
    (covered : ∀ l ∈ touches N hash aDst aSrc initial ++ touches N hash bDst bSrc initial, l ∈ locations)
    (aWriteBRead : ∀ a ∈ writeSet N hash aDst aSrc initial, ∀ r ∈ readSet N hash bDst bSrc initial, a ≠ r) :
    let middle := NumericTraversal.copy N hash aDst aSrc initial
    Transport N hash locations
      ((writeLog N hash bDst bSrc middle).foldl (fun w op => Representation.write w op.1 op.2)
        ((writeLog N hash aDst aSrc initial).foldl (fun w op => Representation.write w op.1 op.2) store))
      (NumericTraversal.copy N hash bDst bSrc middle) := by
  have waCovered : ∀ l ∈ writeSet N hash aDst aSrc initial, l ∈ locations := by
    intro l member; exact covered l (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr member))))
  have rbCovered : ∀ l ∈ readSet N hash bDst bSrc initial, l ∈ locations := by
    intro l member; exact covered l (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl member))))
  have wbCovered : ∀ l ∈ writeSet N hash bDst bSrc initial, l ∈ locations := by
    intro l member; exact covered l (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr member))))
  have frame := copy_frames run aDst aSrc initial (readSet N hash bDst bSrc initial)
    (by
      intro l member
      rcases List.mem_append.mp member with written | observed
      · exact waCovered l written
      · exact rbCovered l observed) aWriteBRead
  have stable := (reads_determine hash bDst bSrc initial (NumericTraversal.copy N hash aDst aSrc initial) frame).2.1
  exact generated_transport run bDst bSrc _ _
    (generated_transport run aDst aSrc store initial before waCovered)
    (by intro l member; exact wbCovered l (stable ▸ member))

/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutation.readSet' does not depend on any axioms -/
#guard_msgs in #print axioms readSet
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutation.writeSet' does not depend on any axioms -/
#guard_msgs in #print axioms writeSet
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutation.touches' does not depend on any axioms -/
#guard_msgs in #print axioms touches
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutation.writeLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms writeLog
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutation.copy_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_log
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutation.log_write_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms log_write_member
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutation.reads_determine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reads_determine
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutation.copy_frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_frames
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutation.copy_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_copy
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutation.copy_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_self
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutation.generated_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms generated_transport
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutation.sequence_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms sequence_transport

/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutation.write_logs_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms write_logs_commute

end Solidity.Backend.StorageOps.NumericCopyCommutation
