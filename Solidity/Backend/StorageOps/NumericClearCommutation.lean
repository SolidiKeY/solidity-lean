import Solidity.Backend.StorageOps.TargetClearRepresentation
import Solidity.Backend.StorageOps.NumericCopyCommutation

/-! Current-header numeric clears: generated finite write certificates,
disjoint commutation and transport over existing PUBLIC stores. No replacement
storage/representation/source semantics; physical separation is per-run only. -/
namespace Solidity.Backend.StorageOps.NumericClearCommutation
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def touches (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (initial : WordStore) : List Solidity.Storage.Loc :=
 base :: (List.range (LifecycleNumeric.headerLength N hash base initial)).map (Solidity.Storage.Loc.data base)

def writeLog (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (initial : WordStore) : List (Solidity.Storage.Loc × Semantics.Word) :=
 (List.range (LifecycleNumeric.headerLength N hash base initial)).map (fun i => (Solidity.Storage.Loc.data base i,ClearDemands.zero)) ++ [(base,ClearDemands.zero)]

private theorem prefix_fold (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (count : Nat) (initial : WordStore) :
 ((List.range count).map (fun i => (Solidity.Storage.Loc.data base i,ClearDemands.zero))).foldl
   (fun m op => writeWord m (op.1.word N hash) op.2) initial =
 TargetClearRepresentation.numericPrefix N hash initial base count := by
 induction count with
 | zero => rfl
 | succ count ih =>
   simp only [List.range_succ,List.map_append,List.map_singleton,List.foldl_append,
     List.foldl_cons,List.foldl_nil,TargetClearRepresentation.numericPrefix,ih]

/-- Finite certificate is derived from the actual runtime loop, not used as a
replacement definition of clear or of independent source observations. -/
theorem clear_log (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (initial : WordStore) :
 TargetClearRepresentation.execute N hash base initial =
 (writeLog N hash base initial).foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial := by
 simp only [writeLog,List.foldl_append,List.foldl_cons,List.foldl_nil,prefix_fold,TargetClearRepresentation.execute]

theorem log_touched (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (initial : WordStore)
 (op : Solidity.Storage.Loc × Semantics.Word) (member : op ∈ writeLog N hash base initial) :
 op.1 ∈ touches N hash base initial := by
 simp only [writeLog,List.mem_append,List.mem_map,List.mem_singleton] at member
 rcases member with ⟨i,inside,rfl⟩ | rfl
 · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,inside,rfl⟩)
 · exact List.mem_cons_self

/-- Arbitrary covered observers, including headers and unrepresented garbage.
The generated old live write set and per-run address relation derive frames. -/
theorem clear_frames {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash preimages locations) (base : Solidity.Storage.Loc) (initial : WordStore)
 (observers : List Solidity.Storage.Loc)
 (covered : ∀ l ∈ touches N hash base initial ++ observers, l ∈ locations)
 (separate : ∀ w ∈ touches N hash base initial, ∀ r ∈ observers, w ≠ r) :
 ∀ r ∈ observers, TargetClearRepresentation.execute N hash base initial (r.word N hash) = initial (r.word N hash) := by
 intro r observed
 have rCovered := covered r (List.mem_append.mpr (Or.inr observed))
 apply TargetClearRepresentation.numeric_outside
 · intro same
   exact separate base List.mem_cons_self r observed (run.word_inj
     (covered base (List.mem_append.mpr (Or.inl List.mem_cons_self))) rCovered same.symm)
 · intro j inside same
   have written : Solidity.Storage.Loc.data base j ∈ touches N hash base initial :=
     List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,List.mem_range.mpr inside,rfl⟩)
   exact separate (.data base j) written r observed (run.word_inj
     (covered _ (List.mem_append.mpr (Or.inl written))) rCovered same.symm)

/-- Two ACTUAL current-header clears commute when their generated OLD access
sets are disjoint under the existing per-run region premise. Header/log stability
is derived, not assumed. Full WordStore equality includes every outside word. -/
theorem clear_clear {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash preimages locations) (left right : Solidity.Storage.Loc) (initial : WordStore)
 (covered : ∀ l ∈ touches N hash left initial ++ touches N hash right initial, l ∈ locations)
 (separate : ∀ a ∈ touches N hash left initial, ∀ b ∈ touches N hash right initial, a ≠ b) :
 TargetClearRepresentation.execute N hash right (TargetClearRepresentation.execute N hash left initial) =
 TargetClearRepresentation.execute N hash left (TargetClearRepresentation.execute N hash right initial) := by
 have leftCovered : ∀ l ∈ touches N hash left initial, l ∈ locations := fun l member => covered l (List.mem_append.mpr (Or.inl member))
 have rightCovered : ∀ l ∈ touches N hash right initial, l ∈ locations := fun l member => covered l (List.mem_append.mpr (Or.inr member))
 have rightHeader := clear_frames run left initial [right]
   (by intro l member; rcases List.mem_append.mp member with written | observed
       · exact leftCovered l written
       · have same := List.mem_singleton.mp observed; subst l; exact rightCovered _ List.mem_cons_self)
   (by intro l member r observed; have same := List.mem_singleton.mp observed; subst r; exact separate l member right List.mem_cons_self)
   right List.mem_cons_self
 have leftHeader := clear_frames run right initial [left]
   (by intro l member; rcases List.mem_append.mp member with written | observed
       · exact rightCovered l written
       · have same := List.mem_singleton.mp observed; subst l; exact leftCovered _ List.mem_cons_self)
   (by intro l member r observed; have same := List.mem_singleton.mp observed; subst r; exact Ne.symm (separate left List.mem_cons_self l member))
   left List.mem_cons_self
 have rightLog : writeLog N hash right (TargetClearRepresentation.execute N hash left initial) = writeLog N hash right initial := by
   simp only [writeLog,LifecycleNumeric.headerLength,rightHeader]
 have leftLog : writeLog N hash left (TargetClearRepresentation.execute N hash right initial) = writeLog N hash left initial := by
   simp only [writeLog,LifecycleNumeric.headerLength,leftHeader]
 calc
  TargetClearRepresentation.execute N hash right (TargetClearRepresentation.execute N hash left initial) =
    (writeLog N hash right initial).foldl (fun m op => writeWord m (op.1.word N hash) op.2)
      ((writeLog N hash left initial).foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial) := by
    rw [clear_log N hash right,rightLog,clear_log N hash left]
  _ = (writeLog N hash left initial).foldl (fun m op => writeWord m (op.1.word N hash) op.2)
      ((writeLog N hash right initial).foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial) := by
    apply NumericCopyCommutation.write_logs_commute
    intro a insideA b insideB same
    have wa := log_touched N hash left initial a insideA
    have wb := log_touched N hash right initial b insideB
    exact separate a.1 wa b.1 wb (run.word_inj (leftCovered a.1 wa) (rightCovered b.1 wb) same)
  _ = TargetClearRepresentation.execute N hash left (TargetClearRepresentation.execute N hash right initial) := by
    rw [clear_log N hash left,leftLog,clear_log N hash right]

/-- Symbolic operation reads the CURRENT existing Store header, just as the
numeric operation does. This is a generated write adapter, not a source meaning. -/
def clearStore (base : Solidity.Storage.Loc) (store : Store) : Store :=
 Representation.write (TargetClearRepresentation.symbolicPrefix store base (store base).val.toNat) base ClearDemands.zero

/-- No graph postowner premise: the original PUBLIC Transport and each actual
current-header-generated access derive the complete output Transport. -/
theorem clear_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash preimages locations) (base : Solidity.Storage.Loc)
 (store : Store) (numeric : WordStore) (initial : Transport N hash locations store numeric)
 (baseCovered : base ∈ locations)
 (visited : ∀ j, j < (store base).val.toNat → Solidity.Storage.Loc.data base j ∈ locations) :
 Transport N hash locations (clearStore base store) (TargetClearRepresentation.execute N hash base numeric) := by
 have header : LifecycleNumeric.headerLength N hash base numeric = (store base).val.toNat := by
   simp only [LifecycleNumeric.headerLength,initial base baseCovered]
 have transportedPrefix := TargetClearRepresentation.prefix_numeric run store numeric base initial (store base).val.toNat visited
 have final := transport_write run transportedPrefix base baseCovered ClearDemands.zero
 unfold clearStore TargetClearRepresentation.execute
 rw [header]
 exact final

/-- Ordered current-header composition needs NO commutation/disjointness. The
second generated coverage is stated on its actual symbolic input after the first. -/
theorem sequence_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash preimages locations) (left right : Solidity.Storage.Loc)
 (store : Store) (numeric : WordStore) (initial : Transport N hash locations store numeric)
 (leftCovered : left ∈ locations) (rightCovered : right ∈ locations)
 (leftVisited : ∀ j, j < (store left).val.toNat → Solidity.Storage.Loc.data left j ∈ locations)
 (rightVisited : ∀ j, j < (clearStore left store right).val.toNat → Solidity.Storage.Loc.data right j ∈ locations) :
 Transport N hash locations (clearStore right (clearStore left store))
   (TargetClearRepresentation.execute N hash right (TargetClearRepresentation.execute N hash left numeric)) := by
 have middle := clear_transport run left store numeric initial leftCovered leftVisited
 exact clear_transport run right (clearStore left store) (TargetClearRepresentation.execute N hash left numeric) middle rightCovered rightVisited

/-- info: 'Solidity.Backend.StorageOps.NumericClearCommutation.clear_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_log
/-- info: 'Solidity.Backend.StorageOps.NumericClearCommutation.log_touched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms log_touched
/-- info: 'Solidity.Backend.StorageOps.NumericClearCommutation.clear_frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_frames
/-- info: 'Solidity.Backend.StorageOps.NumericClearCommutation.clear_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_clear
/-- info: 'Solidity.Backend.StorageOps.NumericClearCommutation.clear_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_transport
/-- info: 'Solidity.Backend.StorageOps.NumericClearCommutation.sequence_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms sequence_transport
end Solidity.Backend.StorageOps.NumericClearCommutation
