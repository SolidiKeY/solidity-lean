import Solidity.Backend.StorageOps.NumericCopyCommutation
import Solidity.Backend.StorageOps.NumericCommutation

/-! Actual copy/lifecycle noninterference. Current machine headers choose the
copy length and guarded lifecycle reset. All stability is derived from finite
run accesses; there is no assumed preservation theorem, new IR/value/state,
global hash premise or emitted/source/world claim. -/
namespace Solidity.Backend.StorageOps.CopyLifecycle
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

private theorem push_replay (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc)
    (before after : WordStore) (header : after (base.word N hash) = before (base.word N hash)) :
    LifecycleNumeric.pushPrimitive N hash base after =
      if LifecycleNumeric.headerLength N hash base before + 1 < 2 ^ 256 then
        some ((NumericCommutation.pushUpdates N hash base before).foldl
          (fun m op => writeWord m (op.1.word N hash) op.2) after) else none := by
  have sameLength : LifecycleNumeric.headerLength N hash base after = LifecycleNumeric.headerLength N hash base before := by
    simp only [LifecycleNumeric.headerLength,header]
  simp only [LifecycleNumeric.pushPrimitive,sameLength,NumericCommutation.pushUpdates]
  split <;> simp only [List.foldl_cons,List.foldl_nil]

/-- Copy followed by actual guarded push equals the reverse Option order.
Shared read/read is permitted on failure: no unexecuted reset is required.
The three conditions are write/header-read, write/write and lifecycle-write/
copy-read; actual log/header/read stability is DERIVED, not a premise. -/
theorem copy_push {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations)
    (dst src base : Solidity.Storage.Loc) (initial : WordStore)
    (covered : ∀ l ∈ NumericCopyCommutation.touches N hash dst src initial ++
      NumericCommutation.pushTouches N hash base initial, l ∈ locations)
    (writeHeader : ∀ w ∈ NumericCopyCommutation.writeSet N hash dst src initial, w ≠ base)
    (writeWrite : ∀ w ∈ NumericCopyCommutation.writeSet N hash dst src initial,
      ∀ op ∈ NumericCommutation.pushUpdates N hash base initial, w ≠ op.1)
    (lifeWriteRead : ∀ op ∈ NumericCommutation.pushUpdates N hash base initial,
      ∀ r ∈ NumericCopyCommutation.readSet N hash dst src initial, op.1 ≠ r) :
    LifecycleNumeric.pushPrimitive N hash base (NumericTraversal.copy N hash dst src initial) =
      (LifecycleNumeric.pushPrimitive N hash base initial).map (NumericTraversal.copy N hash dst src) := by
  have readCovered : ∀ l ∈ NumericCopyCommutation.readSet N hash dst src initial, l ∈ locations := by
    intro l member
    exact covered l (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl member))))
  have writeCovered : ∀ l ∈ NumericCopyCommutation.writeSet N hash dst src initial, l ∈ locations := by
    intro l member
    exact covered l (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr member))))
  have lifeCovered : ∀ op ∈ NumericCommutation.pushUpdates N hash base initial, op.1 ∈ locations := by
    intro op member
    exact covered op.1 (List.mem_append.mpr (Or.inr (NumericCommutation.update_touched N hash base initial op member)))
  have headerMember : base ∈ NumericCommutation.pushTouches N hash base initial := by
    dsimp only [NumericCommutation.pushTouches]
    split <;> exact List.mem_cons_self
  have headerCovered := covered base (List.mem_append.mpr (Or.inr headerMember))
  have headerFrame : NumericTraversal.copy N hash dst src initial (base.word N hash) = initial (base.word N hash) := by
    apply NumericCopyCommutation.copy_frames run dst src initial [base]
    · intro l member
      rcases List.mem_append.mp member with written | observed
      · exact writeCovered l written
      · simp only [List.mem_singleton] at observed
        subst l
        exact headerCovered
    · intro w written r observed
      simp only [List.mem_singleton] at observed
      subst r
      exact writeHeader w written
    · exact List.mem_cons_self
  rw [push_replay N hash base initial _ headerFrame,
      push_replay N hash base initial initial rfl]
  split
  next branch =>
    simp only [Option.map_some]
    apply congrArg some
    let middle := (NumericCommutation.pushUpdates N hash base initial).foldl
      (fun m op => writeWord m (op.1.word N hash) op.2) initial
    have lifeFrame : ∀ r ∈ NumericCopyCommutation.readSet N hash dst src initial,
        middle (r.word N hash) = initial (r.word N hash) := by
      intro r observed
      apply sequence_outside_frame
      intro op member equal
      exact lifeWriteRead op member r observed
        (run.word_inj (lifeCovered op member) (readCovered r observed) equal.symm)
    have stable := (NumericCopyCommutation.reads_determine hash dst src initial middle lifeFrame).2.2
    rw [NumericCopyCommutation.copy_log N hash dst src middle,stable,
      NumericCopyCommutation.copy_log N hash dst src initial]
    apply NumericCopyCommutation.write_logs_commute
    intro op member other memberOther equal
    have written := NumericCopyCommutation.log_write_member N hash dst src initial op member
    exact writeWrite op.1 written other memberOther
      (run.word_inj (writeCovered op.1 written) (lifeCovered other memberOther) equal)
  next failed => rfl


private theorem pop_replay (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc)
    (before after : WordStore) (header : after (base.word N hash) = before (base.word N hash)) :
    PrimitivePop.execute N hash base after =
      if 0 < LifecycleNumeric.headerLength N hash base before then
        some ((NumericCommutation.popUpdates N hash base before).foldl
          (fun m op => writeWord m (op.1.word N hash) op.2) after) else none := by
  have sameLength : LifecycleNumeric.headerLength N hash base after = LifecycleNumeric.headerLength N hash base before := by
    simp only [LifecycleNumeric.headerLength,header]
  simp only [PrimitivePop.execute,sameLength,NumericCommutation.popUpdates]
  split <;> simp only [List.foldl_cons,List.foldl_nil]

/-- Copy followed by actual guarded pop equals the reverse Option order.
Shared read/read is permitted on failure: no unexecuted reset is required.
The three conditions are write/header-read, write/write and lifecycle-write/
copy-read; actual log/header/read stability is DERIVED, not a premise. -/
theorem copy_pop {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations)
    (dst src base : Solidity.Storage.Loc) (initial : WordStore)
    (covered : ∀ l ∈ NumericCopyCommutation.touches N hash dst src initial ++
      NumericCommutation.popTouches N hash base initial, l ∈ locations)
    (writeHeader : ∀ w ∈ NumericCopyCommutation.writeSet N hash dst src initial, w ≠ base)
    (writeWrite : ∀ w ∈ NumericCopyCommutation.writeSet N hash dst src initial,
      ∀ op ∈ NumericCommutation.popUpdates N hash base initial, w ≠ op.1)
    (lifeWriteRead : ∀ op ∈ NumericCommutation.popUpdates N hash base initial,
      ∀ r ∈ NumericCopyCommutation.readSet N hash dst src initial, op.1 ≠ r) :
    PrimitivePop.execute N hash base (NumericTraversal.copy N hash dst src initial) =
      (PrimitivePop.execute N hash base initial).map (NumericTraversal.copy N hash dst src) := by
  have readCovered : ∀ l ∈ NumericCopyCommutation.readSet N hash dst src initial, l ∈ locations := by
    intro l member
    exact covered l (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl member))))
  have writeCovered : ∀ l ∈ NumericCopyCommutation.writeSet N hash dst src initial, l ∈ locations := by
    intro l member
    exact covered l (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr member))))
  have lifeCovered : ∀ op ∈ NumericCommutation.popUpdates N hash base initial, op.1 ∈ locations := by
    intro op member
    exact covered op.1 (List.mem_append.mpr (Or.inr (NumericCommutation.pop_update_touched N hash base initial op member)))
  have headerMember : base ∈ NumericCommutation.popTouches N hash base initial := by
    dsimp only [NumericCommutation.popTouches]
    split <;> exact List.mem_cons_self
  have headerCovered := covered base (List.mem_append.mpr (Or.inr headerMember))
  have headerFrame : NumericTraversal.copy N hash dst src initial (base.word N hash) = initial (base.word N hash) := by
    apply NumericCopyCommutation.copy_frames run dst src initial [base]
    · intro l member
      rcases List.mem_append.mp member with written | observed
      · exact writeCovered l written
      · simp only [List.mem_singleton] at observed
        subst l
        exact headerCovered
    · intro w written r observed
      simp only [List.mem_singleton] at observed
      subst r
      exact writeHeader w written
    · exact List.mem_cons_self
  rw [pop_replay N hash base initial _ headerFrame,
      pop_replay N hash base initial initial rfl]
  split
  next branch =>
    simp only [Option.map_some]
    apply congrArg some
    let middle := (NumericCommutation.popUpdates N hash base initial).foldl
      (fun m op => writeWord m (op.1.word N hash) op.2) initial
    have lifeFrame : ∀ r ∈ NumericCopyCommutation.readSet N hash dst src initial,
        middle (r.word N hash) = initial (r.word N hash) := by
      intro r observed
      apply sequence_outside_frame
      intro op member equal
      exact lifeWriteRead op member r observed
        (run.word_inj (lifeCovered op member) (readCovered r observed) equal.symm)
    have stable := (NumericCopyCommutation.reads_determine hash dst src initial middle lifeFrame).2.2
    rw [NumericCopyCommutation.copy_log N hash dst src middle,stable,
      NumericCopyCommutation.copy_log N hash dst src initial]
    apply NumericCopyCommutation.write_logs_commute
    intro op member other memberOther equal
    have written := NumericCopyCommutation.log_write_member N hash dst src initial op member
    exact writeWrite op.1 written other memberOther
      (run.word_inj (writeCovered op.1 written) (lifeCovered other memberOther) equal)
  next failed => rfl

/-- Ordered actual copy/push transport derives the second access coverage
from INITIAL actual touches and the copy/header frame. No cross-write or reverse
read-separation is needed for this ordered execution theorem. -/
theorem copy_push_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations)
    (dst src base : Solidity.Storage.Loc) (store : Store) (initial final : WordStore)
    (before : Transport N hash locations store initial)
    (success : LifecycleNumeric.pushPrimitive N hash base (NumericTraversal.copy N hash dst src initial) = some final)
    (covered : ∀ l ∈ NumericCopyCommutation.touches N hash dst src initial ++
      NumericCommutation.pushTouches N hash base initial, l ∈ locations)
    (writeHeader : ∀ w ∈ NumericCopyCommutation.writeSet N hash dst src initial, w ≠ base) :
    Transport N hash locations
      ((NumericCommutation.pushUpdates N hash base (NumericTraversal.copy N hash dst src initial)).foldl
        (fun w op => Representation.write w op.1 op.2)
        ((NumericCopyCommutation.writeLog N hash dst src initial).foldl
          (fun w op => Representation.write w op.1 op.2) store)) final := by
  have writeCovered : ∀ l ∈ NumericCopyCommutation.writeSet N hash dst src initial, l ∈ locations := by
    intro l member
    exact covered l (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr member))))
  have headerMember : base ∈ NumericCommutation.pushTouches N hash base initial := by
    dsimp only [NumericCommutation.pushTouches]
    split <;> exact List.mem_cons_self
  have headerFrame : NumericTraversal.copy N hash dst src initial (base.word N hash) = initial (base.word N hash) := by
    apply NumericCopyCommutation.copy_frames run dst src initial [base]
    · intro l member
      rcases List.mem_append.mp member with written | observed
      · exact writeCovered l written
      · simp only [List.mem_singleton] at observed
        subst l
        exact covered base (List.mem_append.mpr (Or.inr headerMember))
    · intro w written r observed
      simp only [List.mem_singleton] at observed
      subst r
      exact writeHeader w written
    · exact List.mem_cons_self
  have lengthEq : LifecycleNumeric.headerLength N hash base (NumericTraversal.copy N hash dst src initial) =
      LifecycleNumeric.headerLength N hash base initial := by simp only [LifecycleNumeric.headerLength,headerFrame]
  have touchesEq : NumericCommutation.pushTouches N hash base (NumericTraversal.copy N hash dst src initial) =
      NumericCommutation.pushTouches N hash base initial := by simp only [NumericCommutation.pushTouches,lengthEq]
  exact NumericCommutation.push_transport run base _ _ final
    (NumericCopyCommutation.generated_transport run dst src store initial before writeCovered) success
    (by
      intro l member
      rw [touchesEq] at member
      exact covered l (List.mem_append.mpr (Or.inr member)))

/-- Ordered actual copy/pop transport derives the second access coverage
from INITIAL actual touches and the copy/header frame. No cross-write or reverse
read-separation is needed for this ordered execution theorem. -/
theorem copy_pop_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations)
    (dst src base : Solidity.Storage.Loc) (store : Store) (initial final : WordStore)
    (before : Transport N hash locations store initial)
    (success : PrimitivePop.execute N hash base (NumericTraversal.copy N hash dst src initial) = some final)
    (covered : ∀ l ∈ NumericCopyCommutation.touches N hash dst src initial ++
      NumericCommutation.popTouches N hash base initial, l ∈ locations)
    (writeHeader : ∀ w ∈ NumericCopyCommutation.writeSet N hash dst src initial, w ≠ base) :
    Transport N hash locations
      ((NumericCommutation.popUpdates N hash base (NumericTraversal.copy N hash dst src initial)).foldl
        (fun w op => Representation.write w op.1 op.2)
        ((NumericCopyCommutation.writeLog N hash dst src initial).foldl
          (fun w op => Representation.write w op.1 op.2) store)) final := by
  have writeCovered : ∀ l ∈ NumericCopyCommutation.writeSet N hash dst src initial, l ∈ locations := by
    intro l member
    exact covered l (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr member))))
  have headerMember : base ∈ NumericCommutation.popTouches N hash base initial := by
    dsimp only [NumericCommutation.popTouches]
    split <;> exact List.mem_cons_self
  have headerFrame : NumericTraversal.copy N hash dst src initial (base.word N hash) = initial (base.word N hash) := by
    apply NumericCopyCommutation.copy_frames run dst src initial [base]
    · intro l member
      rcases List.mem_append.mp member with written | observed
      · exact writeCovered l written
      · simp only [List.mem_singleton] at observed
        subst l
        exact covered base (List.mem_append.mpr (Or.inr headerMember))
    · intro w written r observed
      simp only [List.mem_singleton] at observed
      subst r
      exact writeHeader w written
    · exact List.mem_cons_self
  have lengthEq : LifecycleNumeric.headerLength N hash base (NumericTraversal.copy N hash dst src initial) =
      LifecycleNumeric.headerLength N hash base initial := by simp only [LifecycleNumeric.headerLength,headerFrame]
  have touchesEq : NumericCommutation.popTouches N hash base (NumericTraversal.copy N hash dst src initial) =
      NumericCommutation.popTouches N hash base initial := by simp only [NumericCommutation.popTouches,lengthEq]
  exact NumericCommutation.pop_transport run base _ _ final
    (NumericCopyCommutation.generated_transport run dst src store initial before writeCovered) success
    (by
      intro l member
      rw [touchesEq] at member
      exact covered l (List.mem_append.mpr (Or.inr member)))

/-- info: 'Solidity.Backend.StorageOps.CopyLifecycle.copy_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_push
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycle.copy_pop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_pop
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycle.copy_push_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_push_transport
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycle.copy_pop_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_pop_transport

end Solidity.Backend.StorageOps.CopyLifecycle
