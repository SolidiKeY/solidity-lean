import Solidity.Backend.StorageOps.TargetRetainedCycle

/-! Actual numeric retained-child lifecycle cycles over the PUBLIC WordStore.
The finite run below covers actual generated pop accesses; no global hash
injectivity, new representation or Source/world evaluator is introduced. -/
namespace Solidity.Backend.StorageOps.NumericRetainedCycle
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def reuse (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc)
 (numeric : WordStore) : Option WordStore := do
 let grown ← LifecycleNumeric.pushHeader N hash base numeric
 NestedPopTransport.execute N hash base grown

def popRegrowPop (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc)
 (numeric : WordStore) : Option WordStore := do
 let popped ← NestedPopTransport.execute N hash base numeric
 reuse N hash base popped

private theorem header_bound (N : Nat) (hash : Solidity.Storage.Pre → Nat)
 (base : Solidity.Storage.Loc) (numeric : WordStore) :
 LifecycleNumeric.headerLength N hash base numeric < 2^256 := by
 have bound := (numeric (base.word N hash)).property
 simp only [PrimTy.inRange,decide_eq_true_eq] at bound
 unfold LifecycleNumeric.headerLength
 omega

private theorem header_word (N : Nat) (hash : Solidity.Storage.Pre → Nat)
 (base : Solidity.Storage.Loc) (numeric : WordStore)
 (bound : LifecycleNumeric.headerLength N hash base numeric < 2^256) :
 lengthWord (LifecycleNumeric.headerLength N hash base numeric) bound = numeric (base.word N hash) := by
 apply Subtype.ext
 change Int.ofNat (numeric (base.word N hash)).val.toNat = (numeric (base.word N hash)).val
 exact Int.toNat_of_nonneg (PrimTy.uint_nonneg (numeric (base.word N hash)))

private theorem write_back (numeric : WordStore) (address : Nat) :
 writeWord numeric address (numeric address) = numeric := by
 funext observer
 by_cases same : observer = address
 · subst observer; simp only [writeWord,if_true]
 · exact if_neg same

/-- An actual empty-header numeric clear leaves EVERY physical word unchanged,
including dirty retained data; no region premise is needed for this identity. -/
theorem clear_empty (N : Nat) (hash : Solidity.Storage.Pre → Nat)
 (base : Solidity.Storage.Loc) (numeric : WordStore)
 (empty : numeric (base.word N hash) = ClearDemands.zero) :
 TargetClearRepresentation.execute N hash base numeric = numeric := by
 have header : LifecycleNumeric.headerLength N hash base numeric = 0 := by
  unfold LifecycleNumeric.headerLength
  rw [empty]
  rfl
 unfold TargetClearRepresentation.execute
 rw [header,TargetClearRepresentation.numericPrefix,← empty,write_back]

/-- Actual push then nested pop restores the ENTIRE numeric store when its
reused child header is empty. Header restoration precedes child clear, so this
raw operation identity itself requires no hash injectivity or tail-zero premise. -/
theorem reuse_identity (N : Nat) (hash : Solidity.Storage.Pre → Nat)
 (base : Solidity.Storage.Loc) (numeric : WordStore)
 (room : LifecycleNumeric.headerLength N hash base numeric + 1 < 2^256)
 (empty : numeric ((Solidity.Storage.Loc.data base (LifecycleNumeric.headerLength N hash base numeric)).word N hash) = ClearDemands.zero) :
 reuse N hash base numeric = some numeric := by
 let length := LifecycleNumeric.headerLength N hash base numeric
 let grown := writeWord numeric (base.word N hash) (lengthWord (length+1) room)
 have header : LifecycleNumeric.headerLength N hash base grown = length+1 :=
  LifecycleNumeric.headerLength_known hash base grown ⟨length+1,room⟩ (by simp only [grown,writeWord,if_true])
 have restored : writeWord grown (base.word N hash) (lengthWord length (header_bound N hash base numeric)) = numeric := by
  rw [header_word N hash base numeric]
  funext observer
  by_cases same : observer = base.word N hash
  · subst observer; simp only [writeWord,if_true]
  · simp only [writeWord,if_neg same,grown]
 unfold reuse LifecycleNumeric.pushHeader
 rw [dif_pos room]
 change NestedPopTransport.execute N hash base grown = some numeric
 simp only [NestedPopTransport.execute,header,Nat.add_sub_cancel,dif_pos (by omega : 0 < length+1)]
 rw [restored,clear_empty N hash _ numeric empty]

/-- Capacity failure is exact Option failure before any numeric pop. -/
theorem capacity_failure (N : Nat) (hash : Solidity.Storage.Pre → Nat)
 (base : Solidity.Storage.Loc) (numeric : WordStore)
 (full : ¬ LifecycleNumeric.headerLength N hash base numeric + 1 < 2^256) :
 reuse N hash base numeric = none := by
 unfold reuse LifecycleNumeric.pushHeader
 rw [dif_neg full]
 rfl

/-- Derive actual post-pop root and selected-child words from the ORIGINAL
finite run and coverage of every generated access. No post-frame is assumed. -/
theorem popped_headers {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (base : Solidity.Storage.Loc)
 (numeric result : WordStore)
 (performed : NestedPopTransport.execute N hash base numeric = some result)
 (rootCovered : base ∈ locations)
 (childCovered : Solidity.Storage.Loc.data base (LifecycleNumeric.headerLength N hash base numeric-1) ∈ locations)
 (visited : ∀ j, j < LifecycleNumeric.headerLength N hash
   (.data base (LifecycleNumeric.headerLength N hash base numeric-1))
   (writeWord numeric (base.word N hash) (lengthWord (LifecycleNumeric.headerLength N hash base numeric-1) (by have bound := header_bound N hash base numeric; omega))) →
   Solidity.Storage.Loc.data (.data base (LifecycleNumeric.headerLength N hash base numeric-1)) j ∈ locations) :
 result (base.word N hash) = lengthWord (LifecycleNumeric.headerLength N hash base numeric-1) (by have bound := header_bound N hash base numeric; omega) ∧
 result ((Solidity.Storage.Loc.data base (LifecycleNumeric.headerLength N hash base numeric-1)).word N hash) = ClearDemands.zero := by
 unfold NestedPopTransport.execute at performed
 dsimp only at performed
 split at performed
 · cases performed
   constructor
   · rw [TargetClearRepresentation.numeric_outside]
     · simp only [writeWord,if_true]
     · intro same
       have equality := run.word_inj rootCovered childCovered same
       have depth := congrArg Solidity.Storage.Loc.depth equality
       change base.depth = base.depth+1 at depth
       omega
     · intro j live same
       have equality := run.word_inj rootCovered (visited j live) same
       have depth := congrArg Solidity.Storage.Loc.depth equality
       change base.depth = base.depth+1+1 at depth
       omega
   · simp only [TargetClearRepresentation.execute,writeWord,if_true]
 · cases performed

/-- The finite-run pop proof DERIVES both room and reused-zero for the actual
numeric sequence. Hash/address premises remain explicit at this composition. -/
theorem after_pop {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (base : Solidity.Storage.Loc)
 (numeric result : WordStore)
 (performed : NestedPopTransport.execute N hash base numeric = some result)
 (rootCovered : base ∈ locations)
 (childCovered : Solidity.Storage.Loc.data base (LifecycleNumeric.headerLength N hash base numeric-1) ∈ locations)
 (visited : ∀ j, j < LifecycleNumeric.headerLength N hash
   (.data base (LifecycleNumeric.headerLength N hash base numeric-1))
   (writeWord numeric (base.word N hash) (lengthWord (LifecycleNumeric.headerLength N hash base numeric-1) (by have bound := header_bound N hash base numeric; omega))) →
   Solidity.Storage.Loc.data (.data base (LifecycleNumeric.headerLength N hash base numeric-1)) j ∈ locations) :
 popRegrowPop N hash base numeric = some result := by
 have headers := popped_headers run base numeric result performed rootCovered childCovered visited
 have length : LifecycleNumeric.headerLength N hash base result = LifecycleNumeric.headerLength N hash base numeric-1 := by
  unfold LifecycleNumeric.headerLength
  rw [headers.1]
  rfl
 have live : 0 < LifecycleNumeric.headerLength N hash base numeric := by
  unfold NestedPopTransport.execute at performed
  dsimp only at performed
  split at performed
  · assumption
  · cases performed
 have room : LifecycleNumeric.headerLength N hash base result + 1 < 2^256 := by
  rw [length]
  have bound := header_bound N hash base numeric
  omega
 have empty : result ((Solidity.Storage.Loc.data base (LifecycleNumeric.headerLength N hash base result)).word N hash) = ClearDemands.zero := by
  rw [length]
  exact headers.2
 unfold popRegrowPop
 rw [performed]
 exact reuse_identity N hash base result room empty

/-- info: 'Solidity.Backend.StorageOps.NumericRetainedCycle.clear_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_empty
/-- info: 'Solidity.Backend.StorageOps.NumericRetainedCycle.reuse_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reuse_identity
/-- info: 'Solidity.Backend.StorageOps.NumericRetainedCycle.capacity_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms capacity_failure
/-- info: 'Solidity.Backend.StorageOps.NumericRetainedCycle.popped_headers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms popped_headers
/-- info: 'Solidity.Backend.StorageOps.NumericRetainedCycle.after_pop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms after_pop

/-- BOTH exact Option outcomes equal the first actual pop under the original
finite generated-access premise; no successful-pop assumption remains. -/
theorem outcome {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (base : Solidity.Storage.Loc)
 (numeric : WordStore)
 (rootCovered : base ∈ locations)
 (childCovered : Solidity.Storage.Loc.data base (LifecycleNumeric.headerLength N hash base numeric-1) ∈ locations)
 (visited : ∀ j, j < LifecycleNumeric.headerLength N hash
   (.data base (LifecycleNumeric.headerLength N hash base numeric-1))
   (writeWord numeric (base.word N hash) (lengthWord (LifecycleNumeric.headerLength N hash base numeric-1) (by have bound := header_bound N hash base numeric; omega))) →
   Solidity.Storage.Loc.data (.data base (LifecycleNumeric.headerLength N hash base numeric-1)) j ∈ locations) :
 popRegrowPop N hash base numeric = NestedPopTransport.execute N hash base numeric := by
 cases performed : NestedPopTransport.execute N hash base numeric with
 | none =>
   unfold popRegrowPop
   rw [performed]
   rfl
 | some result => exact after_pop run base numeric result performed rootCovered childCovered visited

/-- info: 'Solidity.Backend.StorageOps.NumericRetainedCycle.outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms outcome
/-- Plain OLD target/numeric cell observations derive the target runtime
premises; both ACTUAL cycle programs then restore their entire respective input.
No output relation or desired target preservation is an input premise. -/
theorem paired_reuse (N : Nat) (hash : Solidity.Storage.Pre → Nat)
 (base : Solidity.Storage.Loc) (numeric : WordStore) (target : Evm.Machine)
 (fits : TargetOperations.KeysFit base)
 (room : LifecycleNumeric.headerLength N hash base numeric + 1 < 2^256)
 (empty : numeric ((Solidity.Storage.Loc.data base (LifecycleNumeric.headerLength N hash base numeric)).word N hash) = ClearDemands.zero)
 (rootAgreement : target.store.cells (TargetOperations.toSlot base fits) =
   TargetOperations.encodeWord (numeric (base.word N hash)))
 (childAgreement : target.store.cells
   (TargetOperations.toSlot (.data base (LifecycleNumeric.headerLength N hash base numeric)) fits) =
   TargetOperations.encodeWord (numeric ((Solidity.Storage.Loc.data base (LifecycleNumeric.headerLength N hash base numeric)).word N hash))) :
 reuse N hash base numeric = some numeric ∧
 Evm.run (TargetRetainedCycle.code (TargetOperations.toSlot base fits)) target = .ok target 0 := by
 have header : target.store (TargetOperations.toSlot base fits) = LifecycleNumeric.headerLength N hash base numeric :=
  congrArg Fin.val rootAgreement
 have child : target.store (.data (TargetOperations.toSlot base fits) (LifecycleNumeric.headerLength N hash base numeric)) = 0 := by
  have observed := congrArg Fin.val childAgreement
  rw [empty] at observed
  exact observed
 refine ⟨reuse_identity N hash base numeric room empty,TargetRetainedCycle.run_reuse target _ ?_ ?_⟩
 · change target.store (TargetOperations.toSlot base fits)+1 < 2^256
   rw [header]
   exact room
 · rw [header]
   exact child

/-- info: 'Solidity.Backend.StorageOps.NumericRetainedCycle.paired_reuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms paired_reuse
end Solidity.Backend.StorageOps.NumericRetainedCycle
