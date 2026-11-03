import Solidity.Backend.StorageOps.CopyDefaults
import Solidity.Backend.StorageOps.TargetOperations

/-! Actual Evm.Instr realization of EXISTING typed default-initialization
updates. No source value is supplied as a target payload oracle: default code
uses schema-directed existing zero updates only. Captured-location/CopyPermit
boundaries do not establish runtime allocation, Source lowering or world closure. -/
namespace Solidity.Backend.StorageOps.TargetDefaultInit
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Compile an existing concrete update sequence with existing SSTORE code.
The pair-list is CopyDefaults.updates, not a new operation AST/state/IR. -/
def writeProgram : (updates : List (Solidity.Storage.Loc × Semantics.Word)) →
 (∀ op ∈ updates, TargetOperations.KeysFit op.1) → List Evm.Instr
 | [], _ => []
 | op::rest, fits => TargetOperations.writeCode (TargetOperations.toSlot op.1 (fits op List.mem_cons_self)) op.2 ++
   writeProgram rest (fun next member => fits next (List.mem_cons_of_mem _ member))

def afterWrites : (updates : List (Solidity.Storage.Loc × Semantics.Word)) →
 (∀ op ∈ updates, TargetOperations.KeysFit op.1) → Evm.Machine → Evm.Machine
 | [], _, machine => machine
 | op::rest, fits, machine =>
   afterWrites rest (fun next member => fits next (List.mem_cons_of_mem _ member))
    {machine with store := Evm.WordStore.write machine.store (TargetOperations.toSlot op.1 (fits op List.mem_cons_self)) (TargetOperations.encodeWord op.2).val}

/-- Whole-Machine execution of ACTUAL generated instructions. -/
theorem run_writes (updates : List (Solidity.Storage.Loc × Semantics.Word))
 (fits : ∀ op ∈ updates, TargetOperations.KeysFit op.1) (machine : Evm.Machine) :
 Evm.run (writeProgram updates fits) machine=.ok (afterWrites updates fits machine) 0 := by
 revert fits
 induction updates generalizing machine with
 | nil => intro fits; rfl
 | cons op rest ih =>
   intro fits
   rw [writeProgram,Evm.run_append_ok (TargetOperations.run_write _ _ machine)]
   exact ih _ _

/-- Complete non-store context survives the ACTUAL write sequence. -/
theorem context_writes (updates : List (Solidity.Storage.Loc × Semantics.Word))
 (fits : ∀ op ∈ updates, TargetOperations.KeysFit op.1) (machine : Evm.Machine) :
 {afterWrites updates fits machine with store := machine.store}=machine := by
 revert fits
 induction updates generalizing machine with
 | nil => intro fits; rfl
 | cons op rest ih =>
   intro fits
   exact congrArg (fun m : Evm.Machine => {m with store := machine.store}) (ih _ _)

/-- OLD covered cell agreement is transported through every actual SSTORE,
not assumed as a desired final state relation. -/
theorem agreement_writes (updates : List (Solidity.Storage.Loc × Semantics.Word))
 (fits : ∀ op ∈ updates, TargetOperations.KeysFit op.1)
 (captured : Store) (machine : Evm.Machine) (locations : List Solidity.Storage.Loc)
 (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
 (before : ∀ l (member : l ∈ locations), machine.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (captured l)) :
 ∀ l (member : l ∈ locations), (afterWrites updates fits machine).store.cells (TargetOperations.toSlot l (fitting l member))=
 TargetOperations.encodeWord ((updates.foldl (fun store op => Representation.write store op.1 op.2) captured) l) := by
 revert fits
 induction updates generalizing captured machine with
 | nil => intro fits; exact before
 | cons op rest ih =>
   intro fits
   exact ih _ _ (TargetOperations.write_agreement locations fitting op.1 (fits op List.mem_cons_self) op.2 captured machine before) _

/-- Every non-generated symbolic target slot frames, including dirty tails. -/
theorem outside_writes (updates : List (Solidity.Storage.Loc × Semantics.Word))
 (fits : ∀ op ∈ updates, TargetOperations.KeysFit op.1) (machine : Evm.Machine) (observer : Evm.Slot)
 (apart : ∀ op (member : op ∈ updates), observer ≠ TargetOperations.toSlot op.1 (fits op member)) :
 (afterWrites updates fits machine).store observer=machine.store observer := by
 revert fits
 induction updates generalizing machine with
 | nil => intro fits apart; rfl
 | cons op rest ih =>
   intro fits apart
   exact (ih _ _ (fun next member => apart next (List.mem_cons_of_mem _ member))).trans
    (Evm.WordStore.write_other machine.store _ (apart op List.mem_cons_self))

/-- Every generated typed query location fits from the captured base alone;
no new index/key profile predicate is introduced. -/
theorem updates_fit {n : Nat} (G : Schema n) (T : TypeGraph.Ty n)
 (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base) :
 ∀ op ∈ CopyDefaults.updates G T base, TargetOperations.KeysFit op.1 := by
 intro op member
 obtain ⟨q,inside,same⟩ := List.mem_map.mp member
 subst op
 exact TargetOperations.query_keysFit q base fits

noncomputable def code {n : Nat} (G : Schema n) (T : TypeGraph.Ty n) (_permit : CopyPermit G T)
 (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base) : List Evm.Instr :=
 writeProgram (CopyDefaults.updates G T base) (updates_fit G T base fits)

noncomputable def afterInit {n : Nat} (G : Schema n) (T : TypeGraph.Ty n)
 (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base) (machine : Evm.Machine) : Evm.Machine :=
 afterWrites (CopyDefaults.updates G T base) (updates_fit G T base fits) machine

/-- Independent existing default representation/numeric initializer compose
with ACTUAL target instructions and successful SLOAD observations. Only OLD
Transport/agreement and exact generated/selected query coverage are inputs. -/
theorem complete {n N L R : Nat} (G : Schema n) (T : TypeGraph.Ty n)
 (permit : CopyPermit G T) (queries : List (Query G T))
 (supported : ∀ q ∈ queries, q.supported)
 (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base)
 {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (captured : Store) (numeric : WordStore) (machine : Evm.Machine)
 (initial : Transport N hash locations captured numeric)
 (covered : ∀ q ∈ CopyDefaults.demands G T ++ queries, q.location base ∈ locations)
 (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
 (before : ∀ l (member : l ∈ locations), machine.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (captured l)) :
 let afterStore := (CopyDefaults.updates G T base).foldl (fun store op => Representation.write store op.1 op.2) captured
 let afterNumeric := CopyDefaults.numericInit (N:=N) G T base hash numeric
 let afterTarget := afterInit G T base fits machine
 Evm.run (code G T permit base fits) machine=.ok afterTarget 0 ∧
 Represented (Value.dflt T) queries base afterStore ∧
 Transport N hash locations afterStore afterNumeric ∧
 (∀ l (member : l ∈ locations), afterTarget.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (afterNumeric (l.word N hash))) ∧
 (∀ q ∈ queries, ∀ word, q.read (Value.dflt T)=some word →
 Evm.run (TargetOperations.readCode (TargetOperations.toSlot (q.location base) (TargetOperations.query_keysFit q base fits))) afterTarget=
 .ok {afterTarget with stack := .val (TargetOperations.encodeWord word) :: afterTarget.stack} 0) := by
 have executed := run_writes (CopyDefaults.updates G T base) (updates_fit G T base fits) machine
 have owner := CopyDefaults.represented G T permit queries supported base captured
 have transported := CopyDefaults.numeric_transport G T run base captured numeric initial
  (fun q member => covered q (List.mem_append.mpr (Or.inl member)))
 have agreement := agreement_writes (CopyDefaults.updates G T base) (updates_fit G T base fits) captured machine locations fitting before
 refine ⟨executed,owner,transported,?_,?_⟩
 · intro l member
   exact (agreement l member).trans (congrArg TargetOperations.encodeWord (transported l member).symm)
 · intro q member word observed
   apply TargetOperations.represented_read (Value.dflt T) queries base fits _ _ owner _ q member word observed
   intro query queryMember
   exact agreement _ (covered query (List.mem_append.mpr (Or.inr queryMember)))

/-- info: 'Solidity.Backend.StorageOps.TargetDefaultInit.run_writes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_writes
/-- info: 'Solidity.Backend.StorageOps.TargetDefaultInit.outside_writes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms outside_writes
/-- info: 'Solidity.Backend.StorageOps.TargetDefaultInit.context_writes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms context_writes
/-- info: 'Solidity.Backend.StorageOps.TargetDefaultInit.agreement_writes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms agreement_writes
/-- info: 'Solidity.Backend.StorageOps.TargetDefaultInit.updates_fit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms updates_fit
/-- info: 'Solidity.Backend.StorageOps.TargetDefaultInit.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.TargetDefaultInit
