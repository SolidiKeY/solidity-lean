import Solidity.Backend.StorageOps.PrimitiveCycleTransport

/-! Actual existing primitive numeric and Evm.Instr operation composition.
Intermediate ownership/transport/target agreement derive from OLD evidence.
The numeric model inherits the existing pair's noncomputable declaration;
no ordinary Source, bytecode/gas or World execution is asserted. -/
namespace Solidity.Backend.StorageOps.PrimitiveCycleProgram
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def code (slot : Evm.Slot) : List Evm.Instr :=
 TargetPrimitivePopPush.code slot ++ TargetPrimitivePop.code slot

noncomputable def execute (N : Nat) (hash : Solidity.Storage.Pre → Nat)
 (base : Solidity.Storage.Loc) (numeric : WordStore) : Option WordStore := do
 let grown ← TargetPrimitivePopPush.execute N hash base numeric
 PrimitivePop.execute N hash base grown

/-- The actual operation-generated symbolic updates return to FIRST-pop words,
without claiming raw Value equality or any world/heap identity. -/
theorem store_returns {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
 (old middle grown result : Value G (.array E))
 (popped : recursivePop old=some middle) (pushed : operationPush middle=some grown)
 (second : recursivePop grown=some result) (base : Solidity.Storage.Loc) (store : Store) :
 let child := Solidity.Storage.Loc.data base (old.length.val-1)
 let firstStore := Representation.write (Representation.write store child ClearDemands.zero)
   base (lengthWord middle.length.val middle.length.isLt)
 let grownStore := Representation.write (Representation.write firstStore (.data base middle.length.val) ClearDemands.zero)
   base (lengthWord grown.length.val grown.length.isLt)
 Representation.write (Representation.write grownStore (.data base (grown.length.val-1)) ClearDemands.zero)
   base (lengthWord result.length.val result.length.isLt) = firstStore := by
 have firstHeader := recursivePop_header old middle popped
 have grownHeader := PopPush.headers old middle grown popped pushed
 have finalHeader := PrimitiveCycleTransport.headers old middle grown result popped pushed second
 have firstChild : Solidity.Storage.Loc.data base middle.length.val = .data base (old.length.val-1) := by
  have last : middle.length.val=old.length.val-1 := by omega
  rw [last]
 have secondChild : Solidity.Storage.Loc.data base (grown.length.val-1) = .data base (old.length.val-1) := by
  rw [grownHeader.1]
 have word : lengthWord result.length.val result.length.isLt = lengthWord middle.length.val middle.length.isLt :=
  congrArg (fun length : Index => lengthWord length.val length.isLt) finalHeader.1
 dsimp only
 rw [firstChild,secondChild,word]
 funext observer
 by_cases root : observer=base
 · subst observer
   simp only [Representation.write,if_true]
 · by_cases cell : observer=Solidity.Storage.Loc.data base (old.length.val-1)
   · simp only [Representation.write,if_neg root,if_pos cell]
   · simp only [Representation.write,if_neg root,if_neg cell]

/-- Empty runtime pop reverts before the pair or final pop can write. -/
theorem run_empty (slot : Evm.Slot) (machine : Evm.Machine)
 (empty : machine.store slot=0) : Evm.run (code slot) machine=.revert := by
 unfold code
 apply Evm.run_append_revert
 exact TargetPrimitivePopPush.run_empty slot machine empty

/-- Actual triple: all middle/grown owner, transport and target facts follow
from ORIGINAL inputs. Legacy metadata, per-run interpretation and coverage stay
explicit; no desired middle or final preservation is an input premise. -/
theorem complete_numeric {n N L R : Nat} {G : Schema n} {p : PrimTy}
 {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash preimages locations)
 (old middle grown result : Value G (.array (.prim p)))
 (popped : recursivePop old=some middle) (pushed : operationPush middle=some grown)
 (second : recursivePop grown=some result)
 (indices : List Index) (base : Solidity.Storage.Loc) (baseFits : TargetOperations.KeysFit base)
 (store : Store) (machine : Evm.Machine) (numeric : WordStore)
 (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
 (before : Represented old (PrimitivePop.queries indices) base store)
 (initial : Transport N hash locations store numeric)
 (targetInitial : ∀ l (member : l ∈ locations), machine.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
 (covered : ∀ q ∈ PrimitivePop.queries (G:=G) (p:=p) indices, q.location base ∈ locations)
 (lastCovered : Solidity.Storage.Loc.data base (old.length.val-1) ∈ locations) :
 let firstWord := lengthWord middle.length.val middle.length.isLt
 let child := Solidity.Storage.Loc.data base (old.length.val-1)
 let firstStore := Representation.write (Representation.write store child ClearDemands.zero) base firstWord
 let firstTarget := {machine with store := Evm.WordStore.write (Evm.WordStore.write machine.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord firstWord).val) (TargetOperations.toSlot child baseFits) 0}
 let growWord := lengthWord grown.length.val grown.length.isLt
 let growChild := Solidity.Storage.Loc.data base middle.length.val
 let grownStore := Representation.write (Representation.write firstStore growChild ClearDemands.zero) base growWord
 let grownTarget := {firstTarget with store := Evm.WordStore.write (Evm.WordStore.write firstTarget.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord growWord).val) (TargetOperations.toSlot growChild baseFits) 0}
 let finalWord := lengthWord result.length.val result.length.isLt
 let finalChild := Solidity.Storage.Loc.data base (grown.length.val-1)
 let finalStore := Representation.write (Representation.write grownStore finalChild ClearDemands.zero) base finalWord
 let finalTarget := {grownTarget with store := Evm.WordStore.write (Evm.WordStore.write grownTarget.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord finalWord).val) (TargetOperations.toSlot finalChild baseFits) 0}
 ∃ finalNumeric,
 GraphRetainedCycle.execute old=some result ∧ execute N hash base numeric=some finalNumeric ∧
 Evm.run (code (TargetOperations.toSlot base baseFits)) machine=.ok finalTarget 0 ∧
 Represented result (PrimitivePop.queries indices) base finalStore ∧
 Transport N hash locations finalStore finalNumeric ∧
 (∀ l (member : l ∈ locations), finalTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (finalNumeric (l.word N hash))) ∧
 (∀ query ∈ PrimitivePop.queries indices, ∀ word, query.read result=some word → finalNumeric (query.location base |>.word N hash)=word) ∧
 finalStore=firstStore := by
 obtain ⟨grownNumeric,pairNumeric,pairTarget,grownOwner,grownTransport,grownAgreement⟩ :=
  TargetPrimitivePopPush.complete_numeric run old middle grown popped pushed indices base baseFits store machine numeric fitting before initial targetInitial covered lastCovered
 have grownHeader := (PopPush.headers old middle grown popped pushed).1
 have finalCovered : Solidity.Storage.Loc.data base (grown.length.val-1) ∈ locations := by
  rw [grownHeader]
  exact lastCovered
 let firstStore : Store := Representation.write (Representation.write store (.data base (old.length.val-1)) ClearDemands.zero)
   base (lengthWord middle.length.val middle.length.isLt)
 let firstTarget : Evm.Machine := {machine with store := Evm.WordStore.write (Evm.WordStore.write machine.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord (lengthWord middle.length.val middle.length.isLt )).val) (TargetOperations.toSlot (.data base (old.length.val-1)) baseFits) 0}
 let grownStore : Store := Representation.write (Representation.write firstStore (.data base middle.length.val) ClearDemands.zero)
   base (lengthWord grown.length.val grown.length.isLt)
 let grownTarget : Evm.Machine := {firstTarget with store := Evm.WordStore.write (Evm.WordStore.write firstTarget.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord (lengthWord grown.length.val grown.length.isLt )).val) (TargetOperations.toSlot (.data base middle.length.val) baseFits) 0}
 have grownTargetAgreement : ∀ l (member : l ∈ locations),
   grownTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (grownStore l) := by
  intro l member
  exact (grownAgreement l member).trans (congrArg TargetOperations.encodeWord (grownTransport l member))
 obtain ⟨finalNumeric,popNumeric,popTarget,owner,transported,agreement⟩ :=
  TargetPrimitivePop.complete_numeric run grown result second indices base baseFits grownStore grownTarget grownNumeric fitting
    grownOwner grownTransport grownTargetAgreement covered finalCovered
 have intrinsic := (PrimitiveCycleTransport.complete old middle grown result popped pushed second indices base store before).1
 refine ⟨finalNumeric,intrinsic,?_,?_,owner,transported,agreement,?_,store_returns old middle grown result popped pushed second base store⟩
 · unfold execute
   rw [pairNumeric]
   exact popNumeric
 · unfold code
   rw [Evm.run_append_ok pairTarget]
   exact popTarget
 · intro query member word observed
   exact owner.numeric transported query member (covered query member) word observed

/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleProgram.store_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms store_returns
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleProgram.run_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_empty
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleProgram.complete_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_numeric
end Solidity.Backend.StorageOps.PrimitiveCycleProgram
