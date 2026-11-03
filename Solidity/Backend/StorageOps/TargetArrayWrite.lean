import Solidity.Backend.StorageOps.TargetArrayRead

/-! Actual runtime primitive writes. Existing live read and save are composed
as an operation adapter, not substituted for ordinary Source evaluation. -/
namespace Solidity.Backend.StorageOps.TargetArrayWrite
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def code : List Evm.Instr := Evm.boundsCheck ++ (Evm.elemSlot 1 ++ [.sstore])
def writeAt {n : Nat} {G : Schema n} {p : PrimTy}
    (old : Value G (.array (.prim p))) (i : Index) (value : p.Denote) : Option (Value G (.array (.prim p))) := do
  let _ ← (TargetArrayRead.path (G := G) (p := p) i).readLive Value.dflt old
  old.save (TargetArrayRead.path (G := G) (p := p) i) (.prim value)

theorem run_current (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (i : Nat) (fits : i < Evm.W) (value : Fin Evm.W) :
    Evm.run code { machine with stack := .val ⟨i,fits⟩ :: .slot slot :: .val value :: tail } =
      if i < machine.store slot then .ok { machine with stack := tail, store := Evm.WordStore.write machine.store (.data slot i) value.val } 0 else .revert := by
  unfold code
  rw [Evm.boundsCheck_run machine (.val value :: tail) _ i slot fits]
  by_cases live : i < machine.store slot
  · simp only [if_pos live]
    rw [Evm.run_append_ok (Evm.elemSlot_run machine (.val value :: tail) i 1 slot fits)]
    simp only [Nat.mul_one]
    rfl
  · simp only [if_neg live]

/-- Successful operation adapter entails BOTH actual live access and actual
existing save. Raw retained save alone is deliberately not sufficient. -/
theorem success {n : Nat} {G : Schema n} {p : PrimTy}
    (old result : Value G (.array (.prim p))) (i : Index) (value : p.Denote)
    (performed : writeAt old i value = some result) :
    i.val < old.length.val ∧ old.save (TargetArrayRead.path (G := G) (p := p) i) (.prim value) = some result := by
  unfold writeAt at performed
  cases found : (TargetArrayRead.path (G := G) (p := p) i).readLive Value.dflt old with
  | none => rw [found] at performed; cases performed
  | some captured =>
    rw [found] at performed
    refine ⟨?_,performed⟩
    by_cases live : i.val < old.length.val
    · exact live
    · have failed := (TargetArrayRead.live_none_iff old i).mpr (by omega)
      rw [found] at failed
      cases failed

/-- No secondary save failure occurs after a LIVE primitive index check.
The existing raw retained save semantics is unchanged. -/
theorem failure {n : Nat} {G : Schema n} {p : PrimTy}
    (old : Value G (.array (.prim p))) (i : Index) (value : p.Denote) :
    writeAt old i value = none ↔ old.length.val ≤ i.val := by
  cases old with
  | array extent length bound slots =>
    by_cases live : i.val < length.val
    · have inside : i.val < extent.val := by omega
      simp only [writeAt,TargetArrayRead.path,TypeGraph.Path.readLive,Step.getLive,Value.length,if_pos live,
        Step.get,dif_pos inside,Option.bind_some,Value.save,TypeGraph.Path.save,Step.put]
      constructor
      · intro impossible; cases impossible
      · intro failed; omega
    · simp only [writeAt,TargetArrayRead.path,TypeGraph.Path.readLive,Step.getLive,Value.length,if_neg live,Option.bind_none]
      constructor
      · intro _; omega
      · intro _; first | rfl | exact True.intro

theorem failure_matches {n : Nat} {G : Schema n} {p : PrimTy}
    (old : Value G (.array (.prim p))) (i : Index) (value : p.Denote)
    (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (header : machine.store slot = old.length.val) :
    Evm.run code { machine with stack := .val ⟨i.val,i.isLt⟩ :: .slot slot :: .val (TargetOperations.encodeWord (PrimTy.toWord value)) :: tail } = .revert ↔ writeAt old i value = none := by
  rw [run_current,header,failure]
  by_cases live : i.val < old.length.val
  · rw [if_pos live]
    constructor
    · intro impossible; cases impossible
    · intro failed; omega
  · rw [if_neg live]
    exact ⟨fun _ => by omega,fun _ => rfl⟩

/-- The path is the same published intrinsic array index location. -/
theorem location {n : Nat} {G : Schema n} {p : PrimTy} (i : Index) (base : Solidity.Storage.Loc) :
    pathLoc (TargetArrayRead.path (G := G) (p := p) i) base = .data base i.val :=
  PrimitivePop.element_location (G := G) (p := p) base i

/-- Reuse the PUBLIC recursive ancestor-header frame, deriving the exact
symbolic child/header separation from the existing Loc constructors. -/
theorem header_frame {n : Nat} {G : Schema n} {p : PrimTy}
    (old result : Value G (.array (.prim p))) (i : Index) (value : p.Denote)
    (performed : writeAt old i value = some result) (base : Solidity.Storage.Loc) (store : Store)
    (before : Represented old [.length .nil] base store) :
    Represented result [.length .nil] base (Representation.write store (pathLoc (TargetArrayRead.path (G := G) (p := p) i) base) (PrimTy.toWord value)) := by
  have saved := (success old result i value performed).2
  have apart : base ≠ pathLoc (TargetArrayRead.path (G := G) (p := p) i) base := by
    rw [location]
    intro same
    have depths := congrArg Solidity.Storage.Loc.depth same
    change base.depth = base.depth + 1 at depths
    omega
  exact before.header_write_frame .nil i .nil (.prim value) saved (PrimTy.toWord value) apart

/-- Actual guarded target write plus PUBLIC selected postrepresentation and
numeric Transport derive only from OLD header/context evidence and actual
source operation, with original finite region/query/frame premises explicit. -/
theorem complete_numeric {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (old result : Value G (.array (.prim p))) (i : Index) (value : p.Denote)
    (performed : writeAt old i value = some result)
    (queries : List (Query G (.array (.prim p)))) (base : Solidity.Storage.Loc)
    (baseFits : TargetOperations.KeysFit base) (store : Store) (numeric : WordStore)
    (machine : Evm.Machine) (tail : List Evm.Word)
    (beforeHeader : Represented old [.length .nil] base store)
    (before : Represented old queries base store)
    (supported : PathSupported (TargetArrayRead.path (G := G) (p := p) i))
    (apart : ∀ q ∈ queries, q.apart (TargetArrayRead.path (G := G) (p := p) i))
    (nonalias : ∀ q ∈ queries, q.location base ≠ pathLoc (TargetArrayRead.path (G := G) (p := p) i) base)
    (initial : Transport N hash locations store numeric)
    (headerCovered : base ∈ locations) (childCovered : pathLoc (TargetArrayRead.path (G := G) (p := p) i) base ∈ locations)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), machine.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l)) :
    let dst := TargetArrayRead.path (G := G) (p := p) i
    let word := PrimTy.toWord value
    let child := pathLoc dst base
    let afterStore := Representation.write store child word
    let afterNumeric := writeWord numeric (child.word N hash) word
    let afterTarget := { machine with stack := tail, store := Evm.WordStore.write machine.store (TargetOperations.toSlot child (TargetOperations.path_keysFit dst base baseFits)) (TargetOperations.encodeWord word).val }
    Evm.run code { machine with stack := .val ⟨i.val,i.isLt⟩ :: .slot (TargetOperations.toSlot base baseFits) :: .val (TargetOperations.encodeWord word) :: tail } = .ok afterTarget 0 ∧
      Represented result (.length .nil :: .word dst :: queries) base afterStore ∧
      Transport N hash locations afterStore afterNumeric ∧
      (∀ l (member : l ∈ locations), afterTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (afterStore l)) := by
  obtain ⟨live,saved⟩ := success old result i value performed
  have header := TargetHeaderPush.source_header old base baseFits store machine beforeHeader (targetInitial base headerCovered)
  have component := RepresentedOperations.scalar_save_numeric run store numeric initial old result (TargetArrayRead.path (G := G) (p := p) i) value queries base before supported saved apart nonalias childCovered
  refine ⟨?_,?_,component.2,?_⟩
  · have address : TargetOperations.toSlot (pathLoc (TargetArrayRead.path (G := G) (p := p) i) base) (TargetOperations.path_keysFit _ base baseFits) = .data (TargetOperations.toSlot base baseFits) i.val := by
      simp only [location,TargetOperations.toSlot]
    rw [run_current,header,if_pos live,address]
  · intro q member
    rcases List.mem_cons.mp member with same | later
    · subst q; exact header_frame old result i value performed base store beforeHeader _ List.mem_cons_self
    · exact component.1 q later
  · exact TargetOperations.write_agreement locations fitting (pathLoc (TargetArrayRead.path (G := G) (p := p) i) base) (TargetOperations.path_keysFit _ base baseFits) (PrimTy.toWord value) store machine targetInitial


/-- info: 'Solidity.Backend.StorageOps.TargetArrayWrite.run_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_current
/-- info: 'Solidity.Backend.StorageOps.TargetArrayWrite.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms success
/-- info: 'Solidity.Backend.StorageOps.TargetArrayWrite.failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms failure
/-- info: 'Solidity.Backend.StorageOps.TargetArrayWrite.failure_matches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failure_matches
/-- info: 'Solidity.Backend.StorageOps.TargetArrayWrite.location' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms location
/-- info: 'Solidity.Backend.StorageOps.TargetArrayWrite.header_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms header_frame
/-- info: 'Solidity.Backend.StorageOps.TargetArrayWrite.complete_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_numeric

end Solidity.Backend.StorageOps.TargetArrayWrite
