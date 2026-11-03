import Solidity.Backend.StorageOps.RepresentedOperations
import Solidity.Storage.HashedLayoutEvm

/-! Operation-side adapters between PUBLIC graph/symbolic representation and
existing Evm.Instr storage operations. No instruction semantics, graph/value
layer, ordinary Source lowering or external numeric-storage bridge is replaced.
These captured-path components retain the existing symbolic-slot target boundary;
bytecode, runtime source address evaluation and live/failing checks remain open. -/
namespace Solidity.Backend.StorageOps.TargetOperations
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Only the existing target key word boundary. EVERY typed path from a fitting
base derives this property; it is not a new source profile/admission restriction. -/
abbrev KeysFit := Solidity.Storage.KeysBelow Evm.W

def toSlot : (l : Solidity.Storage.Loc) → KeysFit l → Evm.Slot
  | .root offset, _ => .root offset
  | .hash key parent offset, fits => .hash ⟨key,fits.1⟩ (toSlot parent fits.2) offset
  | .data parent offset, fits => .data (toSlot parent fits) offset


theorem ofSlot_toSlot (l : Solidity.Storage.Loc) (fits : KeysFit l) : Solidity.Storage.ofSlot (toSlot l fits) = l := by
  induction l with
  | root offset => rfl
  | hash key parent offset ih => exact congrArg (fun p => Solidity.Storage.Loc.hash key p offset) (ih fits.2)
  | data parent offset ih => exact congrArg (fun p => Solidity.Storage.Loc.data p offset) (ih fits)

/-- Reuse the PUBLIC forward map's injectivity/range result. -/
theorem toSlot_ofSlot (slot : Evm.Slot) :
    toSlot (Solidity.Storage.ofSlot slot) (Solidity.Storage.keysBelow_ofSlot slot) = slot :=
  Solidity.Storage.ofSlot_injective (ofSlot_toSlot _ _)

theorem toSlot_injective (a b : Solidity.Storage.Loc) (fa : KeysFit a) (fb : KeysFit b)
    (equal : toSlot a fa = toSlot b fb) : a = b := by
  have backward := congrArg Solidity.Storage.ofSlot equal
  simpa only [ofSlot_toSlot] using backward

theorem add_keysFit (l : Solidity.Storage.Loc) (fits : KeysFit l) (offset : Nat) : KeysFit (l.add offset) := by
  cases l <;> exact fits

theorem step_keysFit {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (step : TypeGraph.Step G A B) (base : Solidity.Storage.Loc) (fits : KeysFit base) : KeysFit (stepLoc step base) := by
  cases step with
  | field position => exact add_keysFit base fits _
  | index i => exact fits
  | fixed i => exact add_keysFit base fits _
  | key k => exact ⟨keyWord_lt k,fits⟩

/-- No finite path depth bound; malformed indices are NOT proved live by this
address conversion. Successful/failing semantic reads remain independent. -/
theorem path_keysFit {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (path : TypeGraph.Path G A B) (base : Solidity.Storage.Loc) (fits : KeysFit base) : KeysFit (pathLoc path base) := by
  induction path generalizing base with
  | nil => exact fits
  | cons step tail ih => exact ih (stepLoc step base) (step_keysFit step base fits)

theorem query_keysFit {n : Nat} {G : Schema n} {A : TypeGraph.Ty n}
    (query : Query G A) (base : Solidity.Storage.Loc) (fits : KeysFit base) : KeysFit (query.location base) := by
  cases query with
  | word path => exact path_keysFit path base fits
  | length path => exact path_keysFit path base fits

/-- Reuse PUBLIC primitive normalization and its checked word bound. -/
def encodeWord (word : Semantics.Word) : Fin Evm.W := ⟨keyWord (p := .uint) word,keyWord_lt word⟩

def readCode (slot : Evm.Slot) : List Evm.Instr := [.push (.slot slot),.sload]
def writeCode (slot : Evm.Slot) (word : Semantics.Word) : List Evm.Instr :=
  [.push (.val (encodeWord word)),.push (.slot slot),.sstore]
/-- Actual SLOAD reads the CURRENT target store before SSTORE; no evaluated
source payload is supplied as a compile-time target oracle. -/
def copyCode (dst src : Evm.Slot) : List Evm.Instr :=
  [.push (.slot src),.sload,.push (.slot dst),.sstore]

theorem run_read (slot : Evm.Slot) (machine : Evm.Machine) :
    Evm.run (readCode slot) machine = .ok { machine with stack := .val (machine.store.cells slot) :: machine.stack } 0 := rfl

theorem run_write (slot : Evm.Slot) (word : Semantics.Word) (machine : Evm.Machine) :
    Evm.run (writeCode slot word) machine =
      .ok { machine with store := Evm.WordStore.write machine.store slot (encodeWord word).val } 0 := rfl

theorem run_copy (dst src : Evm.Slot) (machine : Evm.Machine) :
    Evm.run (copyCode dst src) machine =
      .ok { machine with store := Evm.WordStore.write machine.store dst (machine.store.cells src).val } 0 := rfl

/-- A successful independent graph read is related to ACTUAL SLOAD through the
old PUBLIC owner relation and initial target cell agreement. This does not infer
failure or liveness checks from the total symbolic target storage operation. -/
theorem represented_read {n : Nat} {G : Schema n} {A : TypeGraph.Ty n}
    (value : Value G A) (queries : List (Query G A)) (base : Solidity.Storage.Loc)
    (fits : KeysFit base) (store : Store) (machine : Evm.Machine)
    (before : Represented value queries base store)
    (initial : ∀ q ∈ queries,
      machine.store.cells (toSlot (q.location base) (query_keysFit q base fits)) = encodeWord (store (q.location base)))
    (query : Query G A) (member : query ∈ queries) (word : Semantics.Word) (read : query.read value = some word) :
    Evm.run (readCode (toSlot (query.location base) (query_keysFit query base fits))) machine =
      .ok { machine with stack := .val (encodeWord word) :: machine.stack } 0 := by
  rw [run_read,initial query member,(before query member).2.2 word read]

/-- Initial target agreement is a plain observation equality over existing
stores, independent of the compiler. Actual SSTORE preserves it at EVERY covered
fitting location after the owner's concrete symbolic write. -/
theorem write_agreement (locations : List Solidity.Storage.Loc)
    (fits : ∀ l ∈ locations, KeysFit l) (dst : Solidity.Storage.Loc) (dstFits : KeysFit dst)
    (word : Semantics.Word) (store : Store) (machine : Evm.Machine)
    (before : ∀ l (member : l ∈ locations),
      machine.store.cells (toSlot l (fits l member)) = encodeWord (store l)) :
    ∀ l (member : l ∈ locations),
      (Evm.WordStore.write machine.store (toSlot dst dstFits) (encodeWord word).val).cells
        (toSlot l (fits l member)) = encodeWord (Representation.write store dst word l) := by
  intro l member
  by_cases equal : l = dst
  · subst l
    rw [Evm.WordStore.write_cells_same,Representation.write_same]
  · apply Fin.ext
    rw [Evm.WordStore.cells_val,Evm.WordStore.write_other]
    · exact congrArg Fin.val (before l member) |>.trans (congrArg Fin.val (congrArg encodeWord
        (Representation.write_other store dst l word equal).symm))
    · intro same
      exact equal (toSlot_injective l dst (fits l member) dstFits same)

/-- Actual SLOAD/SSTORE self-alias preserves the entire target Machine,
including arbitrary stack/memory/environment/balances. No graph raw-presence or
world rollback identity is inferred. -/
theorem run_copy_self (slot : Evm.Slot) (machine : Evm.Machine) :
    Evm.run (copyCode slot slot) machine = .ok machine 0 := by
  have same : Evm.WordStore.write machine.store slot (machine.store.cells slot).val = machine.store := by
    apply Evm.WordStore.ext
    intro other
    by_cases equal : other = slot
    · subst other
      exact Evm.WordStore.write_same_of_lt machine.store slot _ (machine.store.cells slot).isLt
    · exact Evm.WordStore.write_other machine.store _ equal
  rw [run_copy,same]

/-- Operation-side composition: independent graph scalar copy, PUBLIC selected
representation, existing per-run numeric transport, and ACTUAL runtime target
SLOAD/SSTORE. Initial target agreement is finite and independent of the compiler.
The target reads its CURRENT source cell; code does not embed an evaluated source
payload. This does NOT discharge ordinary Source lowering, runtime path checks,
recursive target traversal, tagged-slot expansion or external bytecode/world. -/
theorem represented_copy {n N L R : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy}
    {H : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R H P locations) (store : Store) (numeric : WordStore)
    (transport : Transport N H locations store numeric)
    (root result : Value G A) (dst src : TypeGraph.Path G A (.prim p)) (value : p.Denote)
    (source : root.find src = some (.prim value)) (performed : recursiveCopyAt root dst src = some result)
    (queries : List (Query G A)) (base : Solidity.Storage.Loc) (baseFits : KeysFit base)
    (represented : Represented root (.word src :: queries) base store) (supported : PathSupported dst)
    (apart : ∀ q ∈ queries, q.apart dst)
    (nonalias : ∀ q ∈ queries, q.location base ≠ pathLoc dst base)
    (sourceCovered : pathLoc src base ∈ locations) (targetCovered : pathLoc dst base ∈ locations)
    (queryCovered : ∀ q ∈ queries, q.location base ∈ locations)
    (fitting : ∀ l ∈ locations, KeysFit l) (target : Evm.Machine)
    (initial : ∀ l (member : l ∈ locations),
      target.store.cells (toSlot l (fitting l member)) = encodeWord (store l)) :
    let d := toSlot (pathLoc dst base) (path_keysFit dst base baseFits)
    let s := toSlot (pathLoc src base) (path_keysFit src base baseFits)
    let afterStore := Representation.write store (pathLoc dst base) (PrimTy.toWord value)
    let afterNumeric := RepresentedOperations.numericCopy numeric ((pathLoc dst base).word N H) ((pathLoc src base).word N H)
    let afterTarget := { target with store := Evm.WordStore.write target.store d (encodeWord (PrimTy.toWord value)).val }
    Evm.run (copyCode d s) target = .ok afterTarget 0 ∧
      Represented result (.word dst :: queries) base afterStore ∧
      Transport N H locations afterStore afterNumeric ∧
      (∀ l (member : l ∈ locations),
        afterTarget.store.cells (toSlot l (fitting l member)) = encodeWord (afterStore l)) := by
  have oldWord : store (pathLoc src base) = PrimTy.toWord value :=
    (represented (.word src) List.mem_cons_self).2.2 _
      (by simp only [Query.read,Value.observe,source,Option.map_some,Value.head])
  have targetSource : target.store.cells (toSlot (pathLoc src base) (path_keysFit src base baseFits)) =
      encodeWord (PrimTy.toWord value) := (initial _ sourceCovered).trans (congrArg encodeWord oldWord)
  have component := RepresentedOperations.copyAt_scalar_numeric run store numeric transport
    root result dst src value source performed queries base represented supported apart nonalias
    sourceCovered targetCovered queryCovered
  refine ⟨?_,component.1,component.2.1,?_⟩
  · rw [run_copy,targetSource]
  · exact write_agreement locations fitting (pathLoc dst base) (path_keysFit dst base baseFits)
      (PrimTy.toWord value) store target initial

/-- info: 'Solidity.Backend.StorageOps.TargetOperations.KeysFit' does not depend on any axioms -/
#guard_msgs in #print axioms KeysFit
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.toSlot' does not depend on any axioms -/
#guard_msgs in #print axioms toSlot
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.ofSlot_toSlot' does not depend on any axioms -/
#guard_msgs in #print axioms ofSlot_toSlot
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.toSlot_ofSlot' depends on axioms: [propext] -/
#guard_msgs in #print axioms toSlot_ofSlot
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.toSlot_injective' does not depend on any axioms -/
#guard_msgs in #print axioms toSlot_injective
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.add_keysFit' does not depend on any axioms -/
#guard_msgs in #print axioms add_keysFit
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.step_keysFit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_keysFit
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.path_keysFit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms path_keysFit
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.query_keysFit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms query_keysFit
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.encodeWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms encodeWord
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.readCode' does not depend on any axioms -/
#guard_msgs in #print axioms readCode
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.writeCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms writeCode
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.copyCode' does not depend on any axioms -/
#guard_msgs in #print axioms copyCode
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.run_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_read
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.run_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_write
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.run_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_copy
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.represented_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_read
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.write_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms write_agreement
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.run_copy_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_copy_self
/-- info: 'Solidity.Backend.StorageOps.TargetOperations.represented_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_copy

end Solidity.Backend.StorageOps.TargetOperations
