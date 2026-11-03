import Solidity.Backend.StorageOps.TargetArrayWrite
import Solidity.Backend.StorageOps.TargetFixedArrayTransport

/-! Runtime fixed primitive operations consume the CURRENT index/value stack.
Existing PUBLIC fixedCheck/fixedSlot perform the check/address execution;
existing intrinsic paths and PUBLIC representation remain the specification.
No length SLOAD, dynamic hash or new compiler/representation is introduced. -/
namespace Solidity.Backend.StorageOps.TargetFixedPrimitive
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def readCode (m : FixedSize) : List Evm.Instr := Evm.fixedCheck m.val ++ (Evm.fixedSlot 1 ++ [.sload])
def writeCode (m : FixedSize) : List Evm.Instr := Evm.fixedCheck m.val ++ (Evm.fixedSlot 1 ++ [.sstore])
def path {n : Nat} {G : Schema n} {p : PrimTy} {m : FixedSize} (i : Index) : TypeGraph.Path G (.fixed (.prim p) m) (.prim p) := .cons (.fixed i) .nil

theorem run_read (m : FixedSize) (machine : Evm.Machine) (tail : List Evm.Word)
 (slot : Evm.Slot) (i : Index) :
 Evm.run (readCode m) {machine with stack := .val ⟨i.val,i.isLt⟩ :: .slot slot :: tail} =
 if i.val < m.val then .ok {machine with stack := .val (machine.store.cells (slot.add i.val)) :: tail} 0 else .revert := by
 unfold readCode
 have check := Evm.fixedCheck_run machine tail (Evm.fixedSlot 1 ++ [.sload]) m.val i.val slot m.property.2 i.isLt
 rw [check]
 by_cases live : i.val < m.val
 · simp only [if_pos live]
   have moved := Evm.fixedSlot_run machine tail i.val 1 slot i.isLt
   rw [Evm.run_append_ok moved]
   simp only [Nat.mul_one]
   rfl
 · simp only [if_neg live]

theorem run_write (m : FixedSize) (machine : Evm.Machine) (tail : List Evm.Word)
 (slot : Evm.Slot) (i : Index) (value : Fin Evm.W) :
 Evm.run (writeCode m) {machine with stack := .val ⟨i.val,i.isLt⟩ :: .slot slot :: .val value :: tail} =
 if i.val < m.val then .ok {machine with stack := tail,store := Evm.WordStore.write machine.store (slot.add i.val) value.val} 0 else .revert := by
 unfold writeCode
 have check := Evm.fixedCheck_run machine (.val value :: tail) (Evm.fixedSlot 1 ++ [.sstore]) m.val i.val slot m.property.2 i.isLt
 rw [check]
 by_cases live : i.val < m.val
 · simp only [if_pos live]
   have moved := Evm.fixedSlot_run machine (.val value :: tail) i.val 1 slot i.isLt
   rw [Evm.run_append_ok moved]
   simp only [Nat.mul_one]
   rfl
 · simp only [if_neg live]

theorem location {n : Nat} {G : Schema n} {p : PrimTy} {m : FixedSize}
 (i : Index) (base : Solidity.Storage.Loc) :
 pathLoc (path (G:=G) (p:=p) (m:=m) i) base=base.add i.val := by
 simp only [path,pathLoc,stepLoc,inlineSize_prim,Nat.mul_one]

theorem address {n : Nat} {G : Schema n} {p : PrimTy} {m : FixedSize}
 (i : Index) (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base) :
 TargetOperations.toSlot (pathLoc (path (G:=G) (p:=p) (m:=m) i) base)
  (TargetOperations.path_keysFit _ base fits) = (TargetOperations.toSlot base fits).add i.val := by
 simp only [location]
 exact TargetFixedArrayTransport.toSlot_add base fits i.val

/-- Malformed fixed indices really fail; absent in-bounds slots default.
No raw physical zero premise is inferred from an unsuccessful logical read. -/
theorem read_failure {n : Nat} {G : Schema n} {p : PrimTy} {m : FixedSize}
 (old : Value G (.fixed (.prim p) m)) (i : Index) :
 old.find (path i)=none ↔ m.val≤i.val := by
 cases old with
 | fixed slots =>
   by_cases live : i.val < m.val
   · simp only [Value.find,path,TypeGraph.Path.read,Step.get,dif_pos live,Option.bind_some]
     constructor
     · intro impossible; cases impossible
     · intro impossible; omega
   · simp only [Value.find,path,TypeGraph.Path.read,Step.get,dif_neg live,Option.bind_none]
     constructor
     · intro ignored; omega
     · intro ignored; first | rfl | exact True.intro

theorem write_failure {n : Nat} {G : Schema n} {p : PrimTy} {m : FixedSize}
 (old : Value G (.fixed (.prim p) m)) (i : Index) (value : p.Denote) :
 old.save (path i) (.prim value)=none ↔ m.val≤i.val := by
 cases old with
 | fixed slots =>
   by_cases live : i.val < m.val
   · simp only [Value.save,path,TypeGraph.Path.save,Step.get,dif_pos live,Step.put]
     constructor
     · intro impossible; cases impossible
     · intro impossible; omega
   · simp only [Value.save,path,TypeGraph.Path.save,Step.get,dif_neg live]
     constructor
     · intro ignored; omega
     · intro ignored; first | rfl | exact True.intro

/-- Actual current-stack SLOAD and covered numeric read from OLD PUBLIC owner.
No CURRENT index or physical payload is compiled as a source-value oracle. -/
theorem complete_read {n N : Nat} {G : Schema n} {p : PrimTy} {m : FixedSize}
 (old : Value G (.fixed (.prim p) m)) (i : Index) (value : p.Denote)
 (found : old.find (path i)=some (.prim value))
 (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base) (store : Store)
 (numeric : WordStore) (hash : Solidity.Storage.Pre → Nat) (locations : List Solidity.Storage.Loc)
 (machine : Evm.Machine) (tail : List Evm.Word)
 (before : Represented old [.word (path i)] base store)
 (transport : Transport N hash locations store numeric)
 (covered : pathLoc (path (G:=G) (p:=p) (m:=m) i) base ∈ locations)
 (initial : machine.store.cells (TargetOperations.toSlot (pathLoc (path (G:=G) (p:=p) (m:=m) i) base)
  (TargetOperations.path_keysFit _ base fits))=TargetOperations.encodeWord (store (pathLoc (path (G:=G) (p:=p) (m:=m) i) base))) :
 Evm.run (readCode m) {machine with stack := .val ⟨i.val,i.isLt⟩ :: .slot (TargetOperations.toSlot base fits) :: tail} =
 .ok {machine with stack := .val (TargetOperations.encodeWord (PrimTy.toWord value)) :: tail} 0 ∧
 numeric ((pathLoc (path (G:=G) (p:=p) (m:=m) i) base).word N hash)=PrimTy.toWord value := by
 have live : i.val < m.val := by
  by_cases live : i.val < m.val
  · exact live
  · have failed := (read_failure old i).mpr (by omega)
    rw [found] at failed
    cases failed
 have read : (Query.word (path i)).read old=some (PrimTy.toWord value) := by
  simp only [Query.read,Value.observe,found,Option.map_some,Value.head]
 have word := (before _ List.mem_cons_self).2.2 _ read
 change store (pathLoc (path (G:=G) (p:=p) (m:=m) i) base)=PrimTy.toWord value at word
 refine ⟨?_,(transport _ covered).trans word⟩
 rw [run_read,if_pos live]
 rw [address i base fits] at initial
 rw [initial,word]

/-- Successful actual save derives the guard, selected PUBLIC result and all
explicit apart query frames; numeric transport and target agreement are
transported through the actual CURRENT stack write. -/
theorem complete_write {n N L R : Nat} {G : Schema n} {p : PrimTy} {m : FixedSize}
 {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations)
 (old result : Value G (.fixed (.prim p) m)) (i : Index) (value : p.Denote)
 (saved : old.save (path i) (.prim value)=some result)
 (queries : List (Query G (.fixed (.prim p) m))) (base : Solidity.Storage.Loc)
 (fits : TargetOperations.KeysFit base) (store : Store) (numeric : WordStore)
 (machine : Evm.Machine) (tail : List Evm.Word)
 (before : Represented old queries base store)
 (apart : ∀ q ∈ queries,q.apart (path i))
 (nonalias : ∀ q ∈ queries,q.location base≠pathLoc (path (G:=G) (p:=p) (m:=m) i) base)
 (transport : Transport N hash locations store numeric)
 (covered : pathLoc (path (G:=G) (p:=p) (m:=m) i) base ∈ locations)
 (fitting : ∀ l ∈ locations,TargetOperations.KeysFit l)
 (initial : ∀ l (member : l ∈ locations),machine.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (store l)) :
 let dst := path (G:=G) (p:=p) (m:=m) i
 let child := pathLoc dst base
 let word := PrimTy.toWord value
 let afterStore := Representation.write store child word
 let afterNumeric := writeWord numeric (child.word N hash) word
 let afterTarget := {machine with stack := tail,store := Evm.WordStore.write machine.store (TargetOperations.toSlot child (TargetOperations.path_keysFit dst base fits)) (TargetOperations.encodeWord word).val}
 Evm.run (writeCode m) {machine with stack := .val ⟨i.val,i.isLt⟩ :: .slot (TargetOperations.toSlot base fits) :: .val (TargetOperations.encodeWord word) :: tail}=.ok afterTarget 0 ∧
 Represented result (.word dst :: queries) base afterStore ∧
 Transport N hash locations afterStore afterNumeric ∧
 (∀ l (member : l ∈ locations),afterTarget.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (afterStore l)) := by
 have live : i.val < m.val := by
  by_cases live : i.val < m.val
  · exact live
  · have failed := (write_failure old i value).mpr (by omega)
    rw [saved] at failed
    cases failed
 have supported : PathSupported (path (G:=G) (p:=p) (m:=m) i) := ⟨live,True.intro⟩
 have component := RepresentedOperations.scalar_save_numeric run store numeric transport old result (path i) value queries base before supported saved apart nonalias covered
 refine ⟨?_,component.1,component.2,?_⟩
 · rw [run_write,if_pos live,address]
 · exact TargetOperations.write_agreement locations fitting _ (TargetOperations.path_keysFit _ base fits) (PrimTy.toWord value) store machine initial

/-- info: 'Solidity.Backend.StorageOps.TargetFixedPrimitive.run_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_read
/-- info: 'Solidity.Backend.StorageOps.TargetFixedPrimitive.run_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_write
/-- info: 'Solidity.Backend.StorageOps.TargetFixedPrimitive.location' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms location
/-- info: 'Solidity.Backend.StorageOps.TargetFixedPrimitive.address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms address
/-- info: 'Solidity.Backend.StorageOps.TargetFixedPrimitive.read_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms read_failure
/-- info: 'Solidity.Backend.StorageOps.TargetFixedPrimitive.write_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms write_failure
/-- info: 'Solidity.Backend.StorageOps.TargetFixedPrimitive.complete_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_read
/-- info: 'Solidity.Backend.StorageOps.TargetFixedPrimitive.complete_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_write
end Solidity.Backend.StorageOps.TargetFixedPrimitive
