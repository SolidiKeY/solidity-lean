import Solidity.Backend.StorageOps.TargetPrimitivePopPush

/-! Runtime primitive index reads reuse PUBLIC boundsCheck/elemSlot execution,
with independent typed live paths and OLD selected represented words. No extent
or failed-read-zero assumption substitutes for the actual current header. -/
namespace Solidity.Backend.StorageOps.TargetArrayRead
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def code : List Evm.Instr := Evm.boundsCheck ++ (Evm.elemSlot 1 ++ [.sload])
def path {n : Nat} {G : Schema n} {p : PrimTy} (i : Index) : TypeGraph.Path G (.array (.prim p)) (.prim p) := .cons (.index i) .nil

/-- Runtime index and slot are INPUT stack words. Bounds read the CURRENT
header; success replaces these operands by the actual child SLOAD, preserving
the full other context/store. Both retained and out-of-extent failures revert. -/
theorem run_current (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (i : Nat) (fits : i < Evm.W) :
    Evm.run code { machine with stack := .val ⟨i,fits⟩ :: .slot slot :: tail } =
      if i < machine.store slot then .ok { machine with stack := .val (machine.store.cells (.data slot i)) :: tail } 0 else .revert := by
  unfold code
  rw [Evm.boundsCheck_run machine tail _ i slot fits]
  by_cases live : i < machine.store slot
  · simp only [if_pos live]
    rw [Evm.run_append_ok (Evm.elemSlot_run machine tail i 1 slot fits)]
    simp only [Nat.mul_one]
    rfl
  · simp only [if_neg live]

/-- Existing logical word read is used only after the existing LIVE check. -/
theorem live_word {n : Nat} {G : Schema n} {p : PrimTy}
    (old : Value G (.array (.prim p))) (i : Index) :
    ((path i).readLive Value.dflt old).map (fun v => PrimTy.toWord v.head) =
      if i.val < old.length.val then (PrimitivePop.elementQuery i).read old else none := by
  cases old with
  | array extent length bound slots =>
    by_cases live : i.val < length.val
    · have inside : i.val < extent.val := by omega
      simp only [path,TypeGraph.Path.readLive,Step.getLive,Value.length,if_pos live,Step.get,dif_pos inside,
        Option.bind_some,PrimitivePop.elementQuery,Query.read,Value.observe,Value.find,TypeGraph.Path.read,Option.map_some]
    · simp only [path,TypeGraph.Path.readLive,Step.getLive,Value.length,if_neg live,Option.bind_none,Option.map_none]

theorem live_none_iff {n : Nat} {G : Schema n} {p : PrimTy}
    (old : Value G (.array (.prim p))) (i : Index) :
    (path i).readLive Value.dflt old = none ↔ old.length.val ≤ i.val := by
  cases old with
  | array extent length bound slots =>
    by_cases live : i.val < length.val
    · have inside : i.val < extent.val := by omega
      simp only [path,TypeGraph.Path.readLive,Step.getLive,Value.length,if_pos live,Step.get,dif_pos inside,Option.bind_some]
      constructor
      · intro impossible; cases impossible
      · intro failed; omega
    · simp only [path,TypeGraph.Path.readLive,Step.getLive,Value.length,if_neg live,Option.bind_none]
      exact ⟨fun _ => by omega,fun _ => True.intro⟩

/-- Exact live failure is established from plain OLD header agreement, with no
PUBLIC metadata cap or numeric-zero premise for unsuccessful retained queries. -/
theorem failure_matches {n : Nat} {G : Schema n} {p : PrimTy}
    (old : Value G (.array (.prim p))) (i : Index) (machine : Evm.Machine)
    (tail : List Evm.Word) (slot : Evm.Slot) (header : machine.store slot = old.length.val) :
    Evm.run code { machine with stack := .val ⟨i.val,i.isLt⟩ :: .slot slot :: tail } = .revert ↔
      (path i).readLive Value.dflt old = none := by
  rw [run_current,header,live_none_iff]
  by_cases live : i.val < old.length.val
  · rw [if_pos live]
    constructor
    · intro impossible; cases impossible
    · intro failed; omega
  · rw [if_neg live]
    exact ⟨fun _ => by omega,fun _ => rfl⟩

/-- Successful typed LIVE read connects actual guarded runtime instructions to
OLD PUBLIC represented word and target cell agreement. No evaluated word is
compiled into code; slot/index arrive on the input stack. -/
theorem represented_read {n : Nat} {G : Schema n} {p : PrimTy}
    (old : Value G (.array (.prim p))) (i : Index) (value : Value G (.prim p))
    (found : (path i).readLive Value.dflt old = some value)
    (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base) (store : Store)
    (machine : Evm.Machine) (tail : List Evm.Word)
    (before : Represented old (PrimitivePop.queries [i]) base store)
    (initial : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) [i],
      machine.store.cells (TargetOperations.toSlot (q.location base) (TargetOperations.query_keysFit q base fits)) = TargetOperations.encodeWord (store (q.location base))) :
    Evm.run code { machine with stack := .val ⟨i.val,i.isLt⟩ :: .slot (TargetOperations.toSlot base fits) :: tail } =
      .ok { machine with stack := .val (TargetOperations.encodeWord (PrimTy.toWord value.head)) :: tail } 0 := by
  have headerOwner : Represented old [.length .nil] base store := by
    intro q member; have same := List.mem_singleton.mp member; subst q
    exact before _ List.mem_cons_self
  have header := TargetHeaderPush.source_header old base fits store machine headerOwner (initial (.length .nil) List.mem_cons_self)
  have live : i.val < old.length.val := by
    by_cases live : i.val < old.length.val
    · exact live
    · have failed := (live_none_iff old i).mpr (by omega)
      rw [found] at failed
      cases failed
  have read := live_word old i
  rw [found,Option.map_some,if_pos live] at read
  have member : PrimitivePop.elementQuery (G := G) (p := p) i ∈ PrimitivePop.queries [i] := by
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,List.mem_cons_self,rfl⟩)
  have word := (before _ member).2.2 _ read.symm
  have target := initial _ member
  rw [PrimitivePop.element_location] at word
  have targetCell : machine.store.cells (.data (TargetOperations.toSlot base fits) i.val) = TargetOperations.encodeWord (store (.data base i.val)) := by
    simpa only [PrimitivePop.element_location,TargetOperations.toSlot] using target
  rw [word] at targetCell
  rw [run_current,header,if_pos live]
  rw [targetCell]


/-- Covered numeric readback uses PUBLIC initial Transport; read-only execution
requires no new hash-injectivity axiom or write/frame preservation premise. -/
theorem complete_read {n N : Nat} {G : Schema n} {p : PrimTy}
    (old : Value G (.array (.prim p))) (i : Index) (value : Value G (.prim p))
    (found : (path i).readLive Value.dflt old = some value)
    (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base) (store : Store)
    (machine : Evm.Machine) (tail : List Evm.Word) (numeric : WordStore)
    (hash : Solidity.Storage.Pre → Nat) (locations : List Solidity.Storage.Loc)
    (before : Represented old (PrimitivePop.queries [i]) base store)
    (transported : Transport N hash locations store numeric)
    (covered : Solidity.Storage.Loc.data base i.val ∈ locations)
    (initial : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) [i],
      machine.store.cells (TargetOperations.toSlot (q.location base) (TargetOperations.query_keysFit q base fits)) = TargetOperations.encodeWord (store (q.location base))) :
    Evm.run code { machine with stack := .val ⟨i.val,i.isLt⟩ :: .slot (TargetOperations.toSlot base fits) :: tail } =
      .ok { machine with stack := .val (TargetOperations.encodeWord (PrimTy.toWord value.head)) :: tail } 0 ∧
    numeric ((Solidity.Storage.Loc.data base i.val).word N hash) = PrimTy.toWord value.head := by
  refine ⟨represented_read old i value found base fits store machine tail before initial,?_⟩
  have live : i.val < old.length.val := by
    by_cases live : i.val < old.length.val
    · exact live
    · have failed := (live_none_iff old i).mpr (by omega)
      rw [found] at failed
      cases failed
  have read := live_word old i
  rw [found,Option.map_some,if_pos live] at read
  have member : PrimitivePop.elementQuery (G := G) (p := p) i ∈ PrimitivePop.queries [i] :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,List.mem_cons_self,rfl⟩)
  have word := (before _ member).2.2 _ read.symm
  rw [PrimitivePop.element_location] at word
  exact (transported _ covered).trans word


/-- info: 'Solidity.Backend.StorageOps.TargetArrayRead.run_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_current
/-- info: 'Solidity.Backend.StorageOps.TargetArrayRead.live_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms live_word
/-- info: 'Solidity.Backend.StorageOps.TargetArrayRead.live_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms live_none_iff
/-- info: 'Solidity.Backend.StorageOps.TargetArrayRead.failure_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms failure_matches
/-- info: 'Solidity.Backend.StorageOps.TargetArrayRead.represented_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_read
/-- info: 'Solidity.Backend.StorageOps.TargetArrayRead.complete_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete_read

end Solidity.Backend.StorageOps.TargetArrayRead
