import Solidity.Backend.StorageOps.TargetFixedPrimitive
import Solidity.Backend.StorageOps.PathRepresentation
import Solidity.Backend.StorageOps.CommonPrefix

/-! Runtime fixed primitive accesses under arbitrary existing typed ROOT paths.
No new representation/address evaluator or Source/compiler/world bridge.
Captured fitting ROOT addresses and original per-run regions remain explicit. -/
namespace Solidity.Backend.StorageOps.FixedRootPrimitive
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Actual ROOT read yields the local fixed read. Both the current index and
selected payload are consumed by existing fixed-check/load instructions. -/
theorem read {n N : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy} {m : FixedSize}
 (root : Value G A) (pre : TypeGraph.Path G A (.fixed (.prim p) m))
 (old : Value G (.fixed (.prim p) m)) (i : Index) (value : p.Denote)
 (found : root.find pre=some old)
 (selected : root.find (pre.append (TargetFixedPrimitive.path i))=some (.prim value))
 (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base) (store : Store)
 (numeric : WordStore) (hash : Solidity.Storage.Pre → Nat) (locations : List Solidity.Storage.Loc)
 (machine : Evm.Machine) (tail : List Evm.Word)
 (before : Represented root ([.word (TargetFixedPrimitive.path i)].map (Query.prefix pre)) base store)
 (transport : Transport N hash locations store numeric)
 (covered : pathLoc (pre.append (TargetFixedPrimitive.path i)) base ∈ locations)
 (initial : machine.store.cells
  (TargetOperations.toSlot (pathLoc (pre.append (TargetFixedPrimitive.path i)) base)
   (TargetOperations.path_keysFit _ base fits))=
  TargetOperations.encodeWord (store (pathLoc (pre.append (TargetFixedPrimitive.path i)) base))) :
 Evm.run (TargetFixedPrimitive.readCode m)
  {machine with stack:=.val ⟨i.val,i.isLt⟩:: .slot (TargetOperations.toSlot (pathLoc pre base) (TargetOperations.path_keysFit pre base fits))::tail}=
 .ok {machine with stack:=.val (TargetOperations.encodeWord (PrimTy.toWord value))::tail} 0 ∧
 numeric ((pathLoc (pre.append (TargetFixedPrimitive.path i)) base).word N hash)=PrimTy.toWord value := by
 have localRead : old.find (TargetFixedPrimitive.path i)=some (.prim value) := by
  change TypeGraph.Path.read Value.dflt (pre.append _) root=_ at selected
  rw [TypeGraph.Path.read_append] at selected
  change (root.find pre).bind (fun v => v.find (TargetFixedPrimitive.path i))=_ at selected
  simpa only [found,Option.bind_some] using selected
 have owner := PathRepresentation.focus root old pre found [.word (TargetFixedPrimitive.path i)] base store before
 have answer := TargetFixedPrimitive.complete_read old i value localRead (pathLoc pre base)
  (TargetOperations.path_keysFit pre base fits) store numeric hash locations machine tail owner transport
  (by simpa only [pathLoc_append] using covered) (by simpa only [pathLoc_append] using initial)
 simpa only [pathLoc_append] using answer

/-- Actual ROOT save factors through its readable fixed prefix. The successful
save derives the fixed runtime guard, and PUBLIC root frames/numeric transport
follow from the actual update, not a desired postowner premise. -/
theorem write {n N L R : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy} {m : FixedSize}
 {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations)
 (root result : Value G A) (pre : TypeGraph.Path G A (.fixed (.prim p) m))
 (old : Value G (.fixed (.prim p) m)) (i : Index) (value : p.Denote)
 (found : root.find pre=some old) (supported : PathSupported pre)
 (saved : root.save (pre.append (TargetFixedPrimitive.path i)) (.prim value)=some result)
 (queries : List (Query G A)) (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base)
 (store : Store) (numeric : WordStore) (machine : Evm.Machine) (tail : List Evm.Word)
 (before : Represented root queries base store)
 (apart : ∀ q ∈ queries,q.apart (pre.append (TargetFixedPrimitive.path i)))
 (nonalias : ∀ q ∈ queries,q.location base≠pathLoc (pre.append (TargetFixedPrimitive.path i)) base)
 (transport : Transport N hash locations store numeric)
 (covered : pathLoc (pre.append (TargetFixedPrimitive.path i)) base ∈ locations)
 (fitting : ∀ l ∈ locations,TargetOperations.KeysFit l)
 (initial : ∀ l (member : l ∈ locations),machine.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (store l)) :
 let dst := pre.append (TargetFixedPrimitive.path (G:=G) (p:=p) (m:=m) i)
 let child := pathLoc dst base
 let word := PrimTy.toWord value
 let afterStore := Representation.write store child word
 let afterNumeric := writeWord numeric (child.word N hash) word
 let afterTarget := {machine with stack:=tail,store:=Evm.WordStore.write machine.store (TargetOperations.toSlot child (TargetOperations.path_keysFit dst base fits)) (TargetOperations.encodeWord word).val}
 Evm.run (TargetFixedPrimitive.writeCode m)
  {machine with stack:=.val ⟨i.val,i.isLt⟩:: .slot (TargetOperations.toSlot (pathLoc pre base) (TargetOperations.path_keysFit pre base fits)):: .val (TargetOperations.encodeWord word)::tail}=
 .ok afterTarget 0 ∧
 Represented result (.word dst::queries) base afterStore ∧
 Transport N hash locations afterStore afterNumeric ∧
 (∀ l (member : l ∈ locations),afterTarget.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (afterStore l)) := by
 have factored := saved
 rw [prefix_save_append,found] at factored
 simp only [Option.bind_some] at factored
 have live : i.val<m.val := by
  by_cases live : i.val<m.val
  · exact live
  · have failed := (TargetFixedPrimitive.write_failure old i value).mpr (by omega)
    rw [failed] at factored
    cases factored
 have pathSupported : PathSupported (pre.append (TargetFixedPrimitive.path (G:=G) (p:=p) (m:=m) i)) :=
  (PathSupported_append _ _).mpr ⟨supported,by exact ⟨live,True.intro⟩⟩
 have component := RepresentedOperations.scalar_save_numeric run store numeric transport root result
  (pre.append (TargetFixedPrimitive.path i)) value queries base before pathSupported saved apart nonalias covered
 refine ⟨?_,component.1,component.2,?_⟩
 · rw [TargetFixedPrimitive.run_write,if_pos live]
   have address := TargetFixedPrimitive.address (G:=G) (p:=p) (m:=m) i (pathLoc pre base) (TargetOperations.path_keysFit pre base fits)
   simpa only [pathLoc_append] using congrArg
    (fun slot : Evm.Slot => Evm.Out.ok {machine with stack:=tail,store:=Evm.WordStore.write machine.store slot (TargetOperations.encodeWord (PrimTy.toWord value)).val} 0) address.symm
 · exact TargetOperations.write_agreement locations fitting _ (TargetOperations.path_keysFit _ base fits)
    (PrimTy.toWord value) store machine initial

/-- info: 'Solidity.Backend.StorageOps.FixedRootPrimitive.read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read
/-- info: 'Solidity.Backend.StorageOps.FixedRootPrimitive.write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms write
end Solidity.Backend.StorageOps.FixedRootPrimitive
