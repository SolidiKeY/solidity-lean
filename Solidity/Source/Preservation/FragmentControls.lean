import Solidity.Source.Preservation.Fragment
import Solidity.Source.Preservation.CallerReferenceControls
import Solidity.Lowering.P9.CatalogControls

/-! Inhabited joint preservation consumers for actually elaborated complete
call catalogues. A nonempty memory prefix/caller reference is retained through
nested success and recursive timeout. These are source, not EVM, observations.
-/
namespace Solidity.Source.Preservation.FragmentControls
open Solidity.Lowering.P9

abbrev E := GraphControls.resolution.env
def call : RExpr E [.bytes .memory] .bool := .call GraphControls.entryDecl GraphControls.entry_sig .nil
def initial : St E := CallerReferenceControls.original
def caller : Locals E.layout [.bytes .memory] := CallerReferenceControls.caller

theorem initial_mem : MemOK E (Heap.empty : Heap E.layout).ty (caller, initial) :=
  CallerReferenceControls.caller_valid

theorem in_catalog : GraphControls.entryDecl ∈ WholeProgram.functions GraphControls.resolution := by
  rw [CatalogControls.graph_catalog]
  exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)

theorem fragment : call.ValFragC (fun d => d ∈ WholeProgram.functions GraphControls.resolution) :=
  ⟨in_catalog, trivial⟩

theorem source_and_memory (fixed : Roadmap.Fixed) (n : Nat) :
    Source.FragAt (fun d => d ∈ WholeProgram.functions GraphControls.resolution)
      (GraphControls.glob fixed) "P9" n ∧
    FragMemAt (fun d => d ∈ WholeProgram.functions GraphControls.resolution)
      (GraphControls.glob fixed) "P9" n :=
  progress_and_preservation (CatalogControls.graph_calls fixed) n

theorem checked_mem (fixed : Roadmap.Fixed) (n : Nat) (H : HeapTy) :
    Hoare (MemOK E H) (evalE (GraphControls.glob fixed) Solidity.Lowering.P9.caller n call)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) :=
  evalE_fragment_mem (CatalogControls.graph_calls fixed) Solidity.Lowering.P9.caller rfl n call fragment trivial H

theorem checked_ns (fixed : Roadmap.Fixed) (n : Nat) :
    NS (evalE (GraphControls.glob fixed) Solidity.Lowering.P9.caller n call) :=
  evalE_callFrag_ns (CatalogControls.graph_calls fixed) Solidity.Lowering.P9.caller rfl n call fragment trivial

theorem nested_success (fixed : Roadmap.Fixed) :
    (evalE (GraphControls.glob fixed) Solidity.Lowering.P9.caller 12 call).run (caller, initial) =
      (.ok (.val (.bool true)), (caller, initial)) := by
  rw [← GraphControls.cachedGlob_eq fixed]
  rfl

theorem inhabited_preservation (fixed : Roadmap.Fixed) :
    MemOK E (Heap.empty : Heap E.layout).ty
      ((evalE (GraphControls.glob fixed) Solidity.Lowering.P9.caller 12 call).run (caller, initial)).2 := by
  have h := checked_mem fixed 12 (Heap.empty : Heap E.layout).ty (caller, initial) initial_mem
  rw [nested_success] at h
  rw [nested_success]
  exact h.1

theorem wrong_result (fixed : Roadmap.Fixed) :
    (evalE (GraphControls.glob fixed) Solidity.Lowering.P9.caller 12 call).run (caller, initial) ≠
      (.ok (.val (.bool false)), (caller, initial)) := by rw [nested_success]; intro h; cases h

abbrev RE := RecursiveControls.resolution.env
def recCall : RExpr RE [.bytes .memory] .bool :=
  .call RecursiveControls.declaration RecursiveControls.signature .nil

theorem recursive_timeout (fixed : Roadmap.Fixed) :
    (evalE (RecursiveControls.glob fixed) Solidity.Lowering.P9.caller 12 recCall).run
      (CallerReferenceControls.caller, CallerReferenceControls.original) =
    (.error .timeout, (CallerReferenceControls.caller, CallerReferenceControls.original)) := by
  rw [← RecursiveControls.cachedGlob_eq fixed]
  rfl

theorem recursive_mem (fixed : Roadmap.Fixed) (n : Nat) (H : HeapTy) :
    Hoare (MemOK RE H) (evalE (RecursiveControls.glob fixed) Solidity.Lowering.P9.caller n recCall)
      (fun v y => MemOK RE H y ∧ RValOK RE y.2.heap.ty v) (fun _ y => MemOK RE H y) :=
  evalE_fragment_mem (RecursiveControls.derived_callsOK fixed) Solidity.Lowering.P9.caller rfl n recCall
    ⟨List.mem_singleton.mpr rfl, trivial⟩ trivial H

#print axioms source_and_memory
#print axioms checked_mem
#print axioms nested_success
#print axioms recursive_mem
#print axioms recursive_timeout
end Solidity.Source.Preservation.FragmentControls
