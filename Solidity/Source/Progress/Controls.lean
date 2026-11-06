import Solidity.Source.Progress.CheckedPrograms
import Solidity.Source.Preservation.FragmentControls
import Solidity.Lowering.P9.ProgramControls

/-! Actual contract-backed admission, inhabited memory-prefix consumer and
refusal controls. Existing exact source runs are reused, not re-proved.
-/
namespace Solidity.Source.Progress.Controls
open Solidity.Lowering.P9 Preservation

abbrev E := resolution.env
def initial : St E := CallerReferenceControls.original

theorem catalogue : WholeProgram.functions resolution = [declaration] := rfl

theorem admitted (fixed : Roadmap.Fixed) : WholeProgram.checkFunctions resolution (glob fixed) "P9" = true := by
  unfold WholeProgram.checkFunctions
  rw [catalogue]
  exact ProgramControls.checker_accepts fixed

theorem actual_contract (fixed : Roadmap.Fixed) : "P9" ∈ (glob fixed).prog.contracts :=
  List.mem_singleton.mpr rfl

theorem fragment : protectedCall.ValFragC (fun d => d ∈ WholeProgram.functions resolution) := by
  rw [catalogue]
  exact ⟨List.mem_singleton.mpr rfl, trivial⟩

theorem initial_mem : MemOK E (Heap.empty : Heap E.layout).ty
    (.cons (.bool false) .nil, initial) :=
  relocalize (CallerReferenceControls.caller_valid (E := E)) _ ⟨trivial, trivial⟩

theorem checked (fixed : Roadmap.Fixed) (n : Nat) (H : HeapTy) :
    NS (evalE (glob fixed) caller n protectedCall) ∧
      Hoare (MemOK E H) (evalE (glob fixed) caller n protectedCall)
        (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) :=
  checked_expr AdmissionControls.truth_accepted rfl (admitted fixed) caller rfl n protectedCall fragment trivial H

theorem exact_run (fixed : Roadmap.Fixed) :
    (evalE (glob fixed) caller 11 protectedCall).run (.cons (.bool false) .nil, initial) =
      (.ok (.val (.bool true)), (.cons (.bool false) .nil, initial)) :=
  ProgramControls.checked_execution fixed initial

theorem inhabited_consumer (fixed : Roadmap.Fixed) :
    MemOK E (Heap.empty : Heap E.layout).ty
      ((evalE (glob fixed) caller 11 protectedCall).run (.cons (.bool false) .nil, initial)).2 := by
  have h := (checked fixed 11 (Heap.empty : Heap E.layout).ty).2 _ initial_mem
  rw [exact_run] at h
  rw [exact_run]
  exact h.1

theorem wrong_result (fixed : Roadmap.Fixed) :
    (evalE (glob fixed) caller 11 protectedCall).run (.cons (.bool false) .nil, initial) ≠
      (.ok (.val (.bool false)), (.cons (.bool false) .nil, initial)) := by rw [exact_run]; intro h; cases h

theorem timeout_retained (fixed : Roadmap.Fixed) :
    (evalE (glob fixed) caller 0 protectedCall).run (.cons (.bool false) .nil, initial) =
      (.error .timeout, (.cons (.bool false) .nil, initial)) := rfl

open AdmissionControls in
theorem abstract_elaborates_but_refused (fixed : Roadmap.Fixed) :
    (Source.elaborate interfaceResolution).isSome = true ∧
      WholeProgram.checkFunctions interfaceResolution (ProgramControls.globOf interfaceResolution fixed)
        "NoContract" = false := by
  refine ⟨interface_accepted, ?_⟩
  change WholeProgram.check interfaceResolution (ProgramControls.globOf interfaceResolution fixed)
    "NoContract" [abstractDecl] = false
  exact ProgramControls.abstract_refused fixed

theorem dangling_input_refused : ¬ MemOK E (Heap.empty : Heap E.layout).ty
    (.cons (.memRef rfl 1 : Val E.layout (.bytes .memory)) .nil, initial) := by
  intro h
  obtain ⟨t, ht, hs⟩ := h.1.2.1
  cases ht

#print axioms checked
#print axioms inhabited_consumer
#print axioms abstract_elaborates_but_refused
#print axioms dangling_input_refused
end Solidity.Source.Progress.Controls
