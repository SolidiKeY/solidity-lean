import Solidity.Evm.Machine

/-! Structural consequences of a complete numeric word observation. No execution
or target admission is defined here. The entire protected stack is retained. -/
namespace Solidity.Backend.InternalFlow
open Evm

def observedWord (n : Nat) : Word := .val (Evm.wmod n)

theorem numeric_snapshot (ws : List Word) (ns : List Nat)
    (h : ws.mapM (fun w => match w with | .val v => some v.val | .slot _ => none) = some ns) :
    ws = ns.map observedWord := by
  induction ws generalizing ns with
  | nil => cases h; rfl
  | cons w ws ih =>
    cases w with
    | slot s => cases h
    | val v =>
      cases ht : ws.mapM (fun w => match w with | .val v => some v.val | .slot _ => none) with
      | none => simp only [List.mapM_cons,ht] at h; cases h
      | some tail =>
        simp only [List.mapM_cons,ht] at h
        change some (v.val :: tail) = some ns at h
        cases h
        have head : Word.val v = observedWord v.val := by
          apply congrArg Word.val
          apply Fin.ext
          exact (Nat.mod_eq_of_lt v.isLt).symm
        change Word.val v :: ws = observedWord v.val :: tail.map observedWord
        rw [head,ih tail ht]

theorem numeric_stack_cells (m : Machine) (addresses stack cells : List Nat)
    (lengths : cells.length = addresses.length)
    (h : (m.stack ++ addresses.map m.mem).mapM
      (fun w => match w with | .val v => some v.val | .slot _ => none) = some (stack ++ cells)) :
    m.stack = stack.map observedWord ∧ addresses.map m.mem = cells.map observedWord := by
  have raw : m.stack ++ addresses.map m.mem = stack.map observedWord ++ cells.map observedWord := by
    simpa only [List.map_append] using numeric_snapshot _ _ h
  have lengths' : m.stack.length + addresses.length = stack.length + cells.length := by
    simpa only [List.length_append,List.length_map] using congrArg List.length raw
  have same : m.stack.length = (stack.map observedWord).length := by
    rw [List.length_map]
    omega
  exact List.append_inj raw same

/-- info: 'Solidity.Backend.InternalFlow.numeric_snapshot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms numeric_snapshot
/-- info: 'Solidity.Backend.InternalFlow.numeric_stack_cells' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms numeric_stack_cells

end Solidity.Backend.InternalFlow
