import Solidity.Yul.World.ReturnSize
import Solidity.Yul.World.CreationAddressingChecks

/-! Buffer-size/load/copy combinations; not compiler last-call freedom. -/
namespace Solidity.Yul.World.ReturnSizeChecks
open Solidity.Source
open Solidity.Source.StateExamples
open Solidity.Yul.World.Checks
open Solidity.Yul.World.AdapterChecks (observed memory parent done)

theorem last_call_size :
    returndataSize (done false).effects = some (toWord 3) ∧
    returndataSize (done true).effects = some (toWord 3) ∧
    returndataSize (freshChild (done true).effects) = some (toWord 0) := ⟨rfl,rfl,rfl⟩

def first := finishObserved observed parent ⟨havoc,calleeTrace,.success [17,34,51,68]⟩
def last := finishObserved first
  (childContext first.effects.execution parent .call (addr 3) (toWord 0) [])
  ⟨callOps,calleeTrace,.revert [253,254]⟩

theorem overwritten_size :
    returndataSize first.effects = some (toWord 4) ∧
    returndataSize last.effects = some (toWord 2) ∧
    last.effects.execution = first.effects.execution ∧
    last.trace = rollbackTrace (callerTrace ++ calleeTrace) calleeTrace := by
  have he := congrArg (fun e : Effects D₀ LW LW => e.execution)
    (finishObserved_revert first
      (childContext first.effects.execution parent .call (addr 3) (toWord 0) [])
      callOps calleeTrace [253,254]).1
  exact ⟨rfl,rfl,he,rfl⟩

theorem size_copy_boundary :
    copyReturndata TargetMemory.port last.effects memory (toWord 31) (toWord 2) (toWord 0) =
      TargetMemory.port.store memory (toWord 31) [] ∧
    copyReturndata TargetMemory.port last.effects memory (toWord 31) (toWord 3) (toWord 0) = none ∧
    (copyReturndata TargetMemory.port last.effects memory (toWord 31) (toWord 0) (toWord 2)).map
      (fun m => (Solidity.Backend.Environment.readMemory m 31 2,m 30,m 33)) =
      some ([253,254],255,255) := by
  exact ⟨rfl,returndataSize_copy_refusal _ _ _ (toWord 2) _ _ _ rfl (by decide),rfl⟩

theorem size_negative :
    returndataSize last.effects ≠ some (toWord 6) ∧
    returndataSize last.effects ≠ some (toWord 4) ∧
    last.effects.returndata ≠ [17,34,51,68,253,254] := by decide

/-- Symbolic boundary lists: proofs use length_replicate, never allocate or
evaluate these enormous lists. They are NOT reachable EVM-memory witnesses. -/
theorem abstract_word_boundaries :
    checkedReturnSize (List.replicate (2^256) 0) = none ∧
    checkedReturnSize (List.replicate (2^256-1) 0) = some ⟨2^256-1,by decide⟩ := by
  constructor
  · apply checkedReturnSize_refused
    simp only [List.length_replicate,Nat.lt_irrefl,not_false_eq_true]
  · simp only [checkedReturnSize,List.length_replicate,show 2^256-1 < 2^256 by decide,dite_true]

theorem creation_sizes (F : Solidity.Roadmap.Fixed) (salt : Option Solidity.Roadmap.Word) :
    returndataSize (CreationAddressingChecks.result F salt false).observed.effects = some (toWord 0) ∧
    (CreationAddressingChecks.result F salt false).initialization = .success [96,0] ∧
    returndataSize (CreationAddressingChecks.result F salt true).observed.effects = some (toWord 2) := ⟨rfl,rfl,rfl⟩

theorem rule_use : AdapterRules.Box (ReturnSizeRules.Step (toWord 2))
    (fun after => after = ⟨last,memory⟩ ∧ (toWord 2).val = after.observed.effects.returndata.length)
    ⟨last,memory⟩ := ReturnSizeRules.size_rule _ _ rfl

theorem wrong_size_refused : ¬ ReturnSizeRules.Step (toWord 6)
    (⟨last,memory⟩ : AdapterRules.Configuration _ D₀ LW LW) ⟨last,memory⟩ := by
  intro h
  have he := h.1
  contradiction

end Solidity.Yul.World.ReturnSizeChecks
