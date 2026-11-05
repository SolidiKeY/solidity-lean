import Solidity.Theorems
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Typing.Constructibility

/-! Clean-tail-dependent behavior with a reachable dirty-tail countercontrol. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics
local instance : InContract := ⟨Tokens⟩
open scoped Scoped

def tailProgram : Prog Tokens [] [] :=
  sol[Tokens]{ tokens.push(); assert(tokens[tokens.length - 1].value == 0); }

def tailFormula : Fml Tokens [] := .modal .box tailProgram .nil .tt

theorem tail_clean_valid : ValidTail .clean tailFormula := by
  show Fml.Valid dl[Tokens]{ cleanTail(storage) = true →
    [ tokens.push(); assert(tokens[tokens.length - 1].value == 0); ] true }
  sol_prove

theorem tail_clean_status : (Prog.run (State.init Tokens) tailProgram).toOption.isSome = true := by
  decide +kernel

theorem tail_clean_source : ∃ o, Prog.run (State.init Tokens) tailProgram = .ok o := by
  have hp : (Prog.run (State.init Tokens) tailProgram).toOption.isSome = true := tail_clean_status
  cases hr : Prog.run (State.init Tokens) tailProgram with
  | ok o => exact ⟨o, rfl⟩
  | error e => rw [hr] at hp; cases hp

theorem tail_clean_main : holds (State.init Tokens) tailFormula :=
  Main.cleanTail_holds tail_clean_valid (State.init Tokens) (Storage.init_cleanTail Tokens)

def dirtyTailState : State Tokens [] := { State.init Tokens with storage := Tokens.dangling }

theorem dirty_tail_reachable : Reachable Tokens dirtyTailState.storage := dangling_slot_reachable

theorem dirty_tail_not_clean : ¬ dirtyTailState.storage.CleanTail := by
  simp only [dirtyTailState, Tokens.dangling, Storage.CleanTail, SFields.All, SVal.All,
    SList.All, SVec.All, cleanTailH, SList.OrdinaryDefault, SList.fold,
    ordinaryDefaultFold, and_true, and_self]
  decide +kernel

theorem tail_dirty_status : (Prog.run dirtyTailState tailProgram).isPanic = true := by
  decide +kernel

theorem tail_dirty_source : Prog.run dirtyTailState tailProgram = .error .panic := by
  have hp : (Prog.run dirtyTailState tailProgram).isPanic = true := tail_dirty_status
  cases hr : Prog.run dirtyTailState tailProgram with
  | ok o => rw [hr] at hp; cases hp
  | error e =>
    cases e <;> first | rfl | (rw [hr] at hp; cases hp)

theorem tail_dirty_frames_panic :
    (Prog.runFrames dirtyTailState tailProgram Frames.nil).isPanic = true := by
  decide +kernel

theorem tail_premise_cannot_be_erased : ¬ Fml.Valid tailFormula :=
  fun h => Modality.afterRunTR_not_panic (h dirtyTailState) tail_dirty_frames_panic

end Solidity.Assurance.NonVacuityH28
