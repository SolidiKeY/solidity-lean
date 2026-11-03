import Solidity.Yul.World.DelegateSuccessOutput

/-! A distinct live output object, arbitrary-prefix specialization inherited
from the checked ordinary-revert controls, and the actual successful write.
No old fixed `before` encoding is substituted for this two-entry journal. -/
namespace Solidity.Yul.World.DelegateSuccessWitness
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.DelegatePhysical
open Solidity.Yul.World.DelegateRevertWitness (source heap placement inputEntry outputEntry memory loaded reads)
open Solidity.Yul.World.DelegateRevertControls (residue encoding plan observer)
open Solidity.Yul.World.DelegateSuccessBoundary (completed)
open Solidity.Yul.World.DelegateSuccessPort (heap_eq)

def result (G : Glob env) := completed (source G) residue encoding plan observer

def run (G : Glob env) := DelegateSuccessPort.run G 0 (by decide) (source G)
  DelegateChecks.sender DelegateChecks.target DelegateChecks.value 10000 (by decide) rfl
  residue rfl encoding plan (Option.some_get DelegateRevertControls.ready).symm observer rfl
  (memory G) 160 4 (loaded G) (placement G) (outputEntry G) 1 0 2

def expected (G : Glob env) := HeapOutputTransport.image (result G)
  (heap G) (heap_eq (source G) residue encoding plan observer)
  (placement G) (outputEntry G) (memory G) 1 [0x11,0x22]

theorem run_exact (G : Glob env) : run G=some (.ok (.success ReturningCall.output),expected G) := by
  apply DelegateSuccessPort.argument_copy
  · change (3 : Nat)≤4
    decide
  · exact (reads G).1
  · exact (reads G).2

def automatic (G : Glob env) := DelegateSuccessOutput.run G 0 (by decide) (source G)
  DelegateChecks.sender DelegateChecks.target DelegateChecks.value 10000 (by decide) rfl
  residue rfl encoding plan (Option.some_get DelegateRevertControls.ready).symm observer rfl
  (memory G) 160 4 (loaded G) (placement G) (outputEntry G) 1 2

theorem automatic_exact (G : Glob env) : automatic G=some (.ok (.success ReturningCall.output),expected G) := by
  apply DelegateSuccessOutput.run_exact
  · change (3 : Nat)≤4
    decide
  · exact (reads G).1
  · exact (reads G).2

/-- Full journals grow on success, in contrast to the retained ordinary revert. -/
theorem successful_effects (G : Glob env) :
    (((result G).1.1.1.2.ex.world.accounts account).storage.read flagPath=some (.bool true)) ∧
    (result G).1.1.1.2.ex.journal.length=7 ∧
    (result G).1.1.2.journal.length=3 ∧ (result G).1.2.journal.length=3 ∧
    (result G).2.trace=observer.trace ∧ (result G).2.effects.returndata=ReturningCall.output := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem different_prefix (G : Glob env) :
    encoding.journal.length=2 ∧ before.journal.length=1 ∧
    (source G).2.ex.journal.length=6 ∧ residue.journal.length=2 := ⟨rfl,rfl,rfl,rfl⟩

theorem success_not_rollback (G : Glob env) :
    (((result G).1.1.1.2.ex.world.accounts account).storage.read flagPath)≠
      (((DelegateRevertPort.completed G (source G) residue encoding observer).1.1.1.2.ex.world.accounts account).storage.read flagPath) := by
  change (some (.bool true) : Option (Source.Val env.layout (env.cellTy flagPath)))≠some (.bool false)
  intro same
  cases same

def after (G : Glob env) := DelegateRevertHeap.copied (changed (source G) account) (outputEntry G) 1 [0x11,0x22]

theorem full_image (G : Glob env) : expected G=(result G,
    some ((Solidity.Backend.Environment.writeBytes (memory G) 289 [0x11,0x22],after G),
      ((result G).1.1.2,(result G).1.2),(result G).2)) := rfl

theorem aliases (G : Glob env) :
    (Source.bytesOfRV (E:=env) ReturningCall.parentFrame 1 (.val ((after G).1.get (.there .here)))).run (after G)=
      (.ok [0xa1,0x11,0x22,0xa4],after G) ∧
    (Source.bytesOfRV (E:=env) ReturningCall.parentFrame 1 (.val ((after G).1.get (.there (.there .here))))).run (after G)=
      (.ok [0xa1,0x11,0x22,0xa4],after G) ∧
    (Source.bytesOfRV (E:=env) ReturningCall.parentFrame 1 (.val ((after G).2.fnLocals.2.get .here))).run (after G)=
      (.ok [0xa1,0x11,0x22,0xa4],after G) := ⟨rfl,rfl,rfl⟩

theorem input_untouched (G : Glob env) : (after G).2.heap.get 0=(source G).2.heap.get 0 :=
  DelegateRevertHeap.other (changed (source G) account) (outputEntry G) 1 [0x11,0x22] 0 (show (0 : Nat)≠1 from by decide)

theorem exact_end (G : Glob env) :
    DelegateSuccessPort.run G 0 (by decide) (source G) DelegateChecks.sender DelegateChecks.target
      DelegateChecks.value 10000 (by decide) rfl residue rfl encoding plan
      (Option.some_get DelegateRevertControls.ready).symm observer rfl (memory G) 160 4 (loaded G)
      (placement G) (outputEntry G) 1 32 0=
    some (.ok (.success ReturningCall.output),HeapOutputTransport.image (result G) (heap G)
      (heap_eq (source G) residue encoding plan observer) (placement G) (outputEntry G) (memory G) 1 []) := by
  apply DelegateSuccessPort.exact_end_zero
  · change (1 : Nat)≤4
    decide
  · exact (reads G).1
  · exact (reads G).2

theorem invalid_zero (G : Glob env) :
    DelegateSuccessPort.run G 0 (by decide) (source G) DelegateChecks.sender DelegateChecks.target
      DelegateChecks.value 10000 (by decide) rfl residue rfl encoding plan
      (Option.some_get DelegateRevertControls.ready).symm observer rfl (memory G) 160 4 (loaded G)
      (placement G) (outputEntry G) 1 33 0=some (.ok (.success ReturningCall.output),(result G,none)) :=
  DelegateSuccessPort.out_of_source_zero G 0 (by decide) (source G) DelegateChecks.sender DelegateChecks.target
    DelegateChecks.value 10000 (by decide) rfl residue rfl encoding plan
    (Option.some_get DelegateRevertControls.ready).symm observer rfl (memory G) 160 4 (loaded G)
    (placement G) (outputEntry G) 1

theorem stale_buffer : returnWindow observer.effects.returndata 0 4=none ∧
    returnWindow ReturningCall.output 0 4=some [0x11,0x22,0x33,0x44] := ⟨by decide,by decide⟩

theorem after_memOK (G : Glob env) : Source.MemOK env (heap G).ty (after G) :=
  DelegateRevertHeap.memOK (changed (source G) account) (outputEntry G) 1 [0x11,0x22] (heap G).ty
    (by
      have h:=DelegateRevertWitness.source_memOK G
      exact ⟨⟨⟨h.1.1.heap,h.1.1.le⟩,h.1.2⟩,h.2⟩)
end Solidity.Yul.World.DelegateSuccessWitness
