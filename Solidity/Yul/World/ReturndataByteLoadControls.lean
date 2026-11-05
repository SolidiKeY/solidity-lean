import Solidity.Yul.World.ReturndataByteLoad
import Solidity.Yul.World.AdapterChecks

/-! Concrete copy/bounds witnesses plus a conditional use of the exact P6
signature. No Producer instance or reachable callee is supplied by this fixture. -/
namespace Solidity.Yul.World.ReturndataByteLoadControls
open Solidity.Source
open Solidity.Roadmap (Word)
open Solidity.Backend
open Solidity.Yul.World.AdapterChecks (observed memory)

def value : Fin Evm.W := ⟨0x1122334455667788,by decide⟩
def data : List UInt8 := [0xaa,0xbb,0xcc] ++ Semantics.wordBytes value.val ++ [0xef]
def entry := {observed.effects with returndata := data}
def after := Environment.writeBytes memory 64 (Semantics.wordBytes value.val)

theorem window : returnWindow entry.returndata 3 32 = some (Semantics.wordBytes value.val) := by
  first | decide | rfl | omega

theorem copied : copyReturndata TargetMemory.port entry memory (toWord 64) (toWord 3) (toWord 32) = some after := by
  rw [copyReturndata_exact _ _ _ _ _ _ _ window]
  apply TargetMemory.store_exact
  rw [Environment.wordBytes_length]
  decide

/-- Existing concrete copy, conditional byte-target execution, complete outside
frame and saved stack: no scripted load program is presented as a producer. -/
def conditional {code : Nat → Backend.Program}
    (producer : MemoryOps.Physical.ByteWorld.Producer code)
    (frame : Environment.Frame) (tail : List Environment.Word) (room : tail.length+1≤1024) :=
  ReturndataByteLoad.copy_load producer frame entry memory (toWord 64) (toWord 3)
    ⟨2,by decide⟩ value window rfl (by decide) tail room

theorem outside (i : Nat) (h : i<64 ∨ 96≤i) : after i = memory i := by
  apply Environment.writeBytes_frame
  simpa only [Environment.wordBytes_length] using h

theorem exact_end_zero :
    copyReturndata TargetMemory.port entry memory (toWord 64) (toWord 36) (toWord 0) = some memory := by
  first | decide | rfl | omega

theorem out_of_source_zero :
    copyReturndata TargetMemory.port entry memory (toWord 64) (toWord 37) (toWord 0) = none := by
  apply copyReturndata_bounds
  first | decide | rfl | omega

theorem truncated_word_refused :
    copyReturndata TargetMemory.port entry memory (toWord 64) (toWord 5) (toWord 32) = none := by
  apply copyReturndata_bounds
  first | decide | rfl | omega

theorem wrong_word_refused : returnWindow entry.returndata 3 32 ≠ some (Semantics.wordBytes 0) := by
  first | decide | rfl | omega
end Solidity.Yul.World.ReturndataByteLoadControls
