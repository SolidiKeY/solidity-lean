import Solidity.Yul.Composition.Concrete
import Solidity.Source.StateExamples

/-! Inhabited cross-component witnesses, including a journaled storage write.
Byte materialization uses runtime-supplied bytes as code constants; this is not
RETURNDATACOPY lowering. No compiler/source theorem is inferred. -/
namespace Solidity.Yul.Composition.Controls
open Solidity.Source
open Solidity.Source.StateExamples

/-- Nonempty supplied frame operations affecting caller account: slot7 becomes42 and nonce grows. -/
def writes : List (Op D₀ LW LW) :=
  [.account (addr 1) fun a => { a with nonce := a.nonce + 1, storage := a.storage.write countPath (.int 42 (by decide)) }]

def callerLog : Solidity.Yul.World.Log := ⟨addr 1, ⟨0, by decide⟩, #v[], [0x11]⟩
def entry : Solidity.Yul.World.Effects D₀ LW LW := ⟨s₀, [callerLog], [0xff]⟩
def memory : Solidity.Backend.Environment.Slice := ⟨[Solidity.uintOfNat 99], fun _ => 0xee⟩

def revertedCopy := completeAndCopy entry (addr 2) (addr 1) ⟨0, by decide⟩ [] false
  writes [callerLog] (.revert [0xab,0xcd]) 0 2 31 memory

def successfulCopy := completeAndCopy entry (addr 2) (addr 1) ⟨0, by decide⟩ [] false
  writes [callerLog] (.success [0xab,0xcd]) 0 2 31 memory

/-- The adapter executes, retaining caller log, rolled-back slot7/nonce0 and
copying bytesab/cd across31/32, with sentinels untouched. -/
def summary (result : Option (Solidity.Yul.World.Effects D₀ LW LW ×
    Solidity.Backend.Environment.Slice)) : Option (List Nat) := result.map fun (e,m) =>
  [e.execution.world.accounts (addr 1) |>.nonce,
   ((e.execution.world.accounts (addr 1)).storage.read countPath |>.bind Val.word |>.map Fin.val).getD 999,
   e.logs.length, m.memory 30 |>.toNat, m.memory 31 |>.toNat, m.memory 32 |>.toNat, m.memory 33 |>.toNat, m.stack.length]

theorem reverted_witness : summary revertedCopy = some [0,7,1,238,171,205,238,1] := by decide +kernel
theorem success_witness : summary successfulCopy = some [1,42,2,238,171,205,238,1] := by decide +kernel
theorem rollback_discriminates : summary revertedCopy ≠ summary successfulCopy := by decide +kernel
example : (completeAndCopy entry (addr 2) (addr 1) ⟨0, by decide⟩ [] false
    writes [callerLog] (.revert [0xab,0xcd]) 3 0 31 memory).isNone = true := by decide +kernel

#print axioms reverted_witness
#print axioms success_witness
#print axioms rollback_discriminates
end Solidity.Yul.Composition.Controls
