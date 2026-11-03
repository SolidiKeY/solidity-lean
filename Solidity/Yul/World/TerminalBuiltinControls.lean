import Solidity.Yul.World.TerminalBuiltin
import Solidity.Yul.World.AdapterChecks
namespace Solidity.Yul.World.TerminalBuiltinControls
open Solidity.Source Solidity.Source.StateExamples
open Solidity.Roadmap (Word)
open Solidity.Yul.World.AdapterChecks
open Solidity.Backend.Environment (Memory writeBytes)

def payload : Solidity.Roadmap.Bytes := [0xde,0xad,0,0xff]
def image : Memory := writeBytes memory 31 payload
def args : Fin 2 → Word := fun i => (#v[toWord 31,toWord 4]).get i
def zeroArgs : Fin 2 → Word := fun i => (#v[toWord 31,toWord 0]).get i
def overflowArgs : Fin 2 → Word := fun i => (#v[⟨2^256-1,by decide⟩,toWord 2]).get i
def missing : BytePort Memory := {TargetMemory.port with load := fun _ _ _ => none}

theorem full_payloads : terminalBuiltin .«return» TargetMemory.port image args = some (.success payload) ∧
    terminalBuiltin .«revert» TargetMemory.port image args = some (.revert payload) := by
  first | decide | exact ⟨rfl,rfl⟩
theorem empty_outcomes_distinct : terminalBuiltin .«return» TargetMemory.port image zeroArgs = some (.success []) ∧
    terminalBuiltin .«revert» TargetMemory.port image zeroArgs = some (.revert []) := by
  first | decide | exact ⟨rfl,rfl⟩
theorem stop_without_memory : terminalBuiltin .stop missing image (fun i => Fin.elim0 i) = some (.success []) := by
  first | rfl | decide
theorem missing_and_overflow : terminalBuiltin .«revert» missing image args = none ∧
    terminalBuiltin .«revert» TargetMemory.port image overflowArgs = none := by
  first | decide | exact ⟨rfl,rfl⟩
theorem truncated_payload_refused : terminalBuiltin .«revert» TargetMemory.port image args ≠ some (.revert [0xde,0xad,0]) := by
  first | decide | rfl
theorem invalid_unhandled : terminalBuiltin .invalid TargetMemory.port image (fun i => Fin.elim0 i) = none := by
  first | rfl | decide
end Solidity.Yul.World.TerminalBuiltinControls
