import Solidity.Yul.Builtins
import Solidity.Yul.World.Adapters
/-! Intrinsic terminal-byte binding over existing Outcome and BytePort.
Operands are already evaluated. This leaf only returns an outcome; it does
not perform callee control exit, frame rollback, physical writeback or caller
returndata update. Source/G01/G51/compiler/resource adequacy remains external.
None means unhandled builtin or unavailable memory, not an EVM halt verdict. -/
namespace Solidity.Yul.World
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
variable {Memory : Type}
/-- Outcome-only terminal port leaf; frame halt/rollback remain consumers. -/
def terminalBuiltin {a : Nat} (builtin : Solidity.Yul.Builtin a 0)
    (port : BytePort Memory) (memory : Memory) (args : Fin a → Word) : Option Outcome :=
  match builtin with
  | .stop => some (.success [])
  | .«return» => (port.load memory (args 0) (args 1)).map Outcome.success
  | .«revert» => (port.load memory (args 0) (args 1)).map Outcome.revert
  | _ => none

theorem terminal_stop (port : BytePort Memory) (memory : Memory) (args : Fin 0 → Word) :
    terminalBuiltin .stop port memory args = some (.success []) := by
  first | rfl | decide
theorem terminal_return (port : BytePort Memory) (memory : Memory) (args : Fin 2 → Word) (bytes : Bytes)
    (loaded : port.load memory (args 0) (args 1) = some bytes) :
    terminalBuiltin .«return» port memory args = some (.success bytes) := by
  first | simp only [terminalBuiltin,loaded,Option.map_some] | decide | omega | rfl
theorem terminal_revert (port : BytePort Memory) (memory : Memory) (args : Fin 2 → Word) (bytes : Bytes)
    (loaded : port.load memory (args 0) (args 1) = some bytes) :
    terminalBuiltin .«revert» port memory args = some (.revert bytes) := by
  first | simp only [terminalBuiltin,loaded,Option.map_some] | decide | omega | rfl
theorem terminal_revert_iff (port : BytePort Memory) (memory : Memory) (args : Fin 2 → Word) (outcome : Outcome) :
    terminalBuiltin .«revert» port memory args = some outcome ↔
      ∃ bytes, port.load memory (args 0) (args 1) = some bytes ∧ Outcome.revert bytes = outcome := by
  first | simp only [terminalBuiltin,Option.map_eq_some_iff] | decide | omega | rfl
theorem terminal_return_not_revert (port : BytePort Memory) (memory : Memory) (args : Fin 2 → Word) (bytes : Bytes) :
    terminalBuiltin .«return» port memory args ≠ some (.revert bytes) := by
  intro completed
  simp only [terminalBuiltin] at completed
  obtain ⟨loaded,read,impossible⟩ := Option.map_eq_some_iff.mp completed
  cases impossible
theorem terminal_revert_not_return (port : BytePort Memory) (memory : Memory) (args : Fin 2 → Word) (bytes : Bytes) :
    terminalBuiltin .«revert» port memory args ≠ some (.success bytes) := by
  intro completed
  simp only [terminalBuiltin] at completed
  obtain ⟨loaded,read,impossible⟩ := Option.map_eq_some_iff.mp completed
  cases impossible
theorem terminal_revert_missing (port : BytePort Memory) (memory : Memory) (args : Fin 2 → Word)
    (missing : port.load memory (args 0) (args 1) = none) :
    terminalBuiltin .«revert» port memory args = none := by
  first | simp only [terminalBuiltin,missing,Option.map_none] | decide | omega | rfl
end Solidity.Yul.World
