import Solidity.Yul.Builtins
import Solidity.Yul.World.AdapterRules
import Solidity.Yul.World.ByteMemory
/-! Intrinsic returndata leaf over the existing caller-local last buffer.
Operands are already evaluated; size reuses Source.toWord. Exact natural
size needs the real word-range premise. Unsupported leaf constructors return
none, not admission refusal or an EVM halt certificate. Source last-call
origin/noninterference and physical heap writeback remain producer obligations. -/
namespace Solidity.Yul.World
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
variable {D : Layout} {L T : Address → Solidity.Source.SPath → STy} {Memory : Type}

def returndataBuiltin {a r : Nat} (builtin : Solidity.Yul.Builtin a r)
    (port : BytePort Memory) (before : AdapterRules.Configuration Memory D L T)
    (args : Fin a → Word) : Option (Vector Word r × AdapterRules.Configuration Memory D L T) :=
  match builtin with
  | .returndatasize => some (#v[toWord before.observed.effects.returndata.length],before)
  | .returndatacopy =>
    (copyReturndata port before.observed.effects before.memory (args 0) (args 1) (args 2)).map
      (fun memory => (#v[], {before with memory := memory}))
  | _ => none

theorem returndatasize_binding (port : BytePort Memory) (before : AdapterRules.Configuration Memory D L T)
    (args : Fin 0 → Word) :
    returndataBuiltin .returndatasize port before args =
      some (#v[toWord before.observed.effects.returndata.length],before) := by
  first | rfl | decide

theorem returndatacopy_binding (port : BytePort Memory) (before : AdapterRules.Configuration Memory D L T)
    (args : Fin 3 → Word) (bytes : Bytes) (memory : Memory)
    (source : returnWindow before.observed.effects.returndata (args 1).val (args 2).val = some bytes)
    (destination : port.store before.memory (args 0) bytes = some memory) :
    returndataBuiltin .returndatacopy port before args =
      some (#v[],{before with memory := memory}) := by
  first | simp only [returndataBuiltin,copyReturndata_exact _ _ _ _ _ _ _ source,destination,Option.map_some] | decide | omega | rfl

theorem returndatacopy_out_of_bounds (port : BytePort Memory) (before : AdapterRules.Configuration Memory D L T)
    (args : Fin 3 → Word)
    (outside : before.observed.effects.returndata.length < (args 1).val + (args 2).val) :
    returndataBuiltin .returndatacopy port before args = none := by
  first | simp only [returndataBuiltin,copyReturndata_bounds _ _ _ _ _ _ outside,Option.map_none] | decide | omega | rfl
theorem returndatasize_word_exact (before : AdapterRules.Configuration Memory D L T)
    (bound : before.observed.effects.returndata.length < 2^256) :
    (toWord before.observed.effects.returndata.length).val = before.observed.effects.returndata.length := by
  first | simp only [toWord,Nat.mod_eq_of_lt bound] | decide | omega | rfl

theorem returndatacopy_observer (port : BytePort Memory) (before : AdapterRules.Configuration Memory D L T)
    (args : Fin 3 → Word) (out : Vector Word 0 × AdapterRules.Configuration Memory D L T)
    (completed : returndataBuiltin .returndatacopy port before args = some out) :
    out.2.observed = before.observed := by
  cases copied : copyReturndata port before.observed.effects before.memory (args 0) (args 1) (args 2) with
  | none =>
    simp only [returndataBuiltin,copied,Option.map_none] at completed
    cases completed
  | some memory =>
    simp only [returndataBuiltin,copied,Option.map_some,Option.some.injEq] at completed
    cases completed
    rfl
namespace TargetMemory
theorem returndata_copy_readback (before : AdapterRules.Configuration Solidity.Backend.Environment.Memory D L T)
    (args : Fin 3 → Word) (bytes : Bytes)
    (source : returnWindow before.observed.effects.returndata (args 1).val (args 2).val = some bytes)
    (destination : (args 0).val + bytes.length ≤ 2^256) :
    (returndataBuiltin .returndatacopy port before args).map
      (fun out => Solidity.Backend.Environment.readMemory out.2.memory (args 0).val bytes.length) = some bytes := by
  simpa only [returndataBuiltin,Option.map_map,Function.comp_def] using
    copy_readback before.observed.effects before.memory (args 0) (args 1) (args 2) bytes source destination
theorem returndata_copy_frame (before : AdapterRules.Configuration Solidity.Backend.Environment.Memory D L T)
    (args : Fin 3 → Word) (bytes : Bytes) (i : Nat)
    (source : returnWindow before.observed.effects.returndata (args 1).val (args 2).val = some bytes)
    (destination : (args 0).val + bytes.length ≤ 2^256)
    (outside : i < (args 0).val ∨ (args 0).val + bytes.length ≤ i) :
    (returndataBuiltin .returndatacopy port before args).map (fun out => out.2.memory i) = some (before.memory i) := by
  simpa only [returndataBuiltin,Option.map_map,Function.comp_def] using
    copy_frame before.observed.effects before.memory (args 0) (args 1) (args 2) bytes i source destination outside
end TargetMemory
end Solidity.Yul.World
