import Solidity.Yul.Builtins
import Solidity.Yul.World.AdapterRules
/-! Intrinsic CALL-family operand binding to the existing world port.
The producer owes reachable code/account/context/static/world adequacy; arbitrary
FrameAnswer operations are NOT certified here. CompletedCall is retained even
when copiedMemory is none. callContinuation is only an optional normal view;
copy refusal still needs the enclosing physical/source-fault rollback adapter.
This is not a Yul runner, G01/G51/compiler or gas/resource certificate. -/
namespace Solidity.Yul.World
open Solidity.Source
open Solidity.Roadmap (Address Word)
variable {D : Layout} {L T : Address → Solidity.Source.SPath → STy} {Memory : Type}
/-- CALL-family operands address the low 160 bits, not a cleaned source local. -/
def calleeAddress (word : Word) : Address :=
  ⟨word.val % 2^160, Nat.mod_lt _ (by decide)⟩
/-- Partial binding retains completion even when output-copy ownership refuses. -/
def callBuiltin {a : Nat} (builtin : Solidity.Yul.Builtin a 1)
    (port : BytePort Memory) (invoke : WorldPort D L T)
    (before : AdapterRules.Configuration Memory D L T) (parent : CallFrame)
    (args : Fin a → Word) : Option (CompletedCall Memory D L T) :=
  match builtin with
  | .call => callAdapter port invoke before.observed before.memory parent .call
      (calleeAddress (args 1)) (args 0) (args 2) (args 3) (args 4) (args 5) (args 6)
  | .staticcall => callAdapter port invoke before.observed before.memory parent .staticcall
      (calleeAddress (args 1)) (args 0) (toWord 0) (args 2) (args 3) (args 4) (args 5)
  | .delegatecall => callAdapter port invoke before.observed before.memory parent .delegatecall
      (calleeAddress (args 1)) (args 0) (toWord 0) (args 2) (args 3) (args 4) (args 5)
  | _ => none

/-- Optional normal view, not a discarded call completion or fault classifier. -/
def callContinuation (result : CompletedCall Memory D L T) :
    Option (Vector Word 1 × AdapterRules.Configuration Memory D L T) :=
  result.copiedMemory.map (fun memory => (#v[callFlag result.outcome],⟨result.observed,memory⟩))

theorem calleeAddress_value (word : Word) : (calleeAddress word).val = word.val % 2^160 := by
  first | rfl | decide
theorem callContinuation_copied (result : CompletedCall Memory D L T) (memory : Memory)
    (copied : result.copiedMemory = some memory) :
    callContinuation result = some (#v[callFlag result.outcome],⟨result.observed,memory⟩) := by
  first | simp only [callContinuation,copied,Option.map_some] | decide | omega | rfl
theorem callContinuation_refused (result : CompletedCall Memory D L T) (refused : result.copiedMemory = none) :
    callContinuation result = none := by
  first | simp only [callContinuation,refused,Option.map_none] | decide | omega | rfl
theorem callBuiltin_static_value (port : BytePort Memory) (invoke : WorldPort D L T)
    (before : AdapterRules.Configuration Memory D L T) (parent : CallFrame)
    (args : Fin 7 → Word) (static : parent.static = true) (value : (args 2).val ≠ 0) :
    callBuiltin .call port invoke before parent args = none := by
  first
  | simp only [callBuiltin,callAdapter_static_value_refusal port invoke before.observed before.memory parent
      (calleeAddress (args 1)) (args 0) (args 2) (args 3) (args 4) (args 5) (args 6) static value]
  | decide | omega | rfl
theorem call_binding (port : BytePort Memory) (invoke : WorldPort D L T)
    (before : AdapterRules.Configuration Memory D L T) (parent : CallFrame) (args : Fin 7 → Word) :
    callBuiltin .call port invoke before parent args = callAdapter port invoke before.observed before.memory parent
      .call (calleeAddress (args 1)) (args 0) (args 2) (args 3) (args 4) (args 5) (args 6) := rfl

theorem staticcall_binding (port : BytePort Memory) (invoke : WorldPort D L T)
    (before : AdapterRules.Configuration Memory D L T) (parent : CallFrame) (args : Fin 6 → Word) :
    callBuiltin .staticcall port invoke before parent args = callAdapter port invoke before.observed before.memory parent
      .staticcall (calleeAddress (args 1)) (args 0) (toWord 0) (args 2) (args 3) (args 4) (args 5) := rfl

theorem delegatecall_binding (port : BytePort Memory) (invoke : WorldPort D L T)
    (before : AdapterRules.Configuration Memory D L T) (parent : CallFrame) (args : Fin 6 → Word) :
    callBuiltin .delegatecall port invoke before parent args = callAdapter port invoke before.observed before.memory parent
      .delegatecall (calleeAddress (args 1)) (args 0) (toWord 0) (args 2) (args 3) (args 4) (args 5) := rfl
end Solidity.Yul.World
