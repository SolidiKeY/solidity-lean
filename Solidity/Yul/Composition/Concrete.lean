import Solidity.Yul.Composition.Interface

/-! Concrete cross-component laws. The outcome/operation lists are actual
inputs to VY4's completion function; no premise asserts source adequacy. -/
namespace Solidity.Yul.Composition
open Solidity.Roadmap (Address Word Bytes)
open Solidity.Source
variable {D : Layout} {L T : Address → Solidity.Source.SPath → STy}

/-- A failed world frame rolls back its typed journal and logs; its exact
bounded revert bytes are materialized by the concrete target instructions.
Caller stack and memory outside the selected interval survive. -/
theorem revert_copy (entry : Solidity.Yul.World.Effects D L T)
    (a c : Address) (v : Word) (input : Bytes) (static : Bool)
    (ops : List (Op D L T)) (logs : List Solidity.Yul.World.Log) (data bytes : Bytes)
    (offset size destination : Nat) (caller : Solidity.Backend.Environment.Slice)
    (window : Solidity.Yul.World.returnWindow data offset size = some bytes)
    (fits : destination + bytes.length ≤ 2 ^ 256) :
    completeAndCopy entry a c v input static ops logs (.revert data)
      offset size destination caller =
      some (⟨entry.execution, entry.logs, data⟩,
        { caller with memory := Solidity.Backend.Environment.writeBytes caller.memory destination bytes }) := by
  simp only [completeAndCopy, Solidity.Yul.World.complete_revert, window,
    Option.bind_some, Solidity.Backend.Environment.materialize_correct bytes destination caller fits,
    Option.map_some]

/-- The physical selected bytes and every outside byte are independently
specified after copying; there is no arbitrary final-memory equality. -/
theorem copied_window_and_frame (memory : Solidity.Backend.Environment.Memory)
    (bytes : Bytes) (destination index : Nat)
    (outside : index < destination ∨ destination + bytes.length ≤ index) :
    Solidity.Backend.Environment.readMemory
      (Solidity.Backend.Environment.writeBytes memory destination bytes) destination bytes.length = bytes ∧
    Solidity.Backend.Environment.writeBytes memory destination bytes index = memory index :=
  ⟨Solidity.Backend.Environment.read_written bytes destination memory,
   Solidity.Backend.Environment.writeBytes_frame bytes destination index memory outside⟩

/-- A reverted child followed by a successful caller frame uses the restored
journal, caller log prefix and the last completion's bytes. -/
theorem caught_then_success (entry : Solidity.Yul.World.Effects D L T)
    (a c : Address) (v : Word) (input : Bytes) (static : Bool)
    (failedOps callerOps : List (Op D L T))
    (failedLogs callerLogs : List Solidity.Yul.World.Log) (failure result : Bytes) :
    Solidity.Yul.World.complete
      (Solidity.Yul.World.complete entry a c v input static failedOps failedLogs (.revert failure))
      a c v input static callerOps callerLogs (.success result) =
      ⟨entry.execution.run callerOps, entry.logs ++ callerLogs, result⟩ := by
  rw [Solidity.Yul.World.complete_revert]
  rfl

/-- The caught revert window can itself be sliced before a caller copy;
both strict bounds remain premises, including zero-size bounds. -/
theorem nested_revert_window (entry : Solidity.Yul.World.Effects D L T)
    (a c : Address) (v : Word) (input : Bytes) (static : Bool)
    (ops : List (Op D L T)) (logs : List Solidity.Yul.World.Log) (data outer inner : Bytes)
    (offset size subOffset subSize : Nat)
    (first : Solidity.Yul.World.returnWindow data offset size = some outer)
    (second : Solidity.Yul.World.returnWindow outer subOffset subSize = some inner) :
    Solidity.Yul.World.returnWindow
      (Solidity.Yul.World.complete entry a c v input static ops logs (.revert data)).returndata
      (offset + subOffset) subSize = some inner := by
  rw [Solidity.Yul.World.complete_data]
  exact Solidity.Yul.World.returnWindow_compose data outer inner offset size subOffset subSize first second

/-- Concrete VY3 ADD trace with arbitrary caller tail, not just arity. -/
theorem literalSum_run (a b : UInt8) (tail : Solidity.Backend.Scalar.Stack) :
    Solidity.Backend.Scalar.run (literalSum a b).code tail =
      some ((BitVec.ofNat 256 a.toNat + BitVec.ofNat 256 b.toNat) :: tail) := by
  simp only [literalSum, Solidity.Yul.Compilation.Slice.comp,
    Solidity.Yul.Compilation.literalPair, Solidity.Yul.Compilation.addWords,
    List.cons_append, List.nil_append, Solidity.Backend.Scalar.run, Solidity.Backend.Scalar.step_pushByte,
    Option.bind_some]
  rfl

/-- Negative control: zero-byte RETURNDATACOPY beyond the end still fails. -/
example : Solidity.Yul.World.returnWindow [0xab, 0xcd] 3 0 = none := by decide +kernel
example : Solidity.Yul.World.returnWindow [0xab, 0xcd] 1 1 = some [0xcd] := by decide +kernel
example : Solidity.Backend.Scalar.run (literalSum 250 9).code [99] = some [259,99] := by decide +kernel
example : Solidity.Backend.Scalar.run [.op .ADD] [7] = none := rfl
example : Solidity.Backend.Scalar.run (literalSum 250 9).code [99] ≠ some [3,99] := by decide +kernel

#print axioms revert_copy
#print axioms copied_window_and_frame
#print axioms caught_then_success
#print axioms nested_revert_window
#print axioms literalSum_run
end Solidity.Yul.Composition
