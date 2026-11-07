import Solidity.Yul.World.Frames
import Solidity.Yul.Compilation.Slices
import Solidity.Backend.Environment.ByteConstants

/-!
# Concrete producer-bound composition boundary

Consumes exact VY4 frame completion and VY3 numeric target slices. Copy code
uses the existing byte-addressed target executor, not a new memory semantics.
Supplied world operations/outcome are explicit inputs, not proven Yul execution.
Materialization constructs PUSH/MSTORE8 code from the supplied bytes; it is
not RETURNDATACOPY lowering and its target executor omits gas/stack exceptions.
This module does not assert source/target adequacy or admission coverage.
-/
namespace Solidity.Yul.Composition
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Source

/-- Complete the actual supplied frame, select its strict returndata window,
then execute real byte-materialization instructions in caller target memory.
`none` retains bounds/execution failure; no missing window becomes empty. -/
def completeAndCopy {D : Layout} {L T : Address → Solidity.Source.SPath → STy}
    (entry : Solidity.Yul.World.Effects D L T) (a c : Address) (v : Word) (input : Bytes)
    (static : Bool) (ops : List (Op D L T)) (logs : List Solidity.Yul.World.Log) (outcome : Outcome)
    (offset size destination : Nat) (caller : Solidity.Backend.Environment.Slice) :
    Option (Solidity.Yul.World.Effects D L T × Solidity.Backend.Environment.Slice) :=
  let completed := Solidity.Yul.World.complete entry a c v input static ops logs outcome
  (Solidity.Yul.World.returnWindow completed.returndata offset size).bind fun bytes =>
    (Solidity.Backend.Environment.runData (Solidity.Backend.Environment.materialize destination bytes) caller).map fun copied =>
      (completed, copied)

/-- Exact VY3 slice family used by the consumer; indices are producer arities. -/
def literalSum (a b : UInt8) : Solidity.Yul.Compilation.Slice 0 1 :=
  (Solidity.Yul.Compilation.literalPair a b).comp Solidity.Yul.Compilation.addWords

end Solidity.Yul.Composition
