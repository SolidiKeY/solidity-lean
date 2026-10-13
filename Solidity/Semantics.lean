import Solidity.Syntax.Splice

/-!
# The ABI values

What stays untyped (`docs/intrinsic.md`, W10.5): the words of the ABI.  A
value (`PrimVal`, `Value`) is what a call's arguments and returned data are
made of, what the tools take as arguments and print (`#run`,
`#counterexample`), and what a typed value is as a word (`PrimTy.erase`,
`Semantics/Value.lean`); an external call (`ExtKey`) and how it ends
(`ExtResult`) are the transaction's data (`TTx.ext`), which a `try`
decodes at its types; a path's segments (`Seg`) are the side conditions'
path syntax (`Theory/Segs.lean`, `Path.erase`).  The state is typed
(`Semantics/State.lean`): the untyped state, its operations and its run
went at W10.5.6.
-/

namespace Solidity
namespace Semantics

/-- Primitive run-time values — KeY `Prim \extends StValue, MemValue`
(`solidityDLHeader.key`): the values shared by storage and memory. -/
inductive PrimVal where
  | int (v : Int)
  | bool (b : Bool)
  deriving Repr, DecidableEq

/-- Stack values *are* primitive values: KeY gives primitive-typed
program variables the `Prim` subsorts directly, with no separate stack
sort. `Value` stays as the interpreter-facing name. -/
abbrev Value := PrimVal

namespace Value
export PrimVal (int bool)
end Value

/-- One step of a storage path: a field or an `at(i)` selector
(array index or mapping key). -/
inductive Seg where
  | field (name : Name)
  | at (i : Int)
  deriving Repr, DecidableEq

/-- How an external call ends, as its caller sees it: it returns this data,
or it reverts with `Error(string)`, with `Panic(uint)` and this code, or in
another way. -/
inductive ExtResult where
  | ok (data : List Value)
  | error
  | panic (code : Value)
  | other
  deriving Repr, DecidableEq

/-- An external call as it is made: the callee's address, the function, the
arguments' values. -/
structure ExtKey where
  addr : Int
  fn : String
  args : List Value
  deriving Repr, DecidableEq

end Semantics

open Semantics in
/-- The external call a `send` makes: `amt` to `addr` with empty calldata,
which reaches the recipient's `receive` (or fallback) function. -/
def sendKey (addr amt : Int) : ExtKey := ⟨addr, "", [.int amt]⟩

end Solidity
