import Solidity.Syntax.Splice

/-!
# Call data and ABI observations

External-call inputs are typed: `ExtKey` has a bounded receiver and
`CallValue` arguments, each retaining its Solidity type and numeric range.
`PrimTy.Denote` is defined here so the call boundary can use it without
an import cycle.

`PrimVal`/`Value` is the wire and tool representation, decoded at the
expected type (`PrimTy.ofValue?`, `Semantics/Value.lean`). External responses
(`ExtResult`) remain wire data: a callee can return malformed data, which
`try` must reject. `Selector` labels describe comparisons and schema
analysis; actual path segments are indexed (`Seg`/`Segs` in
`Semantics/Storage.lean`). The state is typed (`Semantics/State.lean`).
-/

namespace Solidity

/-- The values of the primitive type `p`. -/
def PrimTy.Denote : PrimTy → Type
  | .bool => Bool
  | .uint => {n : Int // PrimTy.uint.inRange n = true}
  | .int => {n : Int // PrimTy.int.inRange n = true}

namespace PrimTy

instance decEqDenote : (p : PrimTy) → DecidableEq p.Denote
  | .bool => inferInstanceAs (DecidableEq Bool)
  | .uint => inferInstanceAs (DecidableEq {n : Int // PrimTy.uint.inRange n = true})
  | .int => inferInstanceAs (DecidableEq {n : Int // PrimTy.int.inRange n = true})

instance reprDenote : (p : PrimTy) → Repr p.Denote
  | .bool => inferInstanceAs (Repr Bool)
  | .uint => ⟨fun n _ => repr n.1⟩
  | .int => ⟨fun n _ => repr n.1⟩

end PrimTy

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

/-- A selector label for comparison and schema analysis. A label carries no
storage access operation; `Seg` is the typed segment that projects it. -/
inductive Selector where
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

/-- An argument retains its Solidity type and that type's range proof. -/
inductive CallValue where
  | bool (value : Bool)
  | uint (value : PrimTy.uint.Denote)
  | int (value : PrimTy.int.Denote)
  deriving Repr, DecidableEq

/-- Package a typed argument without passing through an ABI erasure. -/
def CallValue.ofTyped : {p : PrimTy} → p.Denote → CallValue
  | .bool, v => .bool v
  | .uint, v => .uint v
  | .int, v => .int v

/-- An external call as it is made: the callee's address, the function, the
arguments' values. -/
structure ExtKey where
  addr : PrimTy.uint.Denote
  fn : String
  args : List CallValue
  deriving Repr, DecidableEq

end Semantics

open Semantics in
/-- The external call a `send` makes: `amt` to `addr` with empty calldata,
which reaches the recipient's `receive` (or fallback) function. -/
def sendKey (addr amt : PrimTy.uint.Denote) : ExtKey := ⟨addr, "", [.uint amt]⟩

end Solidity
