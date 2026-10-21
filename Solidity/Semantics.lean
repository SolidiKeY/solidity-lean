import Solidity.Syntax.Splice

/-!
# Call data and ABI observations

External-call inputs are typed: `ExtKey` has a bounded receiver and
`CallValue` arguments, each retaining its Solidity type and numeric range.
`PrimTy.Denote` is defined here so the call boundary can use it without
an import cycle.

There is no untyped value: a tool's input or output is a `CallValue`, read
at a type by `CallValue.as?` (`Semantics/Value.lean`). External responses
(`ExtResult`) are ABI words (`Word`, a `uint256`): every word is one, and a word is read
at its local's type when a `try` decodes it (`PrimTy.ofWord?`), where a
`bool` that is neither `0` nor `1` reverts, as solc's decoder does. `Selector` labels describe comparisons and schema
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

/-- Typed values of any primitive type compare. -/
instance PrimTy.decEqSigma : DecidableEq ((K : PrimTy) × K.Denote) := fun a b =>
  match a, b with
  | ⟨K, x⟩, ⟨K', y⟩ =>
    if h : K = K' then by
      subst h
      exact if hx : x = y then isTrue (hx ▸ rfl)
        else isFalse fun e => hx (eq_of_heq (Sigma.mk.inj e).2)
    else isFalse fun e => h (Sigma.mk.inj e).1

instance PrimTy.reprSigma : Repr ((K : PrimTy) × K.Denote) where
  reprPrec v _ := repr v.1 ++ " " ++ (PrimTy.reprDenote v.1).reprPrec v.2 0

namespace Semantics

/-- A selector label for comparison and schema analysis, each at its type:
a state variable (`root`), a struct member (`field`), an array's `uint`
index (`idx`), a mapping's key of its key type (`key`), an array's length
(`len`, KeY's `size`).  A label carries no storage access operation; `Seg`
is the typed segment that projects it. -/
inductive Selector where
  | root (name : Name)
  | field (name : Name)
  | idx (i : PrimTy.uint.Denote)
  | key (k : (K : PrimTy) × K.Denote)
  | len
  deriving Repr, DecidableEq

/-- An ABI word: 256 bits, read as a `uint256`. -/
abbrev Word := PrimTy.uint.Denote

/-- How an external call ends, as its caller sees it: it returns these
words, or it reverts with `Error(string)` and this reason, with
`Panic(uint256)` and this code, or in another way, with this data (bytes,
`docs/semantic-gaps.md`, "Revert data"). -/
inductive ExtResult where
  | ok (data : List Word)
  | error (reason : List UInt8)
  | panic (code : Word)
  | other (data : List UInt8)
  deriving Repr, DecidableEq

/-- A typed value of some primitive type: an argument retains its Solidity
type and that type's range proof, and so does what the tools read and print. -/
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
