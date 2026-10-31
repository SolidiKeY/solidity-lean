import Solidity.Semantics.AbiEntry
import Solidity.Syntax.Elab.Lower
import Solidity.RevertBytes

/-!
# Upstream replay: typed ABI entry decoding

The bridge from an admitted source declaration to the typed entry decoder of
`Semantics/AbiEntry.lean`. Each parameter's shape is read from its typed
declaration and width rows (`AbiTy.of`); its location from the declaration
(`calldata`, else `memory`; a primitive is a value). The decoder then runs on
the actual calldata (selector included) and decides, for ABI coder v2:

* `revert`: an entry check fails; solc reverts with empty data before the
  body (`AbiEntry.verdict_revert_iff`).
* `run bytes`: the body runs on the decoded values, given to the existing
  typed decoder as their canonical encoding `bytes`. For a calldata parameter
  the eager value is also what every lazy read yields
  (`AbiEntry.eager_cref`). The original calldata remains the reported
  observation; physical calldata observers (`msg.data`, assembly, slices) are
  refused by the adapter as before.
* `blocked`: a named refusal (a lazily accepted layout an eager copy rejects,
  an element failing only on access, a possible `Panic(0x41)`).
* `legacy`: a parameter outside the typed shapes (function values, nominal
  enums); the previous byte-identical gate applies unchanged.
-/

namespace Solidity.Tools.UpstreamEntry
open Solidity Solidity.AbiEntry

/-- The word kind of a value kind. -/
def kindOf : AbiKind → Option Kind
  | .uint n => some (.uint n)
  | .int n => some (.int n)
  | .bool => some .bool
  | .bytesN n => some (.fixedBytes n)
  | _ => none

/-- The typed shape of a nested ABI type. -/
partial def shapeOf : AbiTy → Option Shape
  | .val k => (kindOf k).map .word
  | .bytes => some .bytes
  | .arr t => (shapeOf t).map .array
  | .fixed t n => (shapeOf t).map (.fixed · n)
  | .tuple _ ms => (ms.mapM fun (m : String × AbiTy) => shapeOf m.2).map .tuple

/-- Nominal enums and function values keep their own refusals. -/
partial def plain (T : Ty) (ws : List (String × Nat)) (k : String) : Bool :=
  (Semantics.lookupBy (k ++ "#enum") ws).isNone && (fnRow? ws k).isNone &&
  match T with
  | .prim _ => true
  | .ref (.array t) | .ref (.fixed t _) => plain t ws (k ++ "[]")
  | .ref (.struct s) => (Semantics.structDef s).all fun (f, t) => plain t (Semantics.structWidths s) f
  | .ref (.mapping ..) => false

/-- The typed parameters of a declaration, or `none` outside the shapes. -/
def params (d : FunDecl) : Option (List Param) :=
  d.params.mapM fun (x, T) => do
    guard (plain T d.widths x)
    let t ← AbiTy.of T d.widths x
    let shape ← shapeOf t
    let loc := match T with
      | .prim _ => Loc.value
      | .ref _ => if Semantics.lookupBy x d.paramLocs == some ParamLoc.calldata then .calldata else .memory
    pure { shape, loc }

/-- What the replay does with one raw vector. -/
inductive Plan where
  | legacy
  | revert
  | run (bytes : List Nat)
  | blocked (reason : String)

/-- Decide one raw vector: `signature` is the canonical ABI signature and
`args` the argument bytes after the selector. -/
def plan (d : FunDecl) (signature : String) (args : List Nat) : Plan :=
  match params d with
  | none => .legacy
  | some ps =>
    let data := Semantics.selectorBytes (Semantics.customSelector signature) ++ args.map UInt8.ofNat
    let I : Input := { data, free := 2 ^ 32 }
    if lim < I.size then .blocked "calldata of 2^64 bytes or more" else
    let fuel := (I.size + 8) * 8
    match verdict I fuel ps with
    | .revert => .revert
    | .run vs => .run ((encodeArgs vs).map UInt8.toNat)
    | .blocked r => .blocked r

end Solidity.Tools.UpstreamEntry
