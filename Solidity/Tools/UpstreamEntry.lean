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
  body (agreement with solc rests on the cited Yul, probes and fuzzing;
  `AbiEntry.verdict_revert_iff` only unfolds the model's verdict).
* `run bytes`: the body runs on the decoded values, given to the existing
  typed decoder as their canonical encoding `bytes`. For a calldata parameter
  the eager value is also what every lazy read yields
  (`AbiEntry.eager_cref`). The original calldata remains the reported
  observation. `msg.data` and assembly are refused by the adapter as before;
  a calldata slice is admitted only where the elaborator copies or decodes it,
  so it reads the same eager value.
* `run` also for a calldata layout only lazy reads accept (negative
  relative offsets), when the body reads that parameter only through complete
  index paths and lengths (`readsOnly`): each read is one lazy access of the
  value given to the body.
* `blocked`: a named refusal (a lazily accepted layout an eager copy rejects,
  an element failing only on access, a possible `Panic(0x41)`, or decoded
  arguments more than four times the calldata, where solc may run out of gas).
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

/-- How many indexings reach a word of the shape: `none` through a tuple
(member reads are not admitted as lazy paths). -/
def readDepth : Shape → Option Nat
  | .word _ => some 0
  | .bytes => some 1
  | .array e => (readDepth e).map (· + 1)
  | .fixed e _ => (readDepth e).map (· + 1)
  | .tuple _ => none

/-- `x[i]…[j]`: its depth and index expressions, innermost first. -/
def indexPath (x : String) : RawExpr → Option (Nat × List RawExpr)
  | .name y => if y == x then some (0, []) else none
  | .index a i => (indexPath x a).map fun (n, is) => (n + 1, is ++ [i])
  | _ => none

/-- Whether every occurrence of `x` in `e` is a complete read `x[i]…[j]` of
a word (`depth` indexings) or the `.length` of a shorter path; the index
expressions are checked in turn. -/
def readsOnlyIn (x : String) (depth : Nat) (e : RawExpr) : Bool :=
  let stripped : RawExpr := Id.run <| e.mapM fun e => pure <| match e with
    | .field a "length" => match indexPath x a with
      | some (n, is) => if n < depth then .tuple is else e
      | none => e
    | e => match indexPath x e with
      | some (n, is) => if n == depth && 0 < n then .tuple is else e
      | none => e
  !stripped.mentions x

/-- The body (without modifiers) reads the calldata parameter `x` of shape
`s` only through complete index paths and lengths: never as a whole value
(copied, passed, returned, encoded, aliased). -/
def readsOnly (d : FunDecl) (x : String) (s : Shape) : Bool :=
  d.mods.isEmpty && match readDepth s with
    | none => false
    | some depth => (d.body.flatMap (RawStmt.flatMapDeep fun st => st.exprs)).all
        (readsOnlyIn x depth)

/-- The typed parameters of a declaration, or `none` outside the shapes. -/
def params (d : FunDecl) : Option (List Param) :=
  d.params.mapM fun (x, T) => do
    guard (plain T d.widths x)
    let t ← AbiTy.of T d.widths x
    let shape ← shapeOf t
    let loc := match T with
      | .prim _ => Loc.value
      | .ref _ => if Semantics.lookupBy x d.paramLocs == some ParamLoc.calldata then .calldata else .memory
    pure { shape, loc, readsOnly := loc == .calldata && readsOnly d x shape }

/-- What the replay does with one raw vector. -/
inductive Plan where
  | legacy
  | revert
  | run (bytes : List Nat)
  | blocked (reason : String)

/-- Decide one raw vector: `signature` is the canonical ABI signature and
`args` the argument bytes after the selector. -/
def plan (d : FunDecl) (signature : String) (args : List Nat) : Plan :=
  if args.any (256 ≤ ·) then .blocked "invalid calldata byte" else
  match params d with
  | none => .legacy
  | some ps =>
    let data := Semantics.selectorBytes (Semantics.customSelector signature) ++ args.map UInt8.ofNat
    let I : Input := { data, free := 2 ^ 32 }
    if lim < I.size then .blocked "calldata of 2^64 bytes or more" else
    let fuel := (I.size + 8) * 8
    match verdict I fuel ps with
    | .revert => .revert
    | .run vs =>
      -- Overlapping tails can decode to far more than the calldata: solc then
      -- runs out of gas copying them, which this model does not observe.
      if 4 * args.length + 4096 < (encodeArgs vs).length then
        .blocked "decoded arguments exceed four times the calldata: gas is outside the model"
      else .run ((encodeArgs vs).map UInt8.toNat)
    | .blocked r => .blocked r

end Solidity.Tools.UpstreamEntry
