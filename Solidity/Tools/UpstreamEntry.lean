import Solidity.Semantics.AbiEntry
import Solidity.Semantics.AbiAccess
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
* `legacy`: a parameter outside the typed shapes (function values, enums
  nested in arrays or structs, an enum without its declared bound); the
  previous gate applies unchanged. A top-level enum parameter decodes at its
  declared cardinality (`Kind.enumBelow`), as `validator_revert_t_enum_*`.
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

/-! ### Access-time reads (lane FU2-C)

A calldata parameter whose reference fails somewhere (`AbiEntry.cpart`
records a path) runs only a body whose every mention of it is an access solc
checks in place:

* a complete read `x[i]…[j]` of a word, or the `.length` of a shorter path,
  with index expressions that neither call, write nor mention `x` (each is
  evaluated again by its guard);
* an argument `x` of `abi.encode`/`abi.encodePacked` (solc's encoder reads
  calldata through the same lazy accessors, so it fails exactly when a path
  is recorded: `AbiEntry.cval_revert_of_cpart`; probes of lane FU2-C).

The replay then runs a rewritten body: the index at depth `m` of a read
becomes `accessGuard(ok, i)`, which `require`s `ok` (an empty revert) and is
`i`, where `ok` says no recorded path of length `m` is the indices so far:
by `AbiEntry.cat_cpart` that is exactly when solc's access at that level does
not revert. An encoding of `x` with a recorded path gains a last argument
`accessGuard(false, 0)`: it reverts after the other arguments are evaluated,
where solc's encoder does. Loop annotations, modifiers, copies, aliases,
passing, slices and member paths keep the refusal. -/

/-- The reverting index guard's name, reserved in the replay scope. -/
def accessGuardName : String := "accessGuard__calldata"

/-- `function accessGuard(bool ok, uint i) returns (uint r) { require(ok); r = i; }` -/
def accessGuardDecl : FunDecl :=
  { params := [("ok", .prim .bool), ("i", .prim .uint)], rets := [("r", .prim .uint)],
    body := [.require (.name "ok"), .assign (.name "r") (.name "i")] }

/-- An index expression a guard may evaluate again: no call, no write, no
conditional, no mention of `x`. -/
def simpleIndex (x : String) : RawExpr → Bool
  | .num _ | .bool _ | .env _ => true
  | .name y => y != x
  | .field e _ => simpleIndex x e
  | .binop _ a b => simpleIndex x a && simpleIndex x b
  | .unop _ a => simpleIndex x a
  | _ => false

/-- `a` is the name `x`. -/
def isName (x : String) : RawExpr → Bool
  | .name y => y == x
  | _ => false

/-- Whether `e` is `abi.encode`/`abi.encodePacked`. -/
def isEncode (g : String) : Bool := g == "abi.encode" || g == "abi.encodePacked"

/-- Every mention of `x` in `e` is an admitted access (above). -/
def accessOnlyIn (x : String) (depth : Nat) (e : RawExpr) : Bool :=
  let stripped : RawExpr := Id.run <| e.mapM fun e => pure <| match e with
    | .field a "length" => match indexPath x a with
      | some (n, is) => if n < depth && is.all (simpleIndex x) then .tuple is else e
      | none => e
    | .call g as =>
      if isEncode g then .call g (as.map fun a => if isName x a then .num 0 else a)
      else e
    | e => match indexPath x e with
      | some (n, is) => if n == depth && 0 < n && is.all (simpleIndex x) then .tuple is else e
      | none => e
  !stripped.mentions x

/-- A loop annotation's expressions, which a guard may not enter. -/
def specExprs : RawStmt → List RawExpr
  | .whileLoop a _ _ | .doWhile a _ _ | .loop a _ _ | .forLoop a _ _ _ _ => a.exprs
  | _ => []

/-- The callee of an encoding statement `abi.encode(…);`, as written
(`abi.encode` a member of `abi`, or a builtin name). -/
def encodeCallee? : RawExpr → Option String
  | .name g => if isEncode g then some g else none
  | .field (.name "abi") m => if isEncode ("abi." ++ m) then some ("abi." ++ m) else none
  | _ => none

/-- A statement's expressions, an encoding statement `abi.encode(…);` read
as the one call it is. -/
def accessExprs : RawStmt → List RawExpr
  | .call f as => match encodeCallee? f with
    | some g => [.call g as]
    | none => (RawStmt.call f as).exprs
  | st => st.exprs

/-- The body reads `x` of shape `s` only through admitted accesses. -/
def accessOnly (d : FunDecl) (x : String) (s : Shape) : Bool :=
  d.mods.isEmpty && match readDepth s with
    | none => false
    | some depth =>
      let stmts := d.body.flatMap (RawStmt.flatMapDeep fun st => [st])
      stmts.all (fun st => ((specExprs st).all fun e => !e.mentions x) &&
        (accessExprs st).all (accessOnlyIn x depth))

/-- `ok` for the access at depth `m` with indices `is` (the first `m`): no
recorded path of length `m` equals them. -/
def accessOk (fails : List AbiEntry.Path) (is : List RawExpr) : Option RawExpr :=
  let m := is.length
  let hits := fails.filter (·.length == m)
  if hits.isEmpty then none else
  some <| hits.foldl (fun acc q =>
    let eq := (is.zip q).foldl (fun c (e, j) => RawExpr.binop .and c (.binop .eqB e (.num j)))
      (RawExpr.bool true)
    .binop .and acc (.unop .not eq)) (.bool true)

/-- `x[i₁]…[iₖ]` with each index guarded at its depth. -/
def guardedPath (x : String) (fails : List AbiEntry.Path) (is : List RawExpr) : RawExpr :=
  (List.range is.length).foldl (fun base m =>
    let i := is[m]!
    match accessOk fails (is.take (m + 1)) with
    | some ok => .index base (.call accessGuardName [ok, i])
    | none => .index base i) (.name x)

/-- The body's accesses of `x` guarded by the recorded paths `fails`. -/
partial def guardExpr (x : String) (depth : Nat) (fails : List AbiEntry.Path) (e : RawExpr) : RawExpr :=
  Id.run <| e.mapM fun e => pure <| match e with
    | .field a "length" => match indexPath x a with
      | some (n, is) => if n < depth then .field (guardedPath x fails is) "length" else e
      | none => e
    | .call g as =>
      if isEncode g && as.any (isName x) && !fails.isEmpty then
        .call g (as ++ [.call accessGuardName [.bool false, .num 0]])
      else e
    | e => match indexPath x e with
      | some (n, is) => if n == depth && 0 < n then guardedPath x fails is else e
      | none => e

partial def guardStmts (x : String) (depth : Nat) (fails : List AbiEntry.Path) (ss : List RawStmt) :
    List RawStmt :=
  ss.map fun s =>
    let s := match s with
      | .call f as =>
        match encodeCallee? f with
        | some g =>
          match guardExpr x depth fails (.call g as) with
          | .call _ as' => RawStmt.call f as'
          | _ => s
        | none => Id.run (s.mapExprsM fun e => pure (guardExpr x depth fails e))
      | s => Id.run (s.mapExprsM fun e => pure (guardExpr x depth fails e))
    s.mapBlocks (guardStmts x depth fails)

/-- The declaration with each access-time parameter's reads guarded
(`fails` by parameter position). -/
def guardDecl (d : FunDecl) (shapes : List Shape) (fails : List (List AbiEntry.Path)) : FunDecl :=
  { d with body := (d.params.zip (shapes.zip fails)).foldl (fun body ((x, _), (s, q)) =>
      if q.isEmpty then body else
      match readDepth s with
      | some depth => guardStmts x depth q body
      | none => body) d.body }

/-- The typed parameters of a declaration, or `none` outside the shapes.
`enums` gives a top-level enum parameter's declared largest member (the
import row's `paramRanges`, by position); an enum parameter without one, and
an enum nested in an array or a struct, keep their refusals. -/
def params (d : FunDecl) (enums : Nat → Option Nat := fun _ => none) : Option (List Param) :=
  d.params.zipIdx.mapM fun ((x, T), i) => do
    let enum := (Semantics.lookupBy (x ++ "#enum") d.widths).isSome || (enums i).isSome
    let shape ← if enum then do
        guard (T matches .prim _)
        let hi ← enums i
        pure (Shape.word (.enumBelow (hi + 1)))
      else do
        guard (plain T d.widths x)
        let t ← AbiTy.of T d.widths x
        shapeOf t
    let loc := match T with
      | .prim _ => Loc.value
      | .ref _ => if Semantics.lookupBy x d.paramLocs == some ParamLoc.calldata then .calldata else .memory
    pure { shape, loc, readsOnly := loc == .calldata && readsOnly d x shape }

/-- Which parameters (by position) the body reads only through admitted
access-time accesses. -/
def accessParams (d : FunDecl) (ps : List Param) : Nat → Bool := fun k =>
  match d.params[k]?, ps[k]? with
  | some (x, _), some p => p.loc == .calldata && accessOnly d x p.shape
  | _, _ => false

/-- What the replay does with one raw vector. -/
inductive Plan where
  | legacy
  | revert
  /-- Run on the canonical encoding `bytes` of the body's values; `guarded`
  is the declaration with its access-time reads guarded, when some
  parameter recorded a failing path. -/
  | run (bytes : List Nat) (guarded : Option FunDecl := none)
  | blocked (reason : String)

/-- Decide one raw vector: `signature` is the canonical ABI signature and
`args` the argument bytes after the selector. -/
def plan (d : FunDecl) (signature : String) (args : List Nat)
    (enums : Nat → Option Nat := fun _ => none) : Plan :=
  if args.any (256 ≤ ·) then .blocked "invalid calldata byte" else
  match params d enums with
  | none => .legacy
  | some ps =>
    let data := Semantics.selectorBytes (Semantics.customSelector signature) ++ args.map UInt8.ofNat
    let I : Input := { data, free := 2 ^ 32 }
    if lim < I.size then .blocked "calldata of 2^64 bytes or more" else
    let fuel := (I.size + 8) * 8
    match verdictA I fuel (accessParams d ps) ps with
    | .revert => .revert
    | .run vs fails =>
      -- Overlapping tails can decode to far more than the calldata: solc then
      -- runs out of gas copying them, which this model does not observe.
      if 4 * args.length + 4096 < (encodeArgs vs).length then
        .blocked "decoded arguments exceed four times the calldata: gas is outside the model"
      else
        let guarded := if fails.all (·.isEmpty) then none
          else some (guardDecl d (ps.map Param.shape) fails)
        .run ((encodeArgs vs).map UInt8.toNat) guarded
    | .blocked r => .blocked r

end Solidity.Tools.UpstreamEntry
