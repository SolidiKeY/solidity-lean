import Solidity.Syntax.Elab.Arms
import Solidity.Syntax.DispatchChain

/-!
# The elaborator's recursion

The `mutual` block that ties `ElabRec`'s arms (`elabRec`) and elaborates
statements, calls and blocks.

A piece of `Syntax/Elab.lean`, whose docstring describes the whole.
-/

namespace Solidity

open Semantics

variable {C : Contract}

variable [FreshNames]

section Elab

variable (C)

/-- `ElabRec`'s default, as `Syntax/Elab/Arms.lean` states it. -/
local instance {α : Type} : Inhabited (ElabM α) := ⟨fun _ _ => .error ""⟩

mutual

/-- The record of the block's functions (`ElabRec`), which ties the arms
defined before it. -/
partial def elabRec (_ : Unit) : ElabRec C where
  hoist := hoist
  hoistBinop := hoistBinop
  hoistTop := hoistTop
  hoistAssign := hoistAssign
  hoistArgs := hoistArgs
  abiMemBytes := abiMemBytes
  abiDecodeBytes := abiDecodeBytes
  abiEncode := @abiEncode
  hoistCallArgs := hoistCallArgs
  fnDispatch := fnDispatch
  fnMemoryDispatch := fnMemoryDispatch
  callValue := callValue
  elabCall := @elabCall
  elabMemCall := elabMemCall
  elabStorageCall := elabStorageCall
  elabCallReceiver := elabCallReceiver
  elabCallReceiverPush := elabCallReceiverPush
  trySelfBody := @trySelfBody
  elabValueCall := elabValueCall
  elabCtor := elabCtor
  hoistStmt := hoistStmt
  elabStmtP := elabStmtP
  elabStmt1 := elabStmt1
  loopExpr := loopExpr
  loopQ := loopQ
  elabStmtsP := elabStmtsP
  elabBranch := elabBranch
  elabScope := elabScope
  elabTuple := @elabTuple

/-- **Captures before a statement**: an `++`/`−−` inside an expression, and a
conditional of references, are evaluated before the statement that holds
them, in the contract's order (an assignment's right-hand side before its target, a
binary operator's right operand first by default, its left under `.viaIR`, an index's base before the
index: an operand read before an effect is captured with `captureExpr`),
into fresh locals (KeY's captures): `values[i++] = 1;`
is `uint se1; se1 = i++; values[se1] = 1;`, and
`Person storage p = c ? alice : bob;` is
`Person storage sp1; if (c) { sp1 = alice; } else { sp1 = bob; }
Person storage p = sp1;`, the alias declared before the branches, which are
scopes.  A memory one is `Person memory mv1 = mx;
if (c) { mv1 = mx; } else { mv1 = my; }`: declared bound to a branch that
indexes nothing (`MPath.indexFree`, a read that cannot revert on a set
local; an unset one, which only a hidden binder holds (decision 17'),
reverts there where solc reads the other branch), or, when both index, to
a fresh default object (`Person memory mv1;`, an object nothing reaches),
and rebound in each branch.  Under the right
operand of `&&`/`||` or in a branch of a conditional, an effect, a call or a
narrow check is captured where solc evaluates it, under a test of its own: `a
&& b` is `bool se = a; if (se) { se = b; }`, and `c ? a : b` is
`uint se; if (c) { se = a; } else { se = b; }`. -/
partial def hoist (s0 : RawExpr) : ElabM (SProg C × RawExpr) :=
  hoistWith C (elabRec ()) s0

/-- Two operands in evaluation order: hold the first read before the second
operand's effects or explicit overflow guards. -/
partial def hoistPair (first last : RawExpr) : ElabM (SProg C × RawExpr × RawExpr) := do
  let (P, first) ← hoist first
  let powerData := powerDataNeeded C (← read) (← ctx) last
  -- Expanding a pure later power inserts failing guards too. Evaluate the
  -- earlier operand before those guards, even when neither operand writes.
  let (Pc, first) ← if powerData then captureExpr C first else captureBefore C first [last]
  let (Q, last) ← if last.hasIncDec || last.hasIdxLen || last.hasCast || hasNarrow C (← ctx) last || powerData
    then hoist last else pure ([], last)
  pure (P ++ Pc ++ Q, first, last)

/-- Binary operands follow the contract's schedule; their positions in the
operator stay fixed, including for subtraction and comparisons. -/
partial def hoistBinop (op : BinOp) (a b : RawExpr) : ElabM (SProg C × RawExpr) := do
  let ltr := C.evalOrder.binaryLeftToRight
  let (P, first, last) ← if ltr then hoistPair a b else hoistPair b a
  pure (P, if ltr then .binop op first last else .binop op last first)

/-- `hoist`, but an operation at the top is left to the statement, which
checks its narrow width after the write (`narrowPost`). -/
partial def hoistTop (e : RawExpr) : ElabM (SProg C × RawExpr) := do
  let e ← e.foldConst
  match e with
  | .binop op a b => do
    let sc ← read
    -- Only the newly enabled unsigned self-frame route uses the expansion.
    -- Signed, unchecked and explicit checking modes keep their old captures.
    let selfPower := sc.selfFrame && !sc.unchecked && sc.overflow.isNone &&
      (intTyOf C (← ctx) a).all (fun (p, _) => p == .uint)
    if op.shortCircuits || (op == .pow && (sc.retainFailureData || selfPower)) then
      hoist (.binop op a b)
    else hoistBinop op a b
  | .unop op a => do
    let (P, a) ← hoist a
    pure (P, .unop op a)
  | e => hoist e

/-- `l = r;`: the right-hand side's captures, then the target's; an operation at
the top of `r` stays there when `l` is a variable (`hoistTop`). -/
partial def hoistAssign (l r : RawExpr) : ElabM (SProg C × RawStmt) := do
  let (P, r) ← if l matches .name _ then hoistTop r else hoist r
  -- a storage reference into a memory object's member or element: copied
  -- into a fresh memory object first, before the target's index (solkey's
  -- `memoryIndexWriteStorageRefRhsCapture`: `T memory mv = sp; m[i] = mv;`)
  let (P, r) ← do
    let Γ ← nctx
    -- the target's shape: its indices, which may have effects, read as `0`
    let rec shape : RawExpr → RawExpr
      | .index e _ => .index (shape e) (.num 0)
      | .field e f => .field (shape e) f
      | e => e
    match synth C Γ (shape l), synth C Γ r with
    | .ok (.mpath (.ref _) (.loc _)), .ok (.path (.ref R) sp) =>
      match hm : (Ty.ref R).mapFree with
      | true =>
        let x ← captureRef C "mv" (.mem R) r
        pure (P ++ [.of Γ (.declMem R x (some (.copy sp hm)) rfl hm)], .name (toString x))
      | false => throw "a copy into memory of a type that holds a mapping"
    | _, _ => pure (P, r)
  let (Pc, r) ← if l.hasIncDec then captureExpr C r else pure ([], r)
  let (Q, l) ← hoist l
  pure (P ++ Pc ++ Q, .assign l r)

/-- A call's arguments, left to right. A non-simple earlier value is held
before hoisting any later argument: casts, fixed-length bases, narrow checks
and modular guards can fail even when they do not modify the state. Bare
names still use the effect-aware capture policy. Already held fresh values
and literals need no additional capture (`captureExpr`). -/
partial def hoistArgs : List RawExpr → ElabM (SProg C × List RawExpr)
  | [] => pure ([], [])
  | a :: as => do
    let (P, a) ← hoist a
    let (Pc, a) ← if !as.isEmpty && !(a matches .name _) then
        captureExpr C a
      else captureBefore C a as
    let (Q, as) ← hoistArgs as
    pure (P ++ Pc ++ Q, a :: as)

/-- A byte string as a memory local: a memory one bound to a fresh name, a
storage one copied into a fresh memory `bytes` (solc's conversion). -/
partial def abiMemBytes (a : RawExpr) : ElabM (SProg C × String) := do
  if let .name x := a then
    if let .ok (.mpath ..) := synth C (← nctx) a then return ([], x)
  let x := toString (← freshCapture "mv")
  pure (← elabStmtsP [.declMemory (.named "bytes") x (some a)], x)



/-- `abi.decode` of a `bytes` or a `string` at the head word `h` of `d`, of
`n` head words: the offset `o` that word holds, the length `L` at `o`, then
the `L` bytes after it copied into a fresh memory `bytes`, each read checked
in range as solc's decoder checks it (an offset or a length past the data
reverts). -/
partial def abiDecodeBytes (T : String) (d : ByteSrc) (h n : Nat) : ElabM (SProg C × String) := do
  let o := toString (← freshCapture "se")
  let L := toString (← freshCapture "se")
  let x := toString (← freshCapture "mv")
  let j := toString (← freshCapture "se")
  let len : RawExpr := d.len
  let start : RawExpr := (RawExpr.name o).addN 32
  let S : List RawStmt :=
    [.require (.binop .ge len (.num (32 * n)))] ++ abiAssemble d o (.num h) 32 ++
    abiBounds d (.name o) (.num 32) ++ abiAssemble d L (.name o) 32 ++
    abiBounds d start (.name L) ++ [
     .declMemory (.named T) x (some (.newArr (.named T) (.name L))),
     .decl (.named "uint") j (some (.num 0)),
     .whileLoop {} (.binop .lt (.name j) (.name L))
       [.assign (.index (.name x) (.name j)) (abiByte d (.binop .add start (.name j))),
        .assign (.name j) (.binop .add (.name j) (.num 1))]]
  pure (← elabStmtsP S, x)

/-- `abi.encode(…)` (`std`) or `abi.encodePacked(…)`/`bytes.concat(…)`/
`string.concat(…)` (`strs`: byte strings only) of the hoisted arguments: a
fresh memory `bytes` of solc's layout (`AbiKind`). -/
partial def abiEncode (std strs : Bool) (args : List RawExpr) (marks : List (Option AbiKind))
    (sel : Option RawExpr := none) : ElabM (SProg C × RawExpr) :=
  abiEncodeWith C (elabRec ()) std strs args marks sel

/-- Prepare a reference call in argument order. Storage-to-memory conversion
copies at the argument's evaluation point; every reference's identity and
each scalar read are held before a later argument can change them. Calls
with only value parameters retain the ordinary capture policy. -/
partial def hoistCallArgs (f : String) (args : List RawExpr) :
    ElabM (SProg C × List RawExpr) := do
  let funs := (← read).funs
  -- A call through a function value captures its own arguments, in order and
  -- at their formal types, after the tag under the source-order schedule
  -- (`dispatchCaptures`); hoisting a later call argument here would run it
  -- before an earlier storage operand is copied.
  if f != "constructor" && funs.all (·.1 != f) && (fnTyOf? C (← ctx) f).isSome then
    return ([], args)
  -- likewise through a callee that is not a name: `callValue`, the memory and
  -- the tuple dispatch capture it at its function type, then the arguments
  if f == callValueName && (args.head?.bind (fnTyOfExpr C (← ctx))).isSome then
    return ([], args)
  let d := if f == "constructor" then C.ctor else lookupBy f funs
  let some d := d | return ← hoistArgs args
  unless d.params.any (fun (_, T) => T matches .ref _) do return ← hoistArgs args
  unless d.params.length == args.length do
    throw s!"{f} takes {d.params.length} arguments, not {args.length}"
  let mut P : SProg C := []
  let mut prepared : List RawExpr := []
  for ((n, T), a) in d.params.zip args do
    -- a reference argument's narrow positions, on the expression as written,
    -- before a capture names it (`elabCallRet` checks the capture again)
    if T matches .ref _ then
      unless a.inlineArrayRoot do
        ElabM.lift (shapeCheck C (← ctx) (shapeUnder d.widths n) a)
    let (Q, a) ← hoist a
    P := P ++ Q
    -- Inline projections now have their independently inferred shape. Check
    -- before capture can bind the argument at the parameter's reference type.
    if T matches .ref _ then ElabM.lift (shapeCheck C (← ctx) (shapeUnder d.widths n) a)
    let Γ ← nctx
    let (Q, a) ← match T with
      | .prim p => do
        if (lookupBy n d.paramLocs).isSome then
          throw s!"{f}: data location on value parameter {n}"
        ElabM.lift (fitCheck C (← ctx) p ((lookupBy n d.widths).getD 256) a)
        captureExpr C a
      | .ref R => do
        let stable ← match a with
          | .name n => match Var.ofName n with
            | .fresh _ i => do
              let sc ← read
              pure (!(C.rootType n).isSome && !sc.mutableFreshNames.contains n &&
                !sc.inlined.any (fun (k₀, k₁) => k₀ ≤ i && i < k₁))
            | _ => pure false
          | _ => pure false
        match lookupBy n d.paramLocs with
        | some .storage =>
          let sp ← ElabM.lift (checkPath C Γ (.ref R) a)
          if stable then pure ([], a) else do
          let x ← captureRef C "sp" (.alias R) a
          pure ([.of Γ (.declStorage R x (some (.path sp)))], .name (toString x))
        | some .memory | some .calldata =>
          let rhs ← ElabM.lift (elabMRhs C Γ R a)
          if stable && (rhs matches .alias _) then pure ([], a) else do
          let x ← captureRef C "mv" (.mem R) a
          pure ([.of Γ (.declMem R x (some rhs) rfl rhs.mapFree)], .name (toString x))
        | none => throw s!"{f}: reference parameter {n} needs a data location"
    P := P ++ Q
    prepared := prepared ++ [a]
  pure (P, prepared)

/-- The captures before an internal dispatch: the callee's tag first under
the source-order schedule (solc's IR pipeline reads the callee value before
the arguments, the legacy one after them; `tests/solc/FunctionValueReferences.sol`,
`calleeOrder`), then each argument once, left to right, at its formal type.
All operands are evaluated before dispatch, including total reads whose value
a later argument can change and failing member reads; the formal type
supplies the contextual type of a literal expression. A memory-array argument
is captured as a memory local: the reference itself for a memory operand (the
callee's writes reach the caller, as Solidity passes memory by reference), a
copy of a storage operand. A storage-array argument is a storage alias of its
path. A struct argument (`fnRefStruct?`) is captured likewise at its location. Returns the statements, the tag's name and the captured arguments. -/
partial def dispatchCaptures (h : RawExpr) (ty : String) (ps : List String) (args : List RawExpr) :
    ElabM (List RawStmt × RawExpr × List RawExpr) := do
  let mut pre : List RawStmt := []
  let mut tag := h
  if C.evalOrder.binaryLeftToRight || !h.isPure then
    let t := toString (← freshCapture "se")
    pre := [.decl (.named ty) t (some h)]
    tag := .name t
  let mut as : List RawExpr := []
  for (a, c) in args.zip ps do
    let y := toString (← freshCapture "se")
    pre := pre ++ [match fnRefElem? C c, fnRefStruct? C c with
      | some (e, false), _ => .declMemory (.array (.named e)) y (some a)
      | some (e, true), _ => .declStorage (.array (.named e)) y (some a)
      | none, some (st, false) => .declMemory (.named st) y (some a)
      | none, some (st, true) => .declStorage (.named st) y (some a)
      | none, none => .decl (.named c) y (some a)]
    as := as ++ [.name y]
  pure (pre, tag, as)

/-- **A call through a function value** `h(a)`, `h` of the function type
`ty` (`fnTyOf?`): its arguments captured once, left to right,
then a dispatch over the functions of `ty`, `if (h == 1) { r = g₁(a); } else
if … else { revert(); }` (`fnTag`): calling an unassigned value is solc's
`Panic(0x51)`, transported as literal data in a self-call frame and otherwise
read as the ordinary solkey revert. A function
of `ty` this one may not call (declared after it) is refused when it is named
as a value in the contract; one that is not cannot reach here (`fnTag`).
With `resNew`, `res` is declared by the statement before (`elabCallRet`). -/
partial def fnDispatch (h ty : String) (args : List RawExpr) (res : Option (Var × PrimTy))
    (resW : Nat) (resNew : Bool) : ElabM (SProg C) := do
  let some (ps, rs, ext) := fnParts? ty | throw s!"{h}: the function type {ty}"
  if ext then return ← extDispatch h ty ps rs args res resW resNew
  unless ps.length == args.length do
    throw s!"{h} takes {ps.length} arguments, not {args.length}"
  -- a reference parameter or return: no function's signature is spelled so
  -- (`FunDecl.sigTy?`), so the dispatch would list none; a memory or storage
  -- array of a plain value element (`fnRefElem?`) is the reference parameter spelled
  if let some c := (ps.filter fun c => (fnRefElem? C c).isNone && (fnRefStruct? C c).isNone) ++ rs |>.find? fun c =>
      (fnCompTy? C c).isNone then
    throw s!"{h}(…): a function type with a {c} parameter or return is not modelled \
      (docs/semantic-gaps.md, \"Function types\")"
  let scope := (← read).funs
  let taken := fnTaken C
  let mut cands : List (String × Nat) := []
  for ((g, d), i) in C.funs.zipIdx do
    if fnInternal C g && FunDecl.sigTy? C d == some ty && fnReachable C g then
      if scope.any (·.1 == g) then cands := cands ++ [(g, i + 1)]
      else if taken.contains g then
        throw s!"{h}(…) may call {g}, which is not declared before this function: \
          declare the functions of type {ty} first"
  let (pre, tag, as) ← dispatchCaptures (.name h) ty ps args
  let call (g : String) : RawStmt := match res with
    | some (x, _) => .assign (.name (toString x)) (.call g as)
    | none => .call (.name g) as
  let (Γ0, _) ← get
  if resNew then
    if let some (x, p) := res then declare C (toString x) (.val p resW)
  let P ← withReader (fun sc => { sc with top := false }) do
    let P ← elabStmtsP pre
    let Γ ← nctx
    -- A self-call transports exact bytes, so Panic(0x51) is independent
    -- of the transaction oracle's fallback code for an unclassified panic.
    let fail : Stmt C Γ.ctx Γ.ctx :=
      if (← read).selfFrame || (← read).retainFailureData then .revertData [.bytes (Semantics.encodePanic 0x51)]
      else .revert
    -- One arm per candidate, in tag order (`DispatchArm.chain`, whose runs
    -- `Semantics/Dispatch.lean` characterises per tag).
    let mut arms : List (DispatchArm C Γ.ctx) := []
    for (g, t) in cands do
      let c ← checkIn C Γ .bool (.binop .eqB tag (.num t))
      let body ← elabScope Γ [call g]
      arms := arms ++ [{ cond := c, body := body.2 }]
    pure (P ++ [.of Γ (DispatchArm.chain arms fail)])
  modify fun (_, k) => (Γ0, k)
  pure P


/-- Internal memory-return dispatch (`bytes memory`, `T[] memory` or a
struct in memory, one return) uses the same source tags, scope checks and argument captures as
scalar dispatch (`dispatchCaptures`). The shared destination is intrinsically
a memory reference, and each branch binds the selected call's returned alias;
no storage copy or scalar encoding of the returned reference is introduced. -/
partial def fnMemoryDispatch (h : RawExpr) (ty : String) (args : List RawExpr) :
    ElabM (SProg C × RawExpr) := do
  let some (ps, [r], false) := fnParts? ty
    | throw "memory dispatch needs an internal signature with one memory return"
  let dstTy : RawTy ← if r == "bytesmemory" then pure (.named "bytes") else
    match fnRefElem? C r, fnRefStruct? C r with
    | some (e, false), _ => pure (.array (.named e))
    | none, some (st, false) => pure (.named st)
    | _, _ => throw s!"memory dispatch returns a {r}, not a memory reference"
  unless ps.length == args.length do
    throw s!"memory dispatch takes {ps.length} arguments, not {args.length}"
  if let some c := ps.find? fun c =>
      (fnRefElem? C c).isNone && (fnRefStruct? C c).isNone && (fnCompTy? C c).isNone then
    throw s!"memory dispatch: a function type with a {c} parameter is not modelled"
  let scope := (← read).funs
  let taken := fnTaken C
  let mut cands : List (String × Nat) := []
  for ((g, d), i) in C.funs.zipIdx do
    if fnInternal C g && FunDecl.sigTy? C d == some ty && fnReachable C g then
      if scope.any (·.1 == g) then cands := cands ++ [(g, i + 1)]
      else if taken.contains g then
        throw s!"memory dispatch may call {g}, which is not declared before this function"
  -- A zero-argument dispatch keeps its original capture of the tag first.
  let (pre, tag, as) ← if args.isEmpty then do
      let t := toString (← freshCapture "se")
      pure ([.decl (.named ty) t (some h)], RawExpr.name t, [])
    else dispatchCaptures h ty ps args
  let dst := toString (← freshCapture "mv")
  let P ← elabStmtsP (pre ++ [.declMemory dstTy dst none])
  let failure := if (← read).selfFrame || (← read).retainFailureData then
      RawStmt.revertRaw (.bytesLit ((Semantics.encodePanic 0x51).map UInt8.toNat)) else RawStmt.revert
  let dispatch := cands.foldr (fun (g, t) rest =>
    RawStmt.ite (.binop .eqB tag (.num t))
      [.assign (.name dst) (.call g as)] [rest]) failure
  let Q ← elabStmtsP [dispatch]
  pure (P ++ Q, .name dst)


/-- **A call through an external function value** `h(a)`, `h` of the
external function type `ty`: `h` is `address * 2^32 + selector` (`fnPure`),
so the call is an external call to `h / 2^32` (`extCallStmt`), dispatched on
the selector `h - h / 2^32 * 2^32` over the functions of `C` of that type, so that one
to `this` runs the function (`Stmt.tryCall`'s `self`, O8); any other
selector is a call the model names `#selector`, its first argument the
selector, whose response the world chooses as for any external call. Imported
source declarations additionally clean the receiver to `address(h / 2^32)`;
the selector still uses the raw quotient. -/
partial def extDispatch (h ty : String) (ps rs : List String) (args : List RawExpr)
    (res : Option (Var × PrimTy)) (resW : Nat) (resNew : Bool) : ElabM (SProg C) := do
  unless ps.length == args.length do
    throw s!"{h} takes {ps.length} arguments, not {args.length}"
  if 1 < rs.length then throw s!"{h}(…): an external function value of several returns"
  let a := toString (← freshCapture "se")
  let sl := toString (← freshCapture "se")
  -- Source addresses are 160 bits. Keep the uncleaned quotient for the
  -- selector subtraction, then capture its genuine address conversion in a
  -- separate local before the try-call. Declaring the quotient as address
  -- would mark it already clean and make addressCapture skip the conversion.
  -- Native contracts retain their existing, wider transaction-address API.
  let source := C.funs.any fun (_, d) => d.sourceDecl.isSome
  let mut pre : List RawStmt := [.decl (.named (if source then "uint" else "address")) a
      (some (.binop .div (.name h) (.num selShift))),
    .decl (.named "uint") sl
      (some (.binop .sub (.name h) (.binop .mul (.name a) (.num selShift))))]
  let mut receiver := a
  if source then
    let clean := toString (← freshCapture "se")
    pre := pre ++ [.decl (.named "address") clean (some (.call "address" [.name a]))]
    receiver := clean
  let mut as : List RawExpr := []
  for (x, c) in args.zip ps do
    if x.isPure then as := as ++ [x] else
      let y := toString (← freshCapture "se")
      pre := pre ++ [.decl (.named c) y (some x)]
      as := as ++ [.name y]
  let mut cands : List (String × Nat) := []
  for (g, d) in C.funs do
    if fnExternalEntry C g && FunDecl.extTy? C d == some ty then
      if let some sel := fnSelector? C g then cands := cands ++ [(g, sel)]
  let other ← extCallStmt (.name receiver) "#selector" (.name sl :: as) rs res
  let mut disp : List RawStmt := [other]
  for (g, sel) in cands.reverse do
    disp := [.ite (.binop .eqB (.name sl) (.num sel)) [← extCallStmt (.name receiver) g as rs res] disp]
  let (Γ0, _) ← get
  if resNew then
    if let some (x, p) := res then declare C (toString x) (.val p resW)
  let P ← elabBranch (pre ++ disp)
  modify fun (_, k) => (Γ0, k)
  pure P

/-- **A call through a value that is not a name** (`callValueName`):
`s.f(x)`, `fs[i](x)`, `choose(b)(x)`.  The callee is evaluated first, into
a fresh local of its function type (`fnTyOfExpr`), then called as a name is
(`fnDispatch`); `r.g(x)` for a function `g` of `C` is an external call
(`extCallStmt`), `this.g(x)` the contract's own (O8). -/
partial def callValue (h : RawExpr) (args : List RawExpr) (res : Option (Var × PrimTy))
    (resW : Nat) (resNew : Bool) : ElabM (SProg C) := do
  -- a function's or a function value's name in parentheses
  if let .name g := h then
    if (← read).funs.any (·.1 == g) || (fnTyOf? C (← ctx) g).isSome then
      return (← elabCallRet g args res resW (resNew := resNew)).1
  let Γe ← ctx
  let stmts : List RawStmt ← match extMember? C Γe h with
    | some (r, g) => do
      let some d := lookupBy g C.funs | throw s!"{g} is not a function of the contract"
      let rs ← d.rets.mapM fun (n, T) => match T with
        | .prim p => pure (declTyName d.widths n p)
        | _ => throw s!"{h.toStr}(…): an external call returns values"
      pure [← extCallStmt r g args rs res]
    | none => do
      let some ty := fnTyOfExpr C Γe h | throw s!"{h.toStr}(…): the callee is not a function value"
      let y := toString (← freshCapture "se")
      let call : RawStmt := match res with
        | some (x, _) => .assign (.name (toString x)) (.call y args)
        | none => .call (.name y) args
      pure [.decl (.named ty) y (some h), call]
  let (Γ0, _) ← get
  if resNew then
    if let some (x, p) := res then declare C (toString x) (.val p resW)
  let P ← elabBranch stmts
  modify fun (_, k) => (Γ0, k)
  pure P

/-- **A call, inlined** (KeY's `FunctionBodyStatement`, then its body): `f`
is found among the functions the scope may call, its arguments are checked
at its parameters' types in the caller's scope, and its body is elaborated in
a scope of its own — its parameters and its return variable, every local
renamed fresh (`renameStmts`), then its `return`s lowered (`lowerReturns`) — with
the functions declared before `f`, so no call recurses.  `res` is the local
the returned value lands in, with its type. -/
partial def elabCall (f : String) (args : List RawExpr) (res : Option (Var × PrimTy))
    (resW : Nat := 256) (resNew : Bool := false) : ElabM (SProg C) := do
  pure (← elabCallRet f args res resW (resNew := resNew)).1

/-- A call of `f`, which returns a memory reference of type `R`, and `bind Γ r`,
the statement that binds the callee's return variable `r` where the call
is, read in the caller's context `Γ` with `r` pushed: `Account memory mv1 =
mv2;`, `m = mv2;` (the module docstring). -/
partial def elabMemCall (f : String) (args : List RawExpr) (R : RefTy)
    (bind : (Γ : NCtx) → Var → (Ty.ref R).mapFree = true → Except String (SStmt C)) :
    ElabM (SProg C) := do
  let dynamic ← if f == callValueName then do
      let h :: rest := args | throw "memory call has no callee"
      pure ((fnTyOfExpr C (← ctx) h).map fun ty => (h, ty, rest))
    else if (← read).funs.all (·.1 != f) then
      pure ((fnTyOf? C (← ctx) f).map fun ty => (RawExpr.name f, ty, args))
    else pure none
  if let some (h, ty, actuals) := dynamic then
    let some (_, [r], false) := fnParts? ty | throw "memory function value of several returns"
    let expected : RawTy ← if r == "bytesmemory" then pure (.named "bytes") else
      match fnRefElem? C r, fnRefStruct? C r with
      | some (e, false), _ => pure (.array (.named e))
      | none, some (st, false) => pure (.named st)
      | _, _ => throw s!"memory function value returns a {r}"
    let (T, _) ← ElabM.lift (elabTyW C expected)
    unless T == .ref R do throw "memory function value returns a different reference type"
    let (P, _) ← fnMemoryDispatch h ty actuals
    let (r, _) :: Γ ← nctx | throw "internal: memory dispatch did not export its reference"
    let ⟨hm⟩ ← ElabM.lift (memOk R)
    return P ++ [← ElabM.lift (bind Γ r hm)]
  let (P, r, _) ← elabCallRet f args none
  match r with
  | some ⟨Γ, R', r, storage⟩ =>
    if storage then throw s!"{f} returns a storage reference, not a memory reference"
    unless R' = R do throw s!"{f} returns a {Ty.ref R'}, not a {Ty.ref R}"
    let ⟨hm⟩ ← ElabM.lift (memOk R)
    pure (P ++ [← ElabM.lift (bind Γ r hm)])
  | none => throw s!"{f} does not return a memory reference"

/-- Bind the alias exported by a storage-returning call, without a copy or
an allocation. The return variable is the newest local after the call. -/
partial def elabStorageCall (f : String) (args : List RawExpr) (R : RefTy)
    (bind : (Γ : NCtx) → Var → Except String (SStmt C)) : ElabM (SProg C) := do
  let (P, result, _) ← elabCallRet f args none
  match result with
  | some ⟨Γ, R', r, storage⟩ =>
    unless storage do throw s!"{f} returns a memory reference, not a storage reference"
    unless R' = R do throw s!"{f} returns a {Ty.ref R'}, not a {Ty.ref R}"
    pure (P ++ [← ElabM.lift (bind Γ r)])
  | none => throw s!"{f} does not return a storage reference"

/-- Retain `f().push(e)` or `f().pop()` as the calculus's native receiver
statement. The callee is elaborated in its frame, without exporting a caller local. -/
partial def elabCallReceiver (f : String) (args : List RawExpr)
    (op : (Γ : NCtx) → (E : Ty) → ElabM (ReceiverOp C Γ.ctx E)) :
    ElabM (SProg C) := do
  let (P, _, _) ← elabCallRet f args none
  let [⟨Γ, _, s⟩] := P | throw s!"{f}: a receiver call must elaborate to one call"
  match s with
  | .call f args (.storage (.array E) r) body =>
    pure [.of Γ (.callReceiver f args r body (← op Γ E))]
  | _ => throw s!"{f}: push/pop needs a dynamic storage-array return"

/-- Keep an effectful operand inside `f().push(e)`, in a private caller scope.
Its prefix is expanded only after the getter has been captured by the taclet. -/
partial def elabCallReceiverPush (f : String) (args : List RawExpr) (a : RawExpr) :
    ElabM (SProg C) := do
  let caller ← ctx
  let (P, _, _) ← elabCallRet f args none
  let [⟨Γ, _, s⟩] := P | throw s!"{f}: a receiver call must elaborate to one call"
  match s with
  | .call f args (.storage (.array E) r) body =>
    let (Q, a) ← hoist a
    let Γv ← nctx
    let value ← (match E with
      | .prim p => do pure (Src.val (← checkIn C Γv p a))
      | .ref R => do
        let some d := lookupBy f (← read).funs | throw "a deferred receiver's declaration is missing"
        let some (r, _) := d.ret | throw "a deferred receiver needs one return"
        ElabM.lift (storageCopyShape C (← ctx) (shapeUnder d.widths (r ++ "[]")) a)
        ElabM.lift (checkStorageCopy C Γv R a)
      : ElabM (Src C Γv.ctx E))
    let result ← if Q.isEmpty then do
      let h ← ElabM.lift (Γv.wkTo Γ)
      pure (.of Γ (.callReceiver f args r body (.push (some (value.wk h)) rfl)))
    else do
      let ⟨Δ, code⟩ ← ElabM.lift (SProg.chain Γ.names Γ.ctx Q)
      let some h := Γv.thinInto (code.outNames Γ.names) Δ |
        throw "internal: a deferred receiver operand left an unmatched local scope"
      pure (.of Γ (.callReceiverPush f args r body code (value.wk h)))
    modify fun (_, k) => (caller, k)
    pure [result]
  | _ => throw s!"{f}: push/pop needs a dynamic storage-array return"

/-- `elabCall`, and the fresh return variable of a callee that returns a
memory reference, with its type and the caller's context: the call's frame
declares it (a fresh default object, `CallRet.mem`) and leaves it to the
caller, which binds it after the call (`elabMemCall`).  With `targets`, the
call is a tuple assignment's right-hand side (`elabTuple`), KeyTaclets'
`FunctionBodyStatement` with targets: it returns every return value
(`CallRet.rets`, one or several), which the caller reads after the call —
their fresh variables, types and widths.  A callee of several returns called
as a statement (`f(a);`, KeY's `InternalCall`) declares them at the head of
its body and returns nothing.  With `resNew`, the local `res` is declared by
the statement before the call (`uint y = f(a);` is `uint y; y = f(a);`):
the call is read in the context it pushes, its arguments where `res` is not
yet in scope. -/
partial def elabCallRet (f : String) (args : List RawExpr) (res : Option (Var × PrimTy))
    (resW : Nat := 256) (targets : Bool := false) (ctor : Bool := false) (resNew : Bool := false)
    (selfFrame : Bool := false) :
    ElabM (SProg C × Option (NCtx × RefTy × Var × Bool) × List (PrimTy × Var × Nat)) :=
  elabCallRetWith C (elabRec ()) f args res resW targets ctor resNew selfFrame

/-- **The body a `try` runs when its receiver is the contract itself**
(`Stmt.tryCall`'s `self`, `docs/options.md` O8): the callee `g` inlined as a
call with targets (`elabCallRet`), its environment the frame's
(`RawStmt.selfFrame`), when `g` is a function declared before this one whose
parameters take the arguments' types and whose return variables are the
`try`'s `ρ`, or a `try` that binds none (`try this.g(x) { … }`); `none` otherwise (another contract's function, or one this
function may not call: the restriction that keeps the run structural). -/
partial def trySelfBody (g : String) {Γ : NCtx} (args : List (ExtArg C Γ.ctx)) (ρ : Ctx) :
    ElabM (Option ((ps : Ctx) × (Γf : Ctx) × Args C Γ.ctx ps × Prog C (ρ ++ ps) Γf)) := do
  unless fnExternalEntry C g do return none
  let some (_, d) := (← read).funs.find? (·.1 == g) | pure none
  unless d.params.map (·.2) == args.map (fun a => Ty.prim a.1) do return none
  unless d.rets.all (fun (_, T) => T matches .prim _) do return none
  let raw := args.map fun a => Simple.toRaw C Γ.names a.2
  -- a `try` that binds none: the callee called as a statement (`selfCall?`)
  let targets := !ρ.isEmpty || d.rets.isEmpty
  let r ← tryCatch (do
      let (P, _, _) ← elabCallRet g raw none (targets := targets) (selfFrame := true)
      pure (some P)) fun _ => pure none
  let some [st] := r | pure none
  if h : st.Γ.ctx = Γ.ctx then
    -- Compiler-generated getters use empty-data bounds failures. Their
    -- source plan has already placed a require before every array index;
    -- instrumenting the guarded reads as ordinary Solidity expressions
    -- would invent unreachable Panic(0x32) data in catchData's analysis.
    let getter := d.sourceDecl.any fun source => match source.callable with
      | .getter _ => true
      | _ => false
    pure ((Stmt.selfCall? C ρ (h ▸ st.s)).map fun ⟨ps, Γf, sargs, sbody⟩ =>
      ⟨ps, Γf, sargs, if getter then sbody else sbody.withPanics⟩)
  else pure none

/-- **The body a value call runs when its receiver is the contract itself**
(`(bool ok, ) = payable(this).call{value: v}("")`, `docs/options.md` O8):
the contract's `receive`, declared before this function, inlined as a call
with no targets, in a frame of its own: `msg.sender` is `address(this)`, and
`msg.value` its one parameter, which the call passes `v` (raw, read in the
caller's scope).  `none` where there is no such `receive`, or where it does
not elaborate so: a function it calls reads `msg.value` (its frame does not
have the parameter). -/
partial def receiveSelfBody {Γ : NCtx} (v : RawExpr) :
    ElabM (Option ((ps : Ctx) × (Γf : Ctx) × Args C Γ.ctx ps × Prog C ([] ++ ps) Γf)) := do
  let funs := (← read).funs
  let some (_, d) := funs.find? (·.1 == "receive") | pure none
  unless d.params.isEmpty && d.rets.isEmpty && d.mods.isEmpty do return none
  -- the parameter `msg.value` reads, a name no source declares
  let receiveValueParam := "msgValue$"
  let pv := RawExpr.name receiveValueParam
  let ps : List (Name × Ty) := [(receiveValueParam, .prim .uint)]
  let d' : FunDecl := { d with params := ps, body := d.body.map (RawStmt.selfFrame pv) }
  let funs' := funs.map fun (n, e) => if n == "receive" then (n, d') else (n, e)
  let r ← tryCatch (do
      let nested : RawExpr := .name (receiveValueParam ++ "nested")
      let (P, _, _) ← withReader (fun sc => { sc with funs := funs', selfValue := nested })
        (elabCallRet "receive" [v] none (targets := true) (selfFrame := true))
      pure (some P)) fun _ => pure none
  let some [st] := r | pure none
  if h : st.Γ.ctx = Γ.ctx then
    pure (Stmt.selfCall? C [] (h ▸ st.s))
  else pure none

/-- **A value call** `(bool ok, ) = r.call{value: v}("")`, its result in
`ix`: with the contract's `receive` available (`receiveSelfBody`), `bool
se = r == address(this); if (se) { try this.receive{value: v}() { ok = true; } catch { ok
= false; } } else { … the call … }`, the self-call a `try` the contract runs
(`Stmt.tryCall`'s `self`), every failure `ok = false` with the state the
caller's; otherwise the call alone. -/
partial def elabValueCall (Γ : NCtx) (ix : Idx Γ.ctx (.val .bool)) (okName : RawExpr)
    (e a : RawExpr) : ElabM (SProg C) := do
  let plain : ElabM (SProg C) := do
    pure [.of Γ (.send ix (← checkIn C Γ .uint e) (← checkIn C Γ .uint a) true)]
  unless (← read).funs.any (·.1 == "receive") do return ← plain
  let st ← get
  let (P, ⟨Γr, addr⟩) ← simpleOf C .uint e
  let Γ1 ← nctx
  let addr1 := addr.wk (← ElabM.lift (Γr.wkTo Γ1))
  -- the test captured, as `ifElseSplit` takes a simple condition
  let c : Val C Γ1.ctx .bool :=
    .binop .eqB rfl rfl (.simple addr1) (.simple (.env .selfAddress rfl))
  let x ← captureAs C "se" (.val .bool)
  let ⟨Γ', _, ixc⟩ ← afterCapture Γ1 x (.val .bool)
  let addr' := addr1.wk (← ElabM.lift (Γ1.wkTo Γ'))
  let ix' := ix.wk (← ElabM.lift (Γ.wkTo Γ'))
  let some ⟨_, _, sargs, sbody⟩ ← receiveSelfBody (Γ := Γ') a | set st; plain
  let v ← checkIn C Γ' .uint a
  let setOk (b : Bool) : List RawStmt := [.assign okName (.bool b)]
  let (Γe, _) ← get
  let okP ← elabStmtsP (setOk true)
  let okP ← ElabM.lift (SProg.chain Γ'.names ([] ++ Γ'.ctx) okP)
  let (_, k) ← get
  set (Γe, k)
  let err ← elabScope Γ' (setOk false)
  let ⟨κ, cb⟩ := CodeBinder.ofOption (none : Option Var)
  let pnc ← elabStmtsP (setOk false)
  let pnc ← ElabM.lift (SProg.chain (cb.names ++ Γ'.names) (κ ++ Γ'.ctx) pnc)
  let (_, k) ← get
  set (Γe, k)
  let other ← elabScope Γ' (setOk false)
  let call : ExtCall C Γ'.ctx := ⟨addr', "receive", []⟩
  let tryS : Stmt C Γ'.ctx Γ'.ctx :=
    .tryCall call Binders.nil okP.2 err.2 cb pnc.2 other.2 sargs sbody true
  pure (P ++ [.of Γ1 (.declLocal .bool x (some c)),
    .of Γ' (.ite (.simple (.local ixc)) (.cons tryS .nil)
      (.cons (.send ix' (.simple addr') v true) .nil))])

/-- **`constructor(args);`**, a deployment (solkey's obligation's
`constructor(x̄)@C;`): the constructor inlined as any call is
(`elabCallRet`), the state variables' initializers prepended to its body
after its parameters are bound; with no `constructor` declared, the implicit
one, of no parameters and no body.  It returns to no targets
(`CallRet.rets []`), a `FunctionBodyStatement` as solkey's is
(`functionBodyExpand`).  Only a program's own statements deploy, never an
inlined body (no function calls the constructor), and not a branch, a loop
or a block (`elabBranch`), which would deploy again or only sometimes. -/
partial def elabCtor (args : List RawExpr) : ElabM (SProg C) := do
  unless (← read).top do
    throw "constructor(…) in a function's body or a block: only a program's own statements deploy"
  pure (← elabCallRet "constructor" args none (targets := true) (ctor := true)).1

/-- The captures a statement's own expressions need (`hoist`), and the
statement left: a right-hand side before the left-hand side, as the
interpreter evaluates them, a receiver before an argument.  A branch's statements are elaborated on their
own. -/
partial def hoistStmt (s0 : RawStmt) : ElabM (SProg C × RawStmt) :=
  hoistStmtWith C (elabRec ()) s0

/-- A statement, as a block: its narrow rewrites (`narrowPure`), its captures
(`hoistStmt`), then the statement,
whose compound target may need a capture of its own. -/
partial def elabStmtP (s : RawStmt) : ElabM (SProg C) :=
  elabStmtPWith C (elabRec ()) s

/-- A statement whose expressions have no effect left. -/
partial def elabStmt1 (s0 : RawStmt) : ElabM (SProg C) :=
  elabStmt1With C (elabRec ()) s0

/-- A loop's condition, invariant or variant, of type `p` (its narrow
rewrites done, `elabStmtP`), read in `Γ`: nothing may be captured before it,
since it is evaluated where the loop is, again.  So an effect, a call to a
declared function, a cast, a narrow operation that needs a capture or a
struct constructor in it is refused (`docs/loops.md`), where solkey
evaluates it per iteration. -/
partial def loopExpr (Γ : NCtx) (p : PrimTy) (e : RawExpr) (what : String) : ElabM (Val C Γ.ctx p) := do
  let st ← get
  let (P, _) ← hoist e
  set st
  unless P.isEmpty do
    throw s!"{e.toStr}: a loop's {what} needs a statement before it (an effect, a call, \
      a cast, a narrow operation or a constructor), and is evaluated again each iteration"
  checkIn C Γ p e

/-- A quantified invariant clause (`LoopQ`): its bound local pushed while
its body is read. -/
partial def loopQ (Γ : NCtx) : RawInv → ElabM (LoopQ C Γ.ctx)
  | .expr e => do pure (.val (← loopExpr Γ .bool e "invariant"))
  | .imp a b => do
    pure (.imp (← loopExpr Γ .bool a "invariant") (← loopExpr Γ .bool b "invariant"))
  | .all p x b => do
    let st ← get
    modify fun (Γe, k) => ((x, .val p) :: Γe, k)
    let body ← loopQ ((Var.ofName x, .val p) :: Γ) b
    set st
    pure (.all (Var.ofName x) p body)

/-- A block. -/
partial def elabStmtsP : List RawStmt → ElabM (SProg C)
  | [] => pure []
  | s :: ss => do
    let P ← elabStmtP s
    let Q ← elabStmtsP ss
    pure (P ++ Q)

/-- A branch: its declarations stay inside it, and it does not deploy
(`ElabScope.top`). -/
partial def elabBranch (ss : List RawStmt) : ElabM (SProg C) := do
  let (Γ, _) ← get
  let P ← withReader (fun sc => { sc with top := false }) (elabStmtsP ss)
  let (_, k) ← get
  set (Γ, k)
  pure P

/-- A branch as a block of its own, from the locals in scope `Γ` (which it
must be entered in). -/
partial def elabScope (Γ : NCtx) (ss : List RawStmt) : ElabM (Blk C Γ.ctx) := do
  ElabM.lift (SProg.chain Γ.names Γ.ctx (← elabBranch ss))

/-- **A tuple assignment from a call through an internal function value**
`(a, b) = h(x)`: the dispatch's captures (`dispatchCaptures`), then one
branch per candidate `g` of `h`'s type, the direct tuple assignment
`(a, b) = g(y)` on the captured arguments, then the unassigned-value failure.
Value returns only: a direct tuple call binds primitive returns. -/
partial def fnTupleDispatch (ts : List (Option RawExpr)) (h ty : String) (args : List RawExpr) :
    ElabM (SProg C) := do
  let some (ps, rs, false) := fnParts? ty
    | throw s!"{h}(…): an external function value in a tuple assignment"
  unless ps.length == args.length do throw s!"{h} takes {ps.length} arguments, not {args.length}"
  unless rs.length == ts.length do throw s!"{h} returns {rs.length} values, not {ts.length}"
  if let some c := ps.find? fun c =>
      (fnRefElem? C c).isNone && (fnRefStruct? C c).isNone && (fnCompTy? C c).isNone then
    throw s!"{h}(…): a function type with a {c} parameter is not modelled"
  if let some c := rs.find? fun c => (fnCompTy? C c).isNone then
    throw s!"{h}(…): a function value returning a {c} among several values is not modelled \
      (a direct tuple call binds value returns)"
  let scope := (← read).funs
  let taken := fnTaken C
  let mut cands : List (String × Nat) := []
  for ((g, d), i) in C.funs.zipIdx do
    if fnInternal C g && FunDecl.sigTy? C d == some ty && fnReachable C g then
      if scope.any (·.1 == g) then cands := cands ++ [(g, i + 1)]
      else if taken.contains g then
        throw s!"{h}(…) may call {g}, which is not declared before this function: \
          declare the functions of type {ty} first"
  let (pre, tag, as) ← dispatchCaptures (.name h) ty ps args
  let failure := if (← read).selfFrame || (← read).retainFailureData then
      RawStmt.revertRaw (.bytesLit ((Semantics.encodePanic 0x51).map UInt8.toNat)) else RawStmt.revert
  let dispatch := cands.foldr (fun (g, t) rest =>
    RawStmt.ite (.binop .eqB tag (.num t)) [.tupleAssign ts (.call g as)] [rest]) failure
  elabStmtsP (pre ++ [dispatch])

/-- **A tuple assignment** `(t₀, , t₂) = e;`, written out as solkey's
`ParserUtils.tupleAssignment` writes it.  From a call of a function of several
returns: the call (`CallRet.rets`), then `tᵢ = rᵢ;` for each target, left to
right (a component left out is not read).  From a tuple `(e₀, e₁, e₂)`: each
component with a target into a fresh temporary, left to right, then each
target assigned its temporary, left to right; a component left out is
dropped if it can neither revert nor have an effect, and evaluated
otherwise (solc's; solkey keeps only a call). Primitive targets may overlap:
the captured values are written right to left, as in Solidity. Reference targets
that may alias, and targets reading another target, remain refused.  The variables of a tuple
declaration, which no component reads, are assigned directly (`direct`). -/
partial def elabTuple (ts : List (Option RawExpr)) (rhs : RawExpr) (direct : Bool := false) :
    ElabM (SProg C) := do
  let tgts := ts.filterMap id
  let mut nonLocal := 0
  let mut primitiveTargets := true
  for t in tgts do
    if t.hasIncDec then throw s!"{t.toStr}: a tuple's target with an effect"
    unless (← synthM C t).2 matches .val _ _ | .path (.prim _) _ | .mpath (.prim _) _ do
      primitiveTargets := false
    unless (← synthM C t).2 matches
        .val _ (.simple (.local _)) | .mpath (.ref _) (.var ..) | .path (.ref _) (.alias _) do
      nonLocal := nonLocal + 1
    for u in tgts do
      if let .name x := u then
        if t.toStr != u.toStr && t.mentions x then throw s!"{t.toStr}: a tuple's target that reads {x}, another"
  -- Until arbitrary LHS locations have their own typed capture, only stable
  -- names/fields/literal indices enter the new overlapping-target path.
  let rec stableTarget : RawExpr → Bool
    | .name _ => true
    | .field b _ => stableTarget b
    | .index b (.num _) => stableTarget b
    | _ => false
  primitiveTargets := primitiveTargets && tgts.all stableTarget
  if nonLocal > 1 && !primitiveTargets then throw "a tuple assignment to two targets that are not stack locals"
  unless primitiveTargets || (tgts.map (·.toStr)).eraseDups.length == tgts.length do
    throw "a tuple assignment to the same target twice"
  let reverseWrites := primitiveTargets &&
    (nonLocal > 1 || (tgts.map (·.toStr)).eraseDups.length != tgts.length)
  match rhs with
  | .ternary c a b =>
    elabStmtsP [.ite c [.tupleAssign ts a] [.tupleAssign ts b]]
  | .call f args =>
    -- a call through a value that is not a name (`s.f(x)`, `fs[i](x)`,
    -- `(h)(x)`): the callee into a fresh local of its type first, as
    -- `callValue` does, then the dispatch on that local
    if f == callValueName then
      if let h :: rest := args then
        if let some ty := fnTyOfExpr C (← ctx) h then
          let y := toString (← freshCapture "se")
          let P ← elabStmtsP [.decl (.named ty) y (some h)]
          return P ++ (← fnTupleDispatch ts y ty rest)
    -- a call through an internal function value (`fnTupleDispatch`)
    if (← read).funs.all (·.1 != f) then
      if let some ty := fnTyOf? C (← ctx) f then
        return ← fnTupleDispatch ts f ty args
    -- a function not declared before this one is `elabCallRet`'s error
    unless (castTy? f).isNone do
      throw s!"{f}(…): the right-hand side of a tuple assignment is a call of a function"
    let (P, args) ← hoistCallArgs f args
    let (Q, _, rs) ← elabCallRet f args none (targets := true)
    unless rs.length == ts.length do throw s!"{f} returns {rs.length} values, not {ts.length}"
    for (p, r, w) in rs do declare C (toString r) (.val p w)
    let pairs := if reverseWrites then (ts.zip rs).reverse else ts.zip rs
    let R ← elabStmtsP (pairs.filterMap fun (t, (_, r, _)) =>
      t.map fun t => .assign t (.name (toString r)))
    pure (P ++ Q ++ R)
  | .tuple es =>
    unless es.length == ts.length do throw s!"a tuple of {es.length} values assigned to {ts.length}"
    let mut tmps : List RawStmt := []
    let mut asgs : List RawStmt := []
    for (t, e) in ts.zip es do
      match t with
      | some t =>
        if direct then
          tmps := tmps ++ [.assign t e]
          continue
        let Γ ← ctx
        let (base, bind) ← match (← synthM C t).2 with
          | .val p _ | .path (.prim p) _ | .mpath (.prim p) _ =>
            let ty := match fnTyOfExpr C Γ t with
              | some fn => fn
              | none => match bytesOf? C Γ t with
                | some n => s!"bytes{n}"
                | none => match widthPath? C Γ t with
                  | some (ws, key, _) => declTyName ws key p
                  | none => tyName p (widthIn C Γ t)
            pure ("se", fun x => RawStmt.decl (.named ty) x (some e))
          | .mpath (.ref R) (.var ..) =>
            pure ("mv", fun x => RawStmt.declMemory (rawTyW (placeShape C Γ t) (.ref R) "") x (some e))
          | .path (.ref R) (.alias _) =>
            pure ("sp", fun x => RawStmt.declStorage (rawTyW (placeShape C Γ t) (.ref R) "") x (some e))
          | _ => throw s!"{t.toStr}: a tuple's reference target must be a local alias"
        let x := toString (← freshCapture base)
        tmps := tmps ++ [bind x]
        asgs := asgs ++ [.assign t (.name x)]
      | none => unless e.isPure do tmps := tmps ++ [.eval [e]]
    elabStmtsP (tmps ++ (if reverseWrites then asgs.reverse else asgs))
  | _ => throw s!"{rhs.toStr}: the right-hand side of a tuple assignment is a tuple or a call"

end

end Elab

end Solidity
