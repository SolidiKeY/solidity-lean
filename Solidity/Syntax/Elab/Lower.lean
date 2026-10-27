import Solidity.Syntax.Elab.Values
import Solidity.ERC7201

/-!
# The elaborator's lowerings

Inlining a call, loops lowered, and `abi.*`, `string.concat`,
`bytes.concat` with the ABI of nested types.

A piece of `Syntax/Elab.lean`, whose docstring describes the whole.
-/

namespace Solidity

open Semantics

variable {C : Contract}

variable [FreshNames]

section Elab

variable (C)


/-! ### Inline arrays -/

/-- Numeric source types that may widen implicitly. Address and byte types
retain their own source identity instead of becoming integers here. -/
def inlineNumeric? : RawTy → Option (PrimTy × Nat)
  | .named s =>
    if s == "address" then none else
    match narrowTy? s, PrimTy.ofName? s with
    | some (p, n), _ => if p.isNumeric then some (p, n) else none
    | none, some p => if p.isNumeric then some (p, 256) else none
    | _, _ => none
  | _ => none

/-- The implicit conversions relevant to a literal's common element type.
Reference elements retain exactly their element widths and finite shape. -/
def inlineImplicit (a b : RawTy) : Bool :=
  if a.toStr == b.toStr then true else
  match a, b with
  | .named s, .named t =>
    match bytesTy? s, bytesTy? t with
    | some n, some m => n ≤ m
    | some _, none | none, some _ => false
    | none, none =>
      match inlineNumeric? a, inlineNumeric? b with
      | some (p, n), some (q, m) => p == q && n ≤ m
      | _, _ => false
  | _, _ => false

/-- A still-rational literal converts directly to the current type, before
considering the literal's mobile type (solc's Type::commonType). -/
def inlineLiteralFits (T : RawTy) (e : RawExpr) : Bool :=
  match T with
  | .named s =>
    match bytesTy? s with
    | some n => match e.bytesLit?, e.litVal? with
      | some bs, _ => bs.length ≤ n
      | none, some v => v == 0
      | _, _ => false
    | none =>
      if s == "string" then e.bytesLit?.isSome else
      match inlineNumeric? T, e.litVal? with
      | some (p, n), some v =>
        let (lo, hi) := intRange p n
        lo ≤ v && v ≤ hi
      | _, _ => false
  | _ => false

mutual
/-- An inline element's source type, before hoisting erases casts and aliases.
The result is raw syntax only; allocation below rechecks it into indexed
memory statements. Nominal kinds not retained by the current frontend fail
rather than becoming integer elements. -/
partial def inlineExprTy (Γ : ECtx) (e₀ : RawExpr) : Except String RawTy := do
  let e ← e₀.foldConst
  if let some v := e.litVal? then
    let (p, n) := mobileTy v v
    let (lo, hi) := intRange p n
    unless lo ≤ v && v ≤ hi do throw "an inline array element has no mobile integer type"
    return .named (tyName p n)
  if e.bytesLit?.isSome then return .named "string"
  if (fnTyOfExpr C Γ e).isSome then
    throw "function-valued inline array elements need their nominal source type"
  if (markOf? C Γ "#enum" e).isSome then
    throw "enum-valued inline array elements need their declaration identity"
  if let some n := bytesOf? C Γ e then return .named s!"bytes{n}"
  if (markOf? C Γ "#address" e).isSome then return .named "address"
  if (exprShape C Γ e).contains ("#string", 1) then return .named "string"
  if let some (tb, k, T) := widthPath? C Γ e then return rawTyW tb T k
  match e with
  | .call "#array" es => return .fixed (← inlineArrayTy Γ es) es.length
  | .newArr T _ =>
    if let .named s := T then
      if dynBytesTy s then return T
    let (t, ws) ← elabTyW C T
    return rawTyW ws t ""
  | .call f _ =>
    if dynBytesTy f then return .named f
    if f == "string.concat" then return .named "string"
    if encodeBuiltin f && (lookupBy f C.funs).isNone then return .named "bytes"
    if let some (p, n) := castTy? f then
      return .named (if f == "address" then "address" else tyName p n)
    if let some d := lookupBy f C.funs then
      let some (r, t) := d.ret | throw s!"{f} does not return one inline array element"
      return rawTyW d.widths t r
    if let some s := C.structName? f then return .named s
    throw s!"cannot infer the inline array element type of {e.toStr}"
  | .named f _ _ =>
    if let some s := C.structName? f then return .named s
    throw s!"cannot infer the inline array element type of {e.toStr}"
  | .incDec _ l | .assign l _ | .opAssign _ l _ => inlineExprTy Γ l
  | .index b _ =>
    match ← inlineExprTy Γ b with
    | .array T | .fixed T _ => pure T
    | _ => throw s!"{b.toStr} is not an inline array element's array base"
  | .field _ "length" => pure (.named "uint")
  | .name x =>
    if (lookupBy x Γ).isNone && C.funs.any (·.1 == x) then
      throw "function-valued inline array elements need their nominal source type"
    let t ← synth C Γ.toNCtx e
    match t.ty with
    | .prim p => pure (.named (tyName p (widthIn C Γ e)))
    | .ref R => pure (rawTyW (exprShape C Γ e) (.ref R) "")
  | _ =>
    let t ← synth C Γ.toNCtx e
    match t.ty with
    | .prim p => pure (.named (tyName p (widthIn C Γ e)))
    | .ref R => pure (rawTyW (exprShape C Γ e) (.ref R) "")

/-- Solc starts at the first element's mobile type and folds implicit
conversion over later elements. The assignment target contributes no type. -/
partial def inlineArrayTy (Γ : ECtx) (es : List RawExpr) : Except String RawTy := do
  let a :: rest := es | throw "an inline array is nonempty"
  let mut T ← inlineExprTy Γ a
  for e₀ in rest do
    let e ← e₀.foldConst
    if inlineLiteralFits T e then continue
    let U ← inlineExprTy Γ e
    if inlineImplicit U T then continue
    if inlineImplicit T U then T := U
    else throw s!"inline array elements {T.toStr} and {U.toStr} have no common type"
  pure T
end


/-! ### Inlining a call -/

/-- A callee's body with its locals renamed fresh, each declaration's name
numbered as a capture of its kind is (`se`, `sp`, `mv`), and the names `ρ`
maps (its parameters and return variable) renamed: inlined, it binds no
name the caller uses. -/
partial def renameStmts (ρ : List (String × String)) : List RawStmt → ElabM (List RawStmt)
  | [] => pure []
  | s :: ss => do
    let r := RawExpr.rename ρ
    let ra (a : RawLoopSpec) : RawLoopSpec :=
      { Id.run (a.mapM (pure ∘ r)) with qinv := a.qinv.map (RawInv.rename ρ) }
    let fresh (base x : String) : ElabM (String × List (String × String)) := do
      let y := toString (← freshCapture base)
      pure (y, (x, y) :: ρ)
    match s with
    | .decl T x i =>
      let (y, ρ') ← fresh "se" x
      pure (.decl T y (i.map r) :: (← renameStmts ρ' ss))
    | .declStorage T x i =>
      let (y, ρ') ← fresh "sp" x
      pure (.declStorage T y (i.map r) :: (← renameStmts ρ' ss))
    | .declMemory T x i =>
      let (y, ρ') ← fresh "mv" x
      pure (.declMemory T y (i.map r) :: (← renameStmts ρ' ss))
    | .declStoragePush T x b =>
      let (y, ρ') ← fresh "sp" x
      pure (.declStoragePush T y (r b) :: (← renameStmts ρ' ss))
    | .declPush T x b =>
      let (y, ρ') ← fresh "se" x
      pure (.declPush T y (r b) :: (← renameStmts ρ' ss))
    | .send (some T) (.name x) e a g =>
      let (y, ρ') ← fresh "se" x
      pure (.send (some T) (.name y) (r e) (r a) g :: (← renameStmts ρ' ss))
    | .ite c t e =>
      pure (.ite (r c) (← renameStmts ρ t) (← renameStmts ρ e) :: (← renameStmts ρ ss))
    | .unchecked b => pure (.unchecked (← renameStmts ρ b) :: (← renameStmts ρ ss))
    | .checked o b => pure (.checked o (← renameStmts ρ b) :: (← renameStmts ρ ss))
    | .block b => pure (.block (← renameStmts ρ b) :: (← renameStmts ρ ss))
    | .tupleDecl vs e =>
      let mut ρ' := ρ
      let mut vs' := []
      for v in vs do
        match v with
        | some (T, x) =>
          let y := toString (← freshCapture "se")
          ρ' := (x, y) :: ρ'
          vs' := vs' ++ [some (T, y)]
        | none => vs' := vs' ++ [none]
      pure (.tupleDecl vs' (r e) :: (← renameStmts ρ' ss))
    | .tryCall e g as rets ok err code pnc other =>
      let mut ρok := ρ
      let mut rets' := []
      for (T, x) in rets do
        let y := toString (← freshCapture "se")
        ρok := (x, y) :: ρok
        rets' := rets' ++ [(T, y)]
      let (code', ρp) ← match code with
        | some x => fresh "se" x >>= fun (y, ρ') => pure (some y, ρ')
        | none => pure (none, ρ)
      pure (.tryCall (r e) g (as.map r) rets' (← renameStmts ρok ok) (← renameStmts ρ err) code'
        (← renameStmts ρp pnc) (← renameStmts ρ other) :: (← renameStmts ρ ss))
    | .whileLoop a c b =>
      pure (.whileLoop (ra a) (r c) (← renameStmts ρ b) :: (← renameStmts ρ ss))
    | .doWhile a b c =>
      pure (.doWhile (ra a) (← renameStmts ρ b) (r c) :: (← renameStmts ρ ss))
    | .loop a c b =>
      pure (.loop (ra a) (r c) (← renameStmts ρ b) :: (← renameStmts ρ ss))
    | .forLoop a [] c u b =>
      pure (.forLoop (ra a) [] (c.map r) (← renameStmts ρ u) (← renameStmts ρ b) ::
        (← renameStmts ρ ss))
    | .forLoop a i c u b =>
      -- the initialisation's declarations scope over the rest of the loop
      let out ← renameStmts ρ (i ++ [.forLoop a [] c u b])
      match out.getLast? with
      | some (.forLoop a' [] c' u' b') =>
        pure (.forLoop a' out.dropLast c' u' b' :: (← renameStmts ρ ss))
      | _ => throw "a `for` loop's initialisation, renamed"
    | s => pure ((Id.run (s.mapExprsM (pure ∘ r))) :: (← renameStmts ρ ss))

/-- `return e;`, lowered to the return variables `rs`: `r = e;` for one;
for several, `r₀ = e₀; r₁ = e₁; …` from `return (e₀, e₁, …);`, or, when a
component reads a return variable, the tuple assignment `(r₀, r₁, …) = e;`,
which reads every component before it writes (`elabTuple`; solkey's
`ReturnLowering`, `returnSwapped`).  Lean only: `return g();` of several
values is `(r₀, r₁, …) = g();`, which solkey's `ReturnLowering` refuses. -/
def lowerReturn (rs : List String) (e : RawExpr) : Except String (List RawStmt) :=
  match rs, e with
  | [], _ => throw "`return` of a value from a function that returns none"
  | [_], .tuple es => throw s!"`return` of {es.length} values from a function that returns one"
  | [n], e => pure [.assign (.name n) e]
  | rs, .tuple es =>
    if es.length != rs.length then
      throw s!"`return` of {es.length} values from a function that returns {rs.length}"
    else if es.any fun e => rs.any e.mentions then
      pure [.tupleAssign (rs.map fun n => some (.name n)) (.tuple es)]
    else pure ((rs.zip es).map fun (n, e) => .assign (.name n) e)
  | rs, e@(.call ..) => pure [.tupleAssign (rs.map fun n => some (.name n)) e]
  | rs, _ => throw s!"`return` of one value from a function that returns {rs.length}"

/-- The names a statement declares in its own block: a declaration's, a tuple
declaration's. -/
def RawStmt.declaredAll (s : RawStmt) : List String :=
  match s with
  | .tupleDecl .. => s.binds
  | s => s.declared?.toList

/-- **A body's `return`s, lowered** to assignments to its return variables
`r` (`return x + 1;` is `r = x + 1;`, `lowerReturn`), so that the run has no abrupt
completion.  What follows a `return` in its block is dead and dropped; the
statements after an `if` one of whose branches returns move into both
branches, which is where they run: `if (c) { return a; } s;` is
`if (c) { r = a; } else { s; }`.  A branch's own declarations would then be
in scope over the moved statements, so a moved statement may not name one
(Solidity scopes it to the branch); in an inlined body every local is
already fresh (`renameStmts`), and that never happens.  A block with a
`return` inside is spliced into the statements after it (solkey's
`blockReturn`, by the same guard).  A `return` inside a loop is lowered
first, to a flag (`lowerLoops`), since this cannot give an early exit from a
loop: what is left of it is the `if (ret) return;` after the outermost loop.
A function on a body as read: it may run before or
after the body is renamed. -/
partial def lowerReturns (r : List String) : List RawStmt → Except String (List RawStmt)
  | [] => pure []
  | .ret none :: _ => pure []
  | .ret (some e) :: _ => lowerReturn r e
  | .block b :: ss => do
    if b.any RawStmt.hasReturn && !ss.isEmpty then
      for x in b.flatMap RawStmt.declaredAll do
        if ss.any (·.mentions x) then
          throw s!"`return` in a block declaring {x}, which the statements after it name"
      lowerReturns r (b ++ ss)
    else
      pure (.block (← lowerReturns r b) :: (← lowerReturns r ss))
  | .ite c t e :: ss => do
    if (t.any RawStmt.hasReturn || e.any RawStmt.hasReturn) && !ss.isEmpty then
      for x in (t ++ e).flatMap RawStmt.declaredAll do
        if ss.any (·.mentions x) then
          throw s!"`return` in a branch declaring {x}, which the statements after it name"
      pure [.ite c (← lowerReturns r (t ++ ss)) (← lowerReturns r (e ++ ss))]
    else
      pure (.ite c (← lowerReturns r t) (← lowerReturns r e) :: (← lowerReturns r ss))
  | .tryCall e g as rets ok err code pnc other :: ss => do
    let bs := [ok, err, pnc, other]
    if bs.any (·.any RawStmt.hasReturn) && !ss.isEmpty then
      for x in (bs.flatten.flatMap RawStmt.declaredAll ++ rets.map (·.2) ++ code.toList) do
        if ss.any (·.mentions x) then
          throw s!"`return` in a clause declaring {x}, which the statements after it name"
      pure [.tryCall e g as rets (← lowerReturns r (ok ++ ss)) (← lowerReturns r (err ++ ss)) code
        (← lowerReturns r (pnc ++ ss)) (← lowerReturns r (other ++ ss))]
    else
      pure (.tryCall e g as rets (← lowerReturns r ok) (← lowerReturns r err) code
        (← lowerReturns r pnc) (← lowerReturns r other) :: (← lowerReturns r ss))
  | .unchecked b :: ss => do
    -- the statements after it would move into the block, and be unchecked
    if b.any RawStmt.hasReturn && !ss.isEmpty then
      throw "`return` inside `unchecked { … }` with statements after the block"
    pure (.unchecked (← lowerReturns r b) :: (← lowerReturns r ss))
  | .checked o b :: ss => do
    if b.any RawStmt.hasReturn && !ss.isEmpty then
      throw "`return` inside `checked { … }` with statements after the block"
    pure (.checked o (← lowerReturns r b) :: (← lowerReturns r ss))
  | s :: ss => do pure (s :: (← lowerReturns r ss))

/-! ### Loops, lowered

solkey's `LoopLowering` (`docs/loops.md`, Decision 2), shape for shape: a
loop's `break`, `continue` and `return` become fresh `bool` flags `brk`,
`cnt`, `ret`, made only when used; the rest of a block after a statement
that may set one runs under `if (!brk && !cnt && !ret) { … }`, testing only
the flags it may set; the loop's condition gets `!brk && !ret`; `for` and
`do … while` become a `while` (`RawStmt.loop`).  In an inlined body it runs
before `lowerReturns`, which then lowers the `if (ret) return;` after the
outermost loop as any early `return`. -/

/-- How a statement in a loop may end abruptly: solkey's `Abrupt`. -/
inductive Abrupt where
  | brk | cnt | ret
  deriving DecidableEq, Repr

/-- The kinds of `a` or `b`, in solkey's order (`brk`, `cnt`, `ret`). -/
def Abrupt.union (a b : List Abrupt) : List Abrupt :=
  [.brk, .cnt, .ret].filter fun k => a.contains k || b.contains k

/-- The flags of the loop being lowered (its `brk` and `cnt`, and the `ret`
the loops of one nest share), each made when first used; `inLoop` is false
outside every loop. -/
structure LoopFlags where
  brk : Option String := none
  cnt : Option String := none
  ret : Option String := none
  inLoop : Bool := false

/-- Lowering loops: the elaborator, and the flags of the loop being lowered. -/
abbrev LowerM := StateT LoopFlags ElabM

/-- The flag of `k`, made fresh on its first use (`brk1`, `cnt2`, `ret3`). -/
def LoopFlags.flag (k : Abrupt) : LowerM String := do
  let fl ← get
  let cur := match k with
    | .brk => fl.brk
    | .cnt => fl.cnt
    | .ret => fl.ret
  if let some x := cur then return x
  let x := toString (← freshCapture (match k with | .brk => "brk" | .cnt => "cnt" | .ret => "ret"))
  match k with
  | .brk => set { fl with brk := some x }
  | .cnt => set { fl with cnt := some x }
  | .ret => set { fl with ret := some x }
  pure x

/-- `e₁ && e₂ && … && c`, nested to the right as it reads. -/
def RawExpr.andAll (es : List RawExpr) (c : RawExpr) : RawExpr :=
  es.foldr (fun e acc => .binop .and e acc) c

/-- `!brk && !cnt && !ret`, of the flags of `ks`, before `c`; solkey's
`notAny`. -/
def notAny (ks : List Abrupt) (c : Option RawExpr := none) : LowerM RawExpr := do
  let gs ← ks.mapM fun k => do pure (RawExpr.unop .not (.name (← LoopFlags.flag k)))
  match c, gs.reverse with
  | some c, _ => pure (RawExpr.andAll gs c)
  | none, g :: rest => pure (RawExpr.andAll rest.reverse g)
  | none, [] => pure (.bool true)

/-- `bool x = b;` -/
def RawStmt.declBool (x : String) (b : Bool) : RawStmt := .decl (.named "bool") x (some (.bool b))

/-- `x = b;` -/
def RawStmt.setBool (x : String) (b : Bool) : RawStmt := .assign (.name x) (.bool b)

/-- A `break`, `continue` or `return`. -/
def RawStmt.isJump : RawStmt → Bool
  | .brk | .cont | .ret _ => true
  | _ => false

/-- Whether a `break`, `continue` or `return` occurs in the statement, at any
depth (solkey's `containsJump`). -/
def RawStmt.hasJump (s : RawStmt) : Bool :=
  s.anyDeep RawStmt.isJump

/-- Lower outside every loop: a `try`'s clauses inside a loop, which have no
jump. -/
def LowerM.outside {α : Type} (x : LowerM α) : LowerM α := do
  let fl ← get
  set ({} : LoopFlags)
  let r ← x
  set fl
  pure r

mutual

/-- A block, lowered: its statements, and how it may end abruptly.  After a
statement that may set a flag, the rest runs under `if (!flag…)`; after a
jump it is dropped. -/
partial def lowerList (rs : Option (List String)) :
    List RawStmt → LowerM (List RawStmt × List Abrupt)
  | [] => pure ([], [])
  | s :: ss => do
    let (s', ab) ← lowerStmt rs s
    if ab.isEmpty then
      let (ss', ab') ← lowerList rs ss
      pure (s' :: ss', ab')
    else if s.isJump then pure ([s'], ab)
    else
      let (ss', ab') ← lowerList rs ss
      if ss'.isEmpty then pure ([s'], ab)
      else pure ([s', .ite (← notAny ab) ss' []], Abrupt.union ab ab')

/-- A statement, lowered.  `rs` are the return variables of the body it is
in, none outside a function. -/
partial def lowerStmt (rs : Option (List String)) (s : RawStmt) :
    LowerM (RawStmt × List Abrupt) := do
  if s matches .whileLoop .. | .forLoop .. | .doWhile .. | .loop .. then return ← lowerLoop rs s
  let lowerB (b : List RawStmt) : LowerM (List RawStmt) := do pure (← lowerList rs b).1
  unless (← get).inLoop do
    return ← match s with
      | .block b => do pure (.block (← lowerB b), [])
      | .unchecked b => do pure (.unchecked (← lowerB b), [])
      | .checked o b => do pure (.checked o (← lowerB b), [])
      | .ite c t e => do pure (.ite c (← lowerB t) (← lowerB e), [])
      | .tryCall e g as rets ok err code pnc other => do
        pure (.tryCall e g as rets (← lowerB ok) (← lowerB err) code (← lowerB pnc) (← lowerB other),
          [])
      | .brk => throw "`break` outside a loop"
      | .cont => throw "`continue` outside a loop"
      | s => pure (s, [])
  match s with
  | .brk => pure (.setBool (← LoopFlags.flag .brk) true, [.brk])
  | .cont => pure (.setBool (← LoopFlags.flag .cnt) true, [.cnt])
  | .ret e =>
    let some rs := rs | throw "`return` outside a function's body"
    let pre ← match e with
      | none => pure []
      | some e => ElabM.lift (lowerReturn rs e)
    pure (.block (pre ++ [.setBool (← LoopFlags.flag .ret) true]), [.ret])
  | .block b => do
    let (b', ab) ← lowerList rs b
    pure (.block b', ab)
  | .unchecked b => do
    let (b', ab) ← lowerList rs b
    pure (.unchecked b', ab)
  | .checked o b => do
    let (b', ab) ← lowerList rs b
    pure (.checked o b', ab)
  | .ite c t e => do
    let (t', a) ← lowerList rs t
    let (e', b) ← lowerList rs e
    pure (.ite c t' e', Abrupt.union a b)
  | .tryCall e g as rets ok err code pnc other => do
    if s.hasJump then throw "`break`, `continue` or `return` inside `try` inside a loop"
    LowerM.outside do
      pure (.tryCall e g as rets (← lowerB ok) (← lowerB err) code (← lowerB pnc) (← lowerB other),
        [])
  | s => pure (s, [])

/-- A loop, lowered to `RawStmt.loop`: `{ before; while (!brk && !ret && c)
{ bool cnt = false; body } }`, with what `for` and `do … while` add, and
`if (ret) return;` after the outermost loop of a nest with a `return`. -/
partial def lowerLoop (rs : Option (List String)) (s : RawStmt) :
    LowerM (RawStmt × List Abrupt) := do
  let (spec, c, init, upd, body, isDo) := match s with
    | .forLoop a i c u b => (a, c.getD (.bool true), i, u, b, false)
    | .doWhile a b c => (a, c, [], [], b, true)
    | .whileLoop a c b | .loop a c b => (a, c, [], [], b, false)
    | _ => ({}, .bool true, [], [], [], false)
  -- An effectful while condition is a statement at the iteration head, not
  -- a prefix outside the loop. Lower its synthetic break with the original
  -- jumps, so continue rechecks it and break/return suppress another check.
  if (s matches .whileLoop ..) && c.hasIncDec && spec.inv.isEmpty &&
      spec.qinv.isEmpty && spec.dec.isNone && spec.unwind.isNone then
    return ← lowerLoop rs (.whileLoop spec (.bool true)
      [.ite (.unop .not c) [.brk] [], .block body])
  let outer ← get
  let outermost := !outer.inLoop
  set ({ ret := if outermost then none else outer.ret, inLoop := true } : LoopFlags)
  let (body', ab) ← lowerList rs body
  let exits := ab.filter (· != .cnt)
  let mut before : List RawStmt := init
  let mut iter : List RawStmt := []
  let mut cond := c
  -- the flags the condition reads, which an invariant says are `bool`s
  let mut heads : List String := []
  if isDo then
    let first := toString (← freshCapture "first")
    before := before ++ [.declBool first true]
    iter := [.setBool first false]
    cond := .binop .or (.name first) cond
    heads := heads ++ [first]
  if let some x := (← get).cnt then iter := iter ++ [.declBool x false]
  iter := iter ++ body'
  unless upd.isEmpty do
    if exits.isEmpty then iter := iter ++ upd
    else iter := iter ++ [.ite (← notAny exits) upd []]
  unless exits.isEmpty do cond ← notAny exits (some cond)
  let fl ← get
  if exits.contains .brk then heads := heads ++ fl.brk.toList
  if exits.contains .ret then heads := heads ++ fl.ret.toList
  if let some x := fl.brk then before := before ++ [.declBool x false]
  let returns := exits.contains .ret
  let retX := fl.ret.getD ""
  if returns && outermost then before := before ++ [.declBool retX false]
  set { outer with ret := if outermost then outer.ret else fl.ret }
  -- Lean's locals are untyped: an invariant says the flags its condition
  -- reads hold a `bool` (`f || !f` is defined exactly then), which KeY's
  -- types say of `brk`, `ret` and `first`
  let spec := if spec.inv.isEmpty && spec.qinv.isEmpty then spec else
    { spec with inv := spec.inv ++ heads.map fun f => .binop .or (.name f) (.unop .not (.name f)),
                brk := spec.brk || exits.contains .brk }
  let w := RawStmt.loop spec cond iter
  let ab' := if returns then [Abrupt.ret] else []
  if before.isEmpty && !(returns && outermost) then return (w, ab')
  if returns && outermost then
    return (.block (before ++ [w, .ite (.name retX) [.ret none] []]), [])
  pure (.block (before ++ [w]), ab')

end

/-- **Loops, lowered** in a block (`lowerList`), outside every loop. -/
def lowerLoops (rs : Option (List String)) (ss : List RawStmt) : ElabM (List RawStmt) := do
  pure (← (lowerList rs ss).run' {}).1

/-- Whether a `_;` occurs in the statement, at any depth. -/
def RawStmt.hasHole (s : RawStmt) : Bool :=
  s.anyDeep (· matches .hole)

/-- A modifier's body with each `_;` the block `inner`, at any depth.  Not
inside `unchecked`, as solc refuses it there. -/
partial def RawStmt.fillHole (inner : List RawStmt) (s : RawStmt) : Except String RawStmt :=
  let go := fun (b : List RawStmt) => b.mapM (RawStmt.fillHole inner)
  match s with
  | .hole => pure (.block inner)
  | .ite c t e => return .ite c (← go t) (← go e)
  | .block b => return .block (← go b)
  | .unchecked b =>
    if b.any RawStmt.hasHole then throw "`_;` inside `unchecked { … }`" else pure (.unchecked b)
  | .checked o b => return .checked o (← go b)
  | .tryCall e g as rets ok err code pnc other =>
    return .tryCall e g as rets (← go ok) (← go err) code (← go pnc) (← go other)
  | .whileLoop a c b => return .whileLoop a c (← go b)
  | .doWhile a b c => return .doWhile a (← go b) c
  | .loop a c b => return .loop a c (← go b)
  | .forLoop a i c u b => return .forLoop a i c u (← go b)
  | s => pure s

/-- **Modifiers, inlined** around a function's body (its locals already
fresh), the first listed outermost, as solc runs them: a modifier's
parameters are declared fresh with its arguments (read in the function's
scope, and evaluated when the modifier is entered: after the code before
the `_;` of the modifiers outside it), then its body with each `_;` the
next modifier (or the function's body), as a block.  A modifier's locals are
renamed fresh, so the body cannot see them.  A `return` in the body is
its last statement and one in a modifier that modifier's (`lowerReturns`,
before its `_;` is filled), so the code after `_;` runs after either, as
it does in solc.  A body run by several
`_;` (or by one in a loop) is run again in the same locals, its parameters
and return variables not reset: solc's legacy pipeline (via-IR resets
them). -/
partial def wrapMods (body : List RawStmt) : List ModApp → ElabM (List RawStmt)
  | [] => pure body
  | m :: ms => do
    let inner ← wrapMods body ms
    unless m.params.length == m.args.length do
      throw s!"modifier {m.name} takes {m.params.length} arguments, not {m.args.length}"
    let mut ρ : List (String × String) := []
    let mut decls : List RawStmt := []
    for ((n, T), a) in m.params.zip m.args do
      -- a narrow parameter (`uint8 n`) is a local of its type: its argument
      -- fits it; a reference one a local at its location, its argument's
      -- narrow positions checked against its own (`shapeCheck`): a storage
      -- one an alias, a memory one bound as `T memory y = a;` binds it
      match T with
      | .prim p =>
        let y := toString (← freshCapture "se")
        decls := decls ++ [.decl (.named (declTyName m.widths n p)) y (some a)]
        ρ := (n, y) :: ρ
      | .ref _ =>
        let rt := rawTyW m.widths T n
        match lookupBy n m.locs with
        | some .storage =>
          let y := toString (← freshCapture "sp")
          decls := decls ++ [.declStorage rt y (some a)]
          ρ := (n, y) :: ρ
        | some .memory =>
          let y := toString (← freshCapture "mv")
          decls := decls ++ [.declMemory rt y (some a)]
          ρ := (n, y) :: ρ
        | _ => throw s!"modifier {m.name}: the reference parameter {n} is in memory or storage"
    let code ← renameStmts ρ m.body
    -- a `return` ends the modifier alone: the code after the `_;` of the
    -- modifiers outside it still runs (solc's legacy pipeline)
    let code ← if code.any RawStmt.hasReturn then
        ElabM.lift (lowerReturns [] (← lowerLoops (some []) code))
      else pure code
    pure (decls ++ (← ElabM.lift (code.mapM (RawStmt.fillHole inner))))

/-- The statements of `unchecked { … }` with their arithmetic wrapping: `x += 1;`
and `x++;` are `x = x +% 1;`.  A call's callee stays checked, as in solc. -/
partial def uncheckStmts : List RawStmt → Except String (List RawStmt)
  | [] => pure []
  | s :: ss => do
    let s' ← match s with
      | .opAssign op l e => do
        let op' : BinOp := match op with | .add => .addW | .sub => .subW | .mul => .mulW | op => op
        pure (.opAssign op' (← l.uncheck) (← e.uncheck))
      | .incDec op l => do
        pure (.opAssign (if op.isIncrement then .addW else .subW) (← l.uncheck) (.num 1))
      | .assignIncDec .. => throw "`v = x++;` inside `unchecked`: write `v = x; x += 1;`"
      -- the push's value, wrapping, is `elabStmtP`'s (`b.push(uint8(0 +% r))`)
      | .pushOpAssign op b r => do pure (.pushOpAssign op (← b.uncheck) (← r.uncheck))
      | .pushIncDec op b => do pure (.pushIncDec op (← b.uncheck))
      | .ite c t e => do pure (.ite (← c.uncheck) (← uncheckStmts t) (← uncheckStmts e))
      | .unchecked b => do pure (.unchecked (← uncheckStmts b))
      | .checked .checking _ => throw "`checked { … }` inside `unchecked { … }`: its operations wrap there"
      | .checked o b => do pure (.checked o (← uncheckStmts b))
      | .block b => do pure (.block (← uncheckStmts b))
      | .tryCall e g as rets ok err code pnc other => do
        pure (.tryCall (← e.uncheck) g (← as.mapM RawExpr.uncheck) rets (← uncheckStmts ok)
          (← uncheckStmts err) code (← uncheckStmts pnc) (← uncheckStmts other))
      -- a loop's specification is not a program's arithmetic: it stays as written
      | .whileLoop a c b => do pure (.whileLoop a (← c.uncheck) (← uncheckStmts b))
      | .doWhile a b c => do pure (.doWhile a (← uncheckStmts b) (← c.uncheck))
      | .loop a c b => do pure (.loop a (← c.uncheck) (← uncheckStmts b))
      | .forLoop a i c u b => do
        pure (.forLoop a (← uncheckStmts i) (← c.mapM RawExpr.uncheck) (← uncheckStmts u)
          (← uncheckStmts b))
      | s => s.mapExprsM RawExpr.uncheck
    pure (s' :: (← uncheckStmts ss))

/-- Why a call of `f`, returning a `T` that is a reference, is refused. -/
def refReturnMsg (f : String) (T : Ty) : String :=
  s!"{f} returns a reference ({T}): a call's value is a value type"

/-- What a call returns, before the context it is read in is known: nothing,
the value of `r`, the return variables `rs` (a tuple's, an obligation's), or
the memory or storage return `r`. -/
inductive RetKind where
  | none
  | val (p : PrimTy) (r : Var)
  | rets (rs : List (PrimTy × Var))
  | mem (R : RefTy) (r : Var)
  | storage (R : RefTy) (r : Var)

/-- An expression in the frame of an external call the contract makes to
itself: `msg.sender` is the contract, `msg.value` is `v` (nothing for a
`try`, which sends no value). -/
def RawExpr.selfFrame (v : RawExpr) (e : RawExpr) : RawExpr :=
  Id.run <| e.mapM fun
    | .env .msgSender => .env .selfAddress
    | .env .msgValue => v
    | e => e

/-- `RawExpr.selfFrame` in every expression of the statement, at any depth. -/
partial def RawStmt.selfFrame (v : RawExpr) (s : RawStmt) : RawStmt :=
  (Id.run (s.mapExprsM (pure ∘ RawExpr.selfFrame v))).mapBlocks (·.map (RawStmt.selfFrame v))

/-- A simple value as the expression that reads it back, its locals by
name (`ns`). -/
def Simple.toRaw {Γ : Ctx} {p : PrimTy} (ns : List Var) : Simple C Γ p → RawExpr
  | .lit n _ => if n < 0 then .unop .neg (.num n.natAbs) else .num n.toNat
  | .bool b => .bool b
  | .local i => .name (toString (i.name ns))
  | .env k _ => .env k

/-- The parts of an inlined call with return variables `ρ`: its arguments
and its body.  A `try` that binds none (`ρ = []`) of a callee that returns
values runs it as a call statement: its return variable declared at the
head of its body (`.val`), or its returns declared there already (`.none`). -/
def Stmt.selfCall? {Γ Γ' : Ctx} (ρ : Ctx) : Stmt C Γ Γ' →
    Option ((ps : Ctx) × (Γf : Ctx) × Args C Γ ps × Prog C (ρ ++ ps) Γf)
  | .call (rs := rs) _ as (.rets _) b => if h : rs = ρ then some ⟨_, _, as, h ▸ b⟩ else none
  | .call _ as (.val p r _) b =>
    if h : ([] : Ctx) = ρ then
      some ⟨_, _, as, h ▸ (Prog.cons (Stmt.declLocal p r none) b : Prog C ([] ++ _) _)⟩
    else none
  | .call _ as .none b => if h : ([] : Ctx) = ρ then some ⟨_, _, as, h ▸ b⟩ else none
  | _ => none

/-! ### `abi.*`, `string.concat`, `bytes.concat`

Solidity's ABI layout, not the EVM's: each builtin is lowered here to a fresh
memory `bytes` of solc's bytes (`docs/semantic-gaps.md`, "Hashing and the
ABI"), written byte by byte with the array writes the model has.  A value
is read at its static type (`AbiKind`): `abi.encode` writes it as a 32-byte
word, big-endian (an `intN` sign-extended, a `bytesN` left-aligned, a
`bool` `0`/`1`), a `bytes`/`string` as an offset in the head and its length
and bytes, padded to 32, in the tail; `abi.encodePacked` (and the two
`concat`s) writes each value in its own width and a byte string's bytes
bare. Addresses, enums and external function values retain their source
widths (20, 1 and 24 bytes respectively). -/

/-- How `abi.encode` sees a value: its static type. -/
inductive AbiKind where
  | uint (n : Nat) | int (n : Nat) | bool | bytesN (n : Nat)
  /-- `bytes` or `string`. -/
  | dyn
  /-- A dynamic array of values of the kind: its offset in the head, its
  length and its elements' words in the tail. -/
  | arr (k : AbiKind)
  /-- A fixed-size array of `n` values: their words in the head. -/
  | fixed (k : AbiKind) (n : Nat)
  /-- A struct of value members (the struct, by its name in the table): their
  words in the head (`AbiKind.ofStruct`). -/
  | tuple (s : String)
  deriving Inhabited, BEq

/-- The width in bytes a packed value takes. -/
def AbiKind.packedWidth : AbiKind → Nat
  | .uint n | .int n => n / 8
  | .bool => 1
  | .bytesN n => n
  | .dyn | .arr _ | .tuple _ => 0
  | .fixed _ n => 32 * n

/-- The kind of a value of type `p` at the key `k` of the width table `ws`:
its width, a `bytesN`'s, an `address`'s 20 bytes, an enum's one. -/
def AbiKind.ofValue (p : PrimTy) (ws : List (String × Nat)) (k : String) : AbiKind :=
  match p with
  | .bool => .bool
  | .int => .int ((lookupBy k ws).getD 256)
  | .uint =>
    match lookupBy (k ++ "#bytes") ws with
    | some n => .bytesN n
    | none =>
      if ((fnRow? ws k).bind fnParts?).any (·.2.2) then .bytesN 24
      else if (lookupBy (k ++ "#address") ws).isSome then .uint 160
      else if (lookupBy (k ++ "#enum") ws).isSome then .uint 8
      else .uint ((lookupBy k ws).getD 256)

/-- A struct's members' kinds, if every member is a value. -/
def AbiKind.ofStruct (s : String) : Option (List (String × AbiKind)) :=
  (structDef s).mapM fun (f, T) => match T with
    | .prim p =>
      if ((fnRow? (structWidths s) f).bind fnParts?).any (!·.2.2) then none
      else some (f, AbiKind.ofValue p (structWidths s) f)
    | .ref _ => none

/-- The words a value of the kind takes in `abi.encode`'s head. -/
def AbiKind.headWords : AbiKind → Nat
  | .fixed _ n => n
  | .tuple s => ((AbiKind.ofStruct s).map List.length).getD 1
  | _ => 1

/-- `a + n`, folded on a literal. -/
def RawExpr.addN (a : RawExpr) (n : Nat) : RawExpr :=
  if n == 0 then a else match a with
    | .num m => .num (m + n)
    | _ => .binop .add a (.num n)

/-- The `m` bytes of the value `w`, big-endian, written at `r[o]` …
`r[o + m - 1]`. -/
def abiBytes (r : String) (o w : RawExpr) (m : Nat) : List RawStmt :=
  (List.range m).map fun j =>
    .assign (.index (.name r) (o.addN j))
      (.call "uint8" [.binop .shr w (.num (8 * (m - 1 - j)))])

/-- `abiBytes` of a literal word: its bytes known, only those not zero
written (`new` left the others zero). -/
def abiLitBytes (r : String) (o : RawExpr) (w : Nat) (m : Nat) : List RawStmt :=
  (List.range m).filterMap fun j =>
    let b := w / 2 ^ (8 * (m - 1 - j)) % 256
    if b == 0 then none else some (.assign (.index (.name r) (o.addN j)) (.num b))

/-- The literal word of a literal value of kind `k`: a number (an `int`'s
two's complement), `true`/`false`. -/
def AbiKind.litWord? (k : AbiKind) (e : RawExpr) : Option Nat :=
  match k, e with
  | .bool, .bool b => some (if b then 1 else 0)
  | .bool, _ => none
  | _, e => e.litVal?.map fun v => if v < 0 then (2 ^ 256 + v).toNat else v.toNat

/-- The word a value of kind `k` is encoded as, a `uint`. -/
def AbiKind.word (k : AbiKind) (e : RawExpr) : RawExpr :=
  match k with
  | .int _ => .unop .toUint e
  | .bool => .ternary e (.num 1) (.num 0)
  | _ => e

/-- `abi.encode`'s writes of a static value of kind `k`, its word `w`, at the
offset `o` (an expression): as `abiEncodeStatic`. -/
def abiEncodeStaticE (r : String) (o : RawExpr) (k : AbiKind) (w : RawExpr) : List RawStmt :=
  match k with
  | .uint n => abiBytes r (o.addN (32 - n / 8)) w (n / 8)
  | .bool => abiBytes r (o.addN 31) w 1
  | .bytesN n => abiBytes r o w n
  | _ => abiBytes r o w 32

/-- `abi.encode`'s writes of a static value of kind `k`, its word `w`, at
the head offset `o`: the word's bytes where they are not the zero `new`
left (a `uintN`'s low `N/8`, a `bool`'s last), a `bytesN` left-aligned. -/
def abiEncodeStatic (r : String) (o : Nat) (k : AbiKind) (w : RawExpr) : List RawStmt :=
  match k with
  | .uint n => abiBytes r (.num (o + 32 - n / 8)) w (n / 8)
  | .bool => abiBytes r (.num (o + 31)) w 1
  | .bytesN n => abiBytes r (.num o) w n
  | _ => abiBytes r (.num o) w 32

/-- The `m` bytes of the word named `x` (`#v` a literal word `v`) at `r[o]`. -/
def abiWrite (r : String) (o : RawExpr) (x : String) (m : Nat) : List RawStmt :=
  if x.startsWith "#" then abiLitBytes r o (x.drop 1).toNat! m else abiBytes r o (.name x) m

/-- `abiEncodeStatic` of the word named `x` (`#v` a literal word `v`). -/
def abiStatic (r : String) (o : Nat) (k : AbiKind) (x : String) : List RawStmt :=
  if x.startsWith "#" then
    let v := (x.drop 1).toNat!
    match k with
    | .uint n => abiLitBytes r (.num (o + 32 - n / 8)) v (n / 8)
    | .bool => abiLitBytes r (.num (o + 31)) v 1
    | .bytesN n => abiLitBytes r (.num o) v n
    | _ => abiLitBytes r (.num o) v 32
  else abiEncodeStatic r o k (.name x)

/-- `j = 0; while (j < L) { r[o + j] = x[j]; j = j + 1; }`: the bytes of
`x` copied to `r` at `o`. -/
def abiCopy (r x j L : String) (o : RawExpr) : List RawStmt :=
  [.decl (.named "uint") j (some (.num 0)),
   .whileLoop {} (.binop .lt (.name j) (.name L))
     [.assign (.index (.name r) (.binop .add o (.name j))) (.index (.name x) (.name j)),
      .assign (.name j) (.binop .add (.name j) (.num 1))]]

/-- `(L + 31) / 32 * 32`: a length padded to whole words. -/
def abiPad (L : RawExpr) : RawExpr := .binop .mul (.binop .div (L.addN 31) (.num 32)) (.num 32)

/-- The bytes a decoder reads: a memory `bytes` named `d`, or a view of it
(a calldata slice, `#sliceV`): its bytes from the offset `off`, `len` of
them. -/
structure ByteSrc where
  d : String
  off : Option RawExpr := none
  len? : Option RawExpr := none

instance : Coe String ByteSrc := ⟨fun d => { d }⟩

/-- How many bytes it has. -/
def ByteSrc.len (s : ByteSrc) : RawExpr := s.len?.getD (.field (.name s.d) "length")

/-- `d[o]`, a byte of `d` (of the view: `d[off + o]`). -/
def abiByte (d : ByteSrc) (o : RawExpr) : RawExpr :=
  .index (.name d.d) (match d.off, o with
    | some (.num b), .num c => .num (b + c)
    | some b, o => .binop .add b o
    | none, o => o)

/-- The `m` bytes of `d` from `o` read big-endian into the `uint` local `w`:
`w = d[o]; w = w * 256 + d[o + 1]; …`. -/
def abiAssemble (d : ByteSrc) (w : String) (o : RawExpr) (m : Nat) : List RawStmt :=
  .decl (.named "uint") w (some (abiByte d o)) ::
    (List.range (m - 1)).map fun j =>
      .assign (.name w) (.binop .add (.binop .mul (.name w) (.num 256)) (abiByte d (o.addN (j + 1))))

/-- `require(d[o + p] == 0)` for each `p` of `ps`. -/
def abiZeros (d : ByteSrc) (o : RawExpr) (ps : List Nat) : List RawStmt :=
  ps.map fun p => .require (.binop .eqB (abiByte d (o.addN p)) (.num 0))

/-- `abi.decode` of the word at byte `o` of `d` at the type `T`: its checks
(solc's decoder reverts on a word out of the type's range: a high byte not
zero, or not the sign's, a `bool` above `1`), the bytes it reads into the
local `w`, and its value.  `none` for a type it does not decode.  A narrow
type reads only its own bytes into `w`; the others it compares with `0`
one by one. -/
def abiDecodeAt (T : String) (d : ByteSrc) (w : String) (o : RawExpr) : Option (List RawStmt × RawExpr) :=
  let unsigned (m : Nat) (v : RawExpr) : List RawStmt × RawExpr :=
    (abiZeros d o (List.range (32 - m)) ++ abiAssemble d w (o.addN (32 - m)) m, v)
  if T == "bool" then
    some (abiZeros d o (List.range 31) ++
      [.require (.binop .lt (abiByte d (o.addN 31)) (.num 2))],
      .binop .eqB (abiByte d (o.addN 31)) (.num 1))
  else if T == "address" then some (unsigned 20 (.name w))
  else if T == "uint" || T == "uint256" then some (abiAssemble d w o 32, .name w)
  else if T == "int" || T == "int256" then some (abiAssemble d w o 32, .call "int256" [.name w])
  else match narrowTy? T, bytesTy? T with
    | some (.uint, n), _ => some (unsigned (n / 8) (.call T [.name w]))
    | some (.int, n), _ =>
      let m := n / 8
      -- the high bytes are the sign's: `0xff` below a byte of `128` or more
      let sign : RawExpr :=
        .ternary (.binop .ge (abiByte d (o.addN (32 - m))) (.num 128)) (.num 255) (.num 0)
      some ((List.range (32 - m)).map (fun p => .require (.binop .eqB (abiByte d (o.addN p)) sign)) ++
        abiAssemble d w (o.addN (32 - m)) m, .call T [.name w])
    | _, some n =>
      some (abiZeros d (o.addN n) (List.range (32 - n)) ++ abiAssemble d w o n,
        .call T [.name w])
    | _, _ => none

/-- The name of the hidden builtin `abi.decode` of one component is lowered
through: `#abiDecode(d, T, i, n)`, the `i`-th of `n` words of `d` read at `T`. -/
def abiDecodeName : String := "#abiDecode"

/-- `revert E(a, b)`'s data, where a `try` reads it: `E`'s selector, folded
as solc folds it (`errorSignature?`), then each argument's ABI word, a
literal's folded to its bytes. -/
def revertErrParts (Γ : NCtx) (e : String) (args : List RawExpr) :
    ElabM (List (RevPart C Γ.ctx)) := do
  let some (d, sig) := errorSignature? C e |
    throw s!"`{e}` is not an error this contract declares with value parameters"
  unless d.params.length == args.length do
    throw s!"`{e}` takes {d.params.length} arguments, given {args.length}"
  let parts ← (d.params.zip args).mapM fun ((n, T), a) => do
    -- The model stores bytesN as its compact uint8N value. ABI words put
    -- those N bytes at the left; uint/int/address words remain right-aligned.
    -- Read the declaration, since eager captures may have erased the marker.
    let a ← match lookupBy (n ++ "#bytes") d.widths with
      | none => pure a
      | some w => do
        unless T == .prim .uint && 0 < w && w ≤ 32 do
          throw s!"`{e}`: invalid fixed-byte custom-error parameter {n}"
        let shift := 8 * (32 - w)
        pure (match a with
          | .num k => .num (k * 2 ^ shift)
          -- checkIn constructs the intrinsic uint Val directly below. Its
          -- shift is 256-bit already; raw casts inserted after hoisting are
          -- not expressions synth can accept and would lose the self body.
          | a => .binop .shl a (.num shift))
    match T, a with
    | .prim _, .num n => pure (RevPart.bytes (Semantics.wordBytes n))
    | .prim _, .bool b => pure (RevPart.bytes (Semantics.wordBytes (if b then 1 else 0)))
    | .prim p, a => pure (RevPart.word (← checkIn C Γ p a))
    | _, _ => throw s!"`{e}`: a custom error's reference argument is not modelled"
  pure (.bytes (Semantics.selectorBytes (Semantics.customSelector sig)) :: parts)

/-- A value type's ABI kind, by its name (`abi.decode`'s components). -/
def valueKind? (t : String) : Option AbiKind :=
  if t == "bool" then some .bool
  else if t == "address" then some (.uint 160)
  else if t == "uint" || t == "uint256" then some (.uint 256)
  else if t == "int" || t == "int256" then some (.int 256)
  else match narrowTy? t, bytesTy? t with
    | some (.uint, n), _ => some (.uint n)
    | some (.int, n), _ => some (.int n)
    | _, some n => some (.bytesN n)
    | _, _ => none

/-- The value type name a kind decodes at (`abiDecodeAt`): an address as a
`uint160`, which an `address` takes. -/
def AbiKind.tyName : AbiKind → String
  | .bool => "bool"
  | .uint n => s!"uint{n}"
  | .int n => s!"int{n}"
  | .bytesN n => s!"bytes{n}"
  | _ => "uint256"

/-! ### The ABI of nested types (lane `open-abi2`)

`abi.encode` and `abi.decode` of an array of references (`uint[][]`,
`bytes[]`, `S[]`), of a struct with a reference member (a `uint[]`, a
`bytes`, a struct), and of a fixed array of either: solc's layout, head and
tail recursively (the ABI specification's `enc`).  A dynamic component is
an offset in its tuple's head, relative to the tuple's start, and its
encoding in the tail; a static one its words in the head; an array a
length word and then the tuple of its elements.  `AbiTy` is the type
read off a place's `Ty` and its rows (`AbiTy.of`); the writer and the
reader below are statements with a loop per sequence (`abiSeqWriteGen`,
`abiSeqReadGen`), a size computed before the buffer is allocated
(`abiSizeGen`), each word the decoder reads checked within the data
first.  The types the flat encoder and decoder already read (`AbiKind`)
stay theirs (`AbiTy.flat`). -/

/-- An ABI type, nested. -/
inductive AbiTy where
  | val (k : AbiKind)
  /-- `bytes` or `string`. -/
  | bytes
  | arr (t : AbiTy)
  | fixed (t : AbiTy) (n : Nat)
  /-- A struct, by its name, and its members. -/
  | tuple (s : String) (ms : List (String × AbiTy))
  deriving Inhabited

/-- Whether its encoding is in a tail (solc's dynamic types). -/
partial def AbiTy.dynamic : AbiTy → Bool
  | .val _ => false
  | .bytes | .arr _ => true
  | .fixed t _ => t.dynamic
  | .tuple _ ms => ms.any (·.2.dynamic)

/-- The bytes it takes in its tuple's head. -/
partial def AbiTy.headSize (t : AbiTy) : Nat :=
  if t.dynamic then 32 else
    match t with
    | .fixed t n => n * t.headSize
    | .tuple _ ms => (ms.map (·.2.headSize)).sum
    | _ => 32

/-- What the flat encoder and decoder read (`AbiKind`). -/
def AbiTy.flat : AbiTy → Bool
  | .val _ | .bytes | .arr (.val _) | .fixed (.val _) _ => true
  | .tuple _ ms => ms.all (·.2 matches .val _)
  | _ => false

/-- The ABI type of a `Ty` whose rows (`placeShape`, `structWidths`) are
keyed below `k`: `none` for a mapping. -/
partial def AbiTy.of (T : Ty) (ws : List (String × Nat)) (k : String) : Option AbiTy :=
  match T with
  | .prim p =>
    if ((fnRow? ws k).bind fnParts?).any (!·.2.2) then none
    else some (.val (AbiKind.ofValue p ws k))
  | .ref (.array t) =>
    if lookupBy (k ++ "[]#bytes") ws == some 1 then some .bytes
    else (AbiTy.of t ws (k ++ "[]")).map .arr
  | .ref (.fixed t n) => (AbiTy.of t ws (k ++ "[]")).map (.fixed · n)
  | .ref (.struct s) =>
    ((structDef s).mapM fun (f, T) => (AbiTy.of T (structWidths s) f).map (f, ·)).map (.tuple s)
  | .ref (.mapping ..) => none

/-- The type a decoded value of `T` (rows `ws` below `k`) is declared at. -/
partial def abiRawTy (T : Ty) (ws : List (String × Nat)) (k : String) : RawTy :=
  match T with
  | .prim p =>
    match AbiKind.ofValue p ws k with
    | .uint 160 => if (lookupBy (k ++ "#address") ws).isSome then .named "address" else .named "uint160"
    | kk => .named kk.tyName
  | .ref (.array t) =>
    if lookupBy (k ++ "[]#bytes") ws == some 1 then
      .named (if (lookupBy (k ++ "#string") ws).isSome then "string" else "bytes")
    else .array (abiRawTy t ws (k ++ "[]"))
  | .ref (.fixed t n) => .fixed (abiRawTy t ws (k ++ "[]")) n
  | .ref (.struct s) => .named s
  | .ref (.mapping ..) => .named "uint"

/-- The element type of an array type. -/
def RawTy.elem : RawTy → RawTy
  | .array t | .fixed t _ => t
  | t => t

/-- A struct member's declared type (`abiRawTy` of its rows). -/
def abiMemberTy (s f : String) : RawTy :=
  match lookupBy f (structDef s) with
  | some T => abiRawTy T (structWidths s) f
  | none => .named "uint"

/-- A fresh `uint` local's name. -/
def abiFresh : ElabM String := do pure (toString (← freshCapture "se"))

mutual

/-- The size in bytes of `v`'s encoding at `t`: the statements computing it,
and it. -/
partial def abiSizeGen (t : AbiTy) (v : RawExpr) : ElabM (List RawStmt × RawExpr) := do
  if !t.dynamic then return ([], .num t.headSize)
  match t with
  | .bytes => pure ([], (abiPad (.field v "length")).addN 32)
  | .arr e =>
    if !e.dynamic then
      pure ([], (RawExpr.binop .mul (.num e.headSize) (.field v "length")).addN 32)
    else
      let (ss, n) ← abiSeqSizeGen e (.field v "length") (.index v)
      pure (ss, n.addN 32)
  | .fixed e n => abiSeqSizeGen e (.num n) (.index v)
  | .tuple _ ms => abiTupleSizeGen (ms.map fun (f, mt) => (mt, .field v f))
  | _ => pure ([], .num 32)

/-- Of `L` dynamic elements: their offsets and their encodings. -/
partial def abiSeqSizeGen (e : AbiTy) (L : RawExpr) (elem : RawExpr → RawExpr) :
    ElabM (List RawStmt × RawExpr) := do
  let acc ← abiFresh
  let i ← abiFresh
  let (ss, n) ← abiSizeGen e (elem (.name i))
  pure ([.decl (.named "uint") acc (some (.binop .mul (.num 32) L)),
    .decl (.named "uint") i (some (.num 0)),
    .whileLoop {} (.binop .lt (.name i) L)
      (ss ++ [.assign (.name acc) (.binop .add (.name acc) n),
        .assign (.name i) (.binop .add (.name i) (.num 1))])], .name acc)

/-- Of a tuple: its head and its dynamic components' tails. -/
partial def abiTupleSizeGen (ms : List (AbiTy × RawExpr)) : ElabM (List RawStmt × RawExpr) := do
  let mut ss : List RawStmt := []
  let mut tot : RawExpr := .num (ms.map (·.1.headSize)).sum
  for (mt, mv) in ms do
    if mt.dynamic then
      let (s1, n) ← abiSizeGen mt mv
      ss := ss ++ s1
      tot := .binop .add tot n
  pure (ss, tot)

end

mutual

/-- The encoding of `v` at `t`, written into `r` from the position `p` (a
local). -/
partial def abiWriteGen (r : String) (t : AbiTy) (v : RawExpr) (p : String) :
    ElabM (List RawStmt) := do
  match t with
  | .val k =>
    let w ← abiFresh
    pure (.decl (.named "uint") w (some (k.word v)) :: abiEncodeStaticE r (.name p) k (.name w))
  | .bytes =>
    let L ← abiFresh
    let j ← abiFresh
    let start : RawExpr := (RawExpr.name p).addN 32
    pure ([.decl (.named "uint") L (some (.field v "length"))] ++ abiBytes r (.name p) (.name L) 32 ++
      [.decl (.named "uint") j (some (.num 0)),
       .whileLoop {} (.binop .lt (.name j) (.name L))
         [.assign (.index (.name r) (.binop .add start (.name j))) (.index v (.name j)),
          .assign (.name j) (.binop .add (.name j) (.num 1))]])
  | .arr e =>
    let L ← abiFresh
    let q ← abiFresh
    pure ([.decl (.named "uint") L (some (.field v "length"))] ++ abiBytes r (.name p) (.name L) 32 ++
      [.decl (.named "uint") q (some ((RawExpr.name p).addN 32))] ++
      (← abiSeqWriteGen r e (.name L) (.index v) q))
  | .fixed e n => abiSeqWriteGen r e (.num n) (.index v) p
  | .tuple _ ms => abiTupleWriteGen r (ms.map fun (f, mt) => (mt, .field v f)) p

/-- `L` elements as a tuple from `q`: each in place if static, else an
offset from `q` and its encoding in the tail. -/
partial def abiSeqWriteGen (r : String) (e : AbiTy) (L : RawExpr) (elem : RawExpr → RawExpr)
    (q : String) : ElabM (List RawStmt) := do
  let i ← abiFresh
  let pos ← abiFresh
  let next := RawStmt.assign (.name i) (.binop .add (.name i) (.num 1))
  if !e.dynamic then
    let body ← abiWriteGen r e (elem (.name i)) pos
    return [.decl (.named "uint") i (some (.num 0)),
      .whileLoop {} (.binop .lt (.name i) L)
        ([.decl (.named "uint") pos
          (some (.binop .add (.name q) (.binop .mul (.num e.headSize) (.name i))))] ++ body ++ [next])]
  let c ← abiFresh
  let off ← abiFresh
  let body ← abiWriteGen r e (elem (.name i)) c
  let (ss, n) ← abiSizeGen e (elem (.name i))
  pure [.decl (.named "uint") c (some (.binop .add (.name q) (.binop .mul (.num 32) L))),
    .decl (.named "uint") i (some (.num 0)),
    .whileLoop {} (.binop .lt (.name i) L)
      ([.decl (.named "uint") pos (some (.binop .add (.name q) (.binop .mul (.num 32) (.name i)))),
        .decl (.named "uint") off (some (.binop .sub (.name c) (.name q)))] ++
        abiBytes r (.name pos) (.name off) 32 ++ body ++ ss ++
        [.assign (.name c) (.binop .add (.name c) n), next])]

/-- A tuple's components from `p`: the head in order, each dynamic one's
offset from `p` there and its encoding at the tail's end. -/
partial def abiTupleWriteGen (r : String) (ms : List (AbiTy × RawExpr)) (p : String) :
    ElabM (List RawStmt) := do
  let c ← abiFresh
  let mut ss : List RawStmt :=
    [.decl (.named "uint") c (some ((RawExpr.name p).addN (ms.map (·.1.headSize)).sum))]
  let mut hp := 0
  for (mt, mv) in ms do
    let hpos ← abiFresh
    ss := ss ++ [.decl (.named "uint") hpos (some ((RawExpr.name p).addN hp))]
    if mt.dynamic then
      let off ← abiFresh
      let (s1, n) ← abiSizeGen mt mv
      ss := ss ++ [.decl (.named "uint") off (some (.binop .sub (.name c) (.name p)))] ++
        abiBytes r (.name hpos) (.name off) 32 ++ (← abiWriteGen r mt mv c) ++ s1 ++
        [.assign (.name c) (.binop .add (.name c) n)]
    else
      ss := ss ++ (← abiWriteGen r mt mv hpos)
    hp := hp + mt.headSize
  pure ss

end

/-- **`abi.encode` of nested types** (above; `abiEncode`, outside its
`mutual` block, `abiKind` and the rest handed in): `none` where every
argument is flat, the flat encoder's.  An argument's type is its place's
(`AbiTy.of`), a value's its kind (`abiKind`, or its mark), a literal byte
string put in memory first. -/
def abiEncodeNested? (abiKind : RawExpr → ElabM AbiKind)
    (abiMemBytes : RawExpr → ElabM (SProg C × String))
    (elabStmtsP : List RawStmt → ElabM (SProg C))
    (args : List RawExpr) (marks : List (Option AbiKind)) (sel : Option RawExpr) :
    ElabM (Option (SProg C × RawExpr)) := do
  let Γ ← ctx
  let tyOf (a : RawExpr) : Option AbiTy :=
    match synth C Γ.toNCtx a with
    | .ok (.mpath (.ref R) _) | .ok (.path (.ref R) _) => AbiTy.of (.ref R) (placeShape C Γ a) ""
    | _ => none
  unless args.any (fun a => (tyOf a).any (!·.flat)) do return none
  let mut P : SProg C := []
  let mut ms : List (AbiTy × RawExpr) := []
  for (a, mark) in args.zip marks do
    match mark with
    | some k => ms := ms ++ [(.val k, a)]
    | none =>
      if a.bytesLit?.isSome then
        let (Q, x) ← abiMemBytes a
        P := P ++ Q
        ms := ms ++ [(.bytes, .name x)]
      else match synth C (← nctx) a with
        | .ok (.mpath (.ref _) _) | .ok (.path (.ref _) _) =>
          let some t := tyOf a | throw s!"{a.toStr}: a mapping is not ABI-encoded"
          ms := ms ++ [(t, a)]
        | .ok _ => ms := ms ++ [(.val (← abiKind a), a)]
        | .error e => throw e
  let r := toString (← freshCapture "mv")
  let tot ← abiFresh
  let p ← abiFresh
  let base : Nat := if sel.isSome then 4 else 0
  let (sz, n) ← abiTupleSizeGen ms
  let selW : List RawStmt ← match sel with
    | none => pure []
    | some e => do
      let w ← abiFresh
      pure (.decl (.named "uint") w (some e) :: abiBytes r (.num 0) (.name w) 4)
  let S : List RawStmt := sz ++ [.decl (.named "uint") tot (some (n.addN base)),
    .declMemory (.named "bytes") r (some (.newArr (.named "bytes") (.name tot))),
    .decl (.named "uint") p (some (.num base))] ++ selW ++ (← abiTupleWriteGen r ms p)
  return some (P ++ (← elabStmtsP S), .name r)

/-- Check a byte interval before forming its end. The subtraction occurs
only after the offset check, so hostile words cannot overflow the check. -/
def abiBounds (d : ByteSrc) (o n : RawExpr) : List RawStmt :=
  [.require (.binop .le o d.len),
   .require (.binop .le n (.binop .sub d.len o))]

/-- The complete element head must fit before allocation or iteration.
Division avoids multiplying an untrusted length by its stride. -/
def abiSeqBounds (d : ByteSrc) (stride : Nat) (n q : RawExpr) : List RawStmt :=
  [.require (.binop .le q d.len)] ++
  if stride == 0 then [] else
    [.require (.binop .le n (.binop .div (.binop .sub d.len q) (.num stride)))]

/-- The word at `o` of `d` read at the kind `k`, checked within the data
first: the statements, and its value. -/
def abiWordAt (d : ByteSrc) (k : AbiKind) (o : RawExpr) : ElabM (List RawStmt × RawExpr) := do
  let w ← abiFresh
  let some (reads, v) := abiDecodeAt k.tyName d w o | throw "internal: a kind abi.decode reads"
  pure (abiBounds d o (.num 32) ++ reads, v)

mutual

/-- `abi.decode` of a value of `t` declared `T` whose encoding starts at `p`
in `d`: its statements, ending in `put` of it. -/
partial def abiReadGen (d : ByteSrc) (t : AbiTy) (T : RawTy) (p : RawExpr)
    (put : RawExpr → RawStmt) : ElabM (List RawStmt) := do
  match t with
  | .val k =>
    let (ss, v) ← abiWordAt d k p
    pure (ss ++ [put v])
  | .bytes =>
    let (s1, L) ← abiWordAt d (.uint 256) p
    let n ← abiFresh
    let x := toString (← freshCapture "mv")
    let j ← abiFresh
    let start : RawExpr := p.addN 32
    pure (s1 ++ [.decl (.named "uint") n (some L)] ++ abiBounds d start (.name n) ++ [
      .declMemory T x (some (.newArr T (.name n))),
      .decl (.named "uint") j (some (.num 0)),
      .whileLoop {} (.binop .lt (.name j) (.name n))
        [.assign (.index (.name x) (.name j)) (abiByte d (.binop .add start (.name j))),
         .assign (.name j) (.binop .add (.name j) (.num 1))],
      put (.name x)])
  | .arr e =>
    let (s1, L) ← abiWordAt d (.uint 256) p
    let n ← abiFresh
    let x := toString (← freshCapture "mv")
    pure (s1 ++ [.decl (.named "uint") n (some L)] ++
      abiSeqBounds d e.headSize (.name n) (p.addN 32) ++ [
      .declMemory T x (some (.newArr T (.name n)))] ++
      (← abiSeqReadGen d e T.elem (.name n) (p.addN 32) fun i v => .assign (.index (.name x) i) v) ++
      [put (.name x)])
  | .fixed e m =>
    let x := toString (← freshCapture "mv")
    pure (abiSeqBounds d e.headSize (.num m) p ++ [.declMemory T x none] ++
      (← abiSeqReadGen d e T.elem (.num m) p fun i v => .assign (.index (.name x) i) v) ++
      [put (.name x)])
  | .tuple s ms =>
    let x := toString (← freshCapture "mv")
    let mut ss : List RawStmt := abiBounds d p (.num ((ms.map (·.2.headSize)).sum)) ++
      [.declMemory T x none]
    let mut hp := 0
    for (f, mt) in ms do
      let hpos : RawExpr := p.addN hp
      let putF (v : RawExpr) : RawStmt := .assign (.field (.name x) f) v
      if mt.dynamic then
        let (s1, off) ← abiWordAt d (.uint 256) hpos
        let at0 ← abiFresh
        ss := ss ++ s1 ++ abiBounds d p off ++
          [.decl (.named "uint") at0 (some (.binop .add p off))] ++
          (← abiReadGen d mt (abiMemberTy s f) (.name at0) putF)
      else
        ss := ss ++ (← abiReadGen d mt (abiMemberTy s f) hpos putF)
      hp := hp + mt.headSize
    pure (ss ++ [put (.name x)])

/-- `L` elements from `q`, each in place if static, else at the offset its
head word holds from `q`; `put i v` stores the `i`-th. -/
partial def abiSeqReadGen (d : ByteSrc) (e : AbiTy) (T : RawTy) (L q : RawExpr)
    (put : RawExpr → RawExpr → RawStmt) : ElabM (List RawStmt) := do
  let i ← abiFresh
  let pos ← abiFresh
  let qn ← abiFresh
  let next := RawStmt.assign (.name i) (.binop .add (.name i) (.num 1))
  let posE : RawExpr := .binop .add (.name qn) (.binop .mul (.num e.headSize) (.name i))
  let body ← if !e.dynamic then abiReadGen d e T (.name pos) (put (.name i)) else do
    let (s1, off) ← abiWordAt d (.uint 256) (.name pos)
    let at0 ← abiFresh
    pure (s1 ++ abiBounds d (.name qn) off ++
      [.decl (.named "uint") at0 (some (.binop .add (.name qn) off))] ++
      (← abiReadGen d e T (.name at0) (put (.name i))))
  pure ([.decl (.named "uint") qn (some q)] ++ abiSeqBounds d e.headSize L (.name qn) ++
    [.decl (.named "uint") i (some (.num 0)), .whileLoop {} (.binop .lt (.name i) L)
      ([.decl (.named "uint") pos (some posE)] ++ body ++ [next])])

end

/-- The ABI type of `abi.decode`'s component written `Te`, and its declared
type, where it is not flat (`decodeKind?`'s). -/
def abiDecodeTy? (Te : RawExpr) : Option (AbiTy × RawTy) := do
  let T ← abiTyExpr? Te
  let (ty, ws) ← (elabTyW C T).toOption
  let t ← AbiTy.of ty ws ""
  if t.flat then none else some (t, T)

/-- The kind of `abi.decode`'s component written `T` that is not a value
type or a byte string: `T[]`, `T[k]` of a value type `T`, a struct of value
members. -/
def decodeKind? (T : RawExpr) : Option AbiKind :=
  match T with
  | .name t =>
    if t.endsWith "[]" then (valueKind? (t.dropRight 2)).map .arr
    else match C.structName? t with
      | some s => if (AbiKind.ofStruct s).isSome then some (.tuple s) else none
      | none => none
  | .index (.name t) (.num m) => (valueKind? t).map (.fixed · m)
  | _ => none

/-- The words a component written `T` takes in the head. -/
def decodeHeadWords (T : RawExpr) : Nat :=
  match decodeKind? C T, abiDecodeTy? C T with
  | some k, _ => k.headWords
  | none, some (t, _) => t.headSize / 32
  | none, none => 1

/-- `(T a, U b) = abi.decode(x, (T, U))`'s components, each at the word
its predecessors' head words leave (`decodeHeadWords`): the head's words, and
the `i`-th component's `#abiDecode`. -/
def abiDecodeHeads (x : String) (ts : List RawExpr) (d : RawExpr := .name x) :
    Nat × (Nat → RawExpr) :=
  let ws := ts.map (decodeHeadWords C)
  let n := ws.foldl (· + ·) 0
  (n, fun i => .call abiDecodeName [d, ts[i]!, .num ((ws.take i).foldl (· + ·) 0), .num n])

/-- A calldata slice's view (`#sliceV`): decoded in place, not bound. -/
def RawExpr.isSliceView : RawExpr → Bool
  | .call f _ => f == sliceViewName
  | _ => false

/-- **`abi.decode`** (`hoist`, outside its `mutual` block for its size, the
recursive calls handed in): `abi.decode(b, (T))` is `#abiDecode(b, T, 0,
n)`, and `#abiDecode(b, T, i, n)` the component at word `i` of a head of
`n` words.  A value type is its word read back, a word out of the type's
range reverting (`abiDecodeAt`); a `bytes`/`string` its offset, length and
bytes (`abiDecodeBytes`); a struct of values and a `T[k]` their words in
the head, a member or an element each; a `T[]` its offset in the head, its
length there and its elements' words after it, read by a loop into a fresh
`new T[](length)`, an offset or a length past the data reverting, as
solc's decoder does. -/
def abiDecodeWith (hoist : RawExpr → ElabM (SProg C × RawExpr))
    (abiMemBytes : RawExpr → ElabM (SProg C × String))
    (elabStmtsP : List RawStmt → ElabM (SProg C))
    (abiDecodeBytes : String → ByteSrc → Nat → Nat → ElabM (SProg C × String))
    (f : String) (args : List RawExpr) : ElabM (SProg C × RawExpr) := do
  if f == "abi.decode" then
    let [b, T] := args | throw "abi.decode(b, (T)) takes a byte string and a type"
    if T matches .tuple _ then
      throw "abi.decode: one type here; a tuple of them is a declaration's `(T a, U b) = abi.decode(…)`"
    return ← hoist (.call abiDecodeName [b, T, .num 0, .num (decodeHeadWords C T)])
  let [b, Te, .num i, .num n] := args | throw "internal: #abiDecode's arguments"
  -- a calldata slice's view (`RawStmt.sliceViews`): its base read in place
  let (P, Q, d) ← (match b with
    | .call f [.name base, o, L] =>
      if f == sliceViewName then
        pure ([], [], ByteSrc.mk base (match o with | .num 0 => none | o => some o) (some L))
      else do
        let (P, b) ← hoist b
        let (Q, d) ← abiMemBytes b
        pure (P, Q, (d : ByteSrc))
    | b => do
      let (P, b) ← hoist b
      let (Q, d) ← abiMemBytes b
      pure (P, Q, (d : ByteSrc)) : ElabM (SProg C × SProg C × ByteSrc))
  let len : RawExpr := d.len
  -- a view of a literal length too short: the revert itself, no read after it
  let enough : RawStmt := match len with
    | .num l => if l < 32 * n then .revert else .require (.binop .ge len (.num (32 * n)))
    | _ => .require (.binop .ge len (.num (32 * n)))
  if let .name T := Te then
    -- a byte string: its offset in the head, its length and bytes in the tail
    if dynBytesTy T then
      let (R, x) ← abiDecodeBytes T d (32 * i) n
      return (P ++ Q ++ R, .name x)
    if (valueKind? T).isSome then
      let w := toString (← freshCapture "se")
      let x := toString (← freshCapture "se")
      let some (reads, v) := abiDecodeAt T d w (.num (32 * i)) |
        throw s!"abi.decode at {T}: only value types are decoded"
      let R ← elabStmtsP ([enough] ++ reads ++ [.decl (.named T) x (some v)])
      return (P ++ Q ++ R, .name x)
  let some k := decodeKind? C Te | do
    -- a nested type: head and tail recursively (`abiReadGen`)
    let some (t, T) := abiDecodeTy? C Te |
      throw s!"abi.decode at {Te.toStr}: a value type, a byte string, an array or a struct"
    let x := toString (← freshCapture "mv")
    let p : RawExpr := .num (32 * i)
    let S ← if t.dynamic then do
        let (s1, off) ← abiWordAt d (.uint 256) p
        let at0 ← abiFresh
        pure (s1 ++ [.decl (.named "uint") at0 (some off)] ++
          (← abiReadGen d t T (.name at0) fun v => .declMemory T x (some v)))
      else abiReadGen d t T p fun v => .declMemory T x (some v)
    return (P ++ Q ++ (← elabStmtsP ([enough] ++ S)), .name x)
  let x := toString (← freshCapture "mv")
  -- the word at `o` read at the kind `kk` into a fresh local, then `put` of it
  let word (kk : AbiKind) (o : RawExpr) (put : RawExpr → RawStmt) : ElabM (List RawStmt) := do
    let w := toString (← freshCapture "se")
    let some (reads, v) := abiDecodeAt kk.tyName d w o | throw "internal: a member's kind"
    pure (reads ++ [put v])
  let S ← match k, Te with
    | .tuple s, .name t => do
      let ms := (AbiKind.ofStruct s).getD []
      let reads ← ms.zipIdx.mapM fun ((g, kk), j) =>
        word kk (.num (32 * (i + j))) (.assign (.field (.name x) g))
      pure ([enough, .declMemory (.named t) x none] ++ reads.flatten)
    | .fixed kk m, .index (.name t) _ => do
      let reads ← (List.range m).mapM fun j =>
        word kk (.num (32 * (i + j))) (.assign (.index (.name x) (.num j)))
      pure ([enough, .declMemory (.fixed (.named t) m) x none] ++ reads.flatten)
    | .arr kk, .name t => do
      let et := t.dropRight 2
      let o := toString (← freshCapture "se")
      let L := toString (← freshCapture "se")
      let j := toString (← freshCapture "se")
      let start : RawExpr := (RawExpr.name o).addN 32
      let body ← word kk (.binop .add start (.binop .mul (.name j) (.num 32)))
        (.assign (.index (.name x) (.name j)))
      pure ([enough] ++ abiAssemble d o (.num (32 * i)) 32 ++
        abiBounds d (.name o) (.num 32) ++ abiAssemble d L (.name o) 32 ++
        abiSeqBounds d 32 (.name L) start ++ [
         .declMemory (.array (.named et)) x (some (.newArr (.array (.named et)) (.name L))),
         .decl (.named "uint") j (some (.num 0)),
         .whileLoop {} (.binop .lt (.name j) (.name L))
           (body ++ [.assign (.name j) (.binop .add (.name j) (.num 1))])])
    | _, _ => throw s!"abi.decode at {Te.toStr}: not decoded"
  return (P ++ Q ++ (← elabStmtsP S), .name x)

/-- `abi.encodeWithSelector(s, …)`, `abi.encodeWithSignature(sig, …)`,
`abi.encodeCall(g, (…))`: the selector, as an expression, and the rest of
the arguments (`hoist`, outside its `mutual` block for its size). -/
def encodeSelector? (Γ : ECtx) (f : String) (args : List RawExpr) :
    Except String (Option (RawExpr × List RawExpr)) :=
  match f, args with
  | "abi.encodeWithSelector", s :: rest => pure (some (s, rest))
  | "abi.encodeWithSignature", s :: rest =>
    match s.bytesLit? with
    | some bs => pure (some (.num (Keccak.keccak256Nat bs / 2 ^ 224), rest))
    | none => pure (some (.binop .shr (.call "keccak256" [s]) (.num 224), rest))
  | "abi.encodeCall", [g, t] => do
    let rest := match t with
      | .tuple as => as
      | a => [a]
    match g with
    | e@(.field _ _) =>
      if let some (_, g) := extMember? C Γ e then
        if let some sel := fnSelector? C g then return some (.num sel, rest)
      throw "abi.encodeCall: an external function member is required"
    | .name g =>
      if let some ty := fnTyOf? C Γ g then
        if let some (_, _, true) := fnParts? ty then
          let a : RawExpr := .binop .div (.name g) (.num selShift)
          return some (.binop .sub (.name g) (.binop .mul a (.num selShift)), rest)
      if (lookupBy g Γ).isNone && (C.rootType g).isNone then
        if let some sel := fnSelector? C g then return some (.num sel, rest)
      throw s!"abi.encodeCall({g}, …): a function of the contract or an external \
        function value"
    | _ => throw "abi.encodeCall(f, …): f a function of the contract or a function value"
  | _, _ => pure none

/-- `keccak256(b)`, `sha256(b)`, `ripemd160(b)`: of a memory `bytes` (a
storage one copied first), into a fresh `bytes32` (`Val.hash`), a
`bytes20` for `ripemd160` (`ripemd160Bytes`, below `2^160`).
`ecrecover(h, v, r, s)`: of the precompile's input, the four arguments' ABI
words (`abi.encode`), an `address` (`ecrecoverBytes`). -/
def hoistHashWith (hoist : RawExpr → ElabM (SProg C × RawExpr))
    (abiMemBytes : RawExpr → ElabM (SProg C × String))
    (elabStmtsP : List RawStmt → ElabM (SProg C)) (f : String) (args : List RawExpr) :
    ElabM (SProg C × RawExpr) := do
  let k := (HashKind.ofName? f).getD .keccak
  if f == "ecrecover" then
    let [_, _, _, _] := args | throw "ecrecover takes four arguments"
    let (P, a) ← hoist (.call "abi.encode" args)
    let (Q, b) ← abiMemBytes a
    let y := toString (← freshCapture "se")
    let R ← elabStmtsP [.decl (.named "address") y
      (some (.field (.name b) (hashMember .ecrecover)))]
    return (P ++ Q ++ R, .name y)
  let [a] := args | throw s!"{f} takes one argument"
  let (P, a) ← hoist a
  let (Q, b) ← abiMemBytes a
  let y := toString (← freshCapture "se")
  let T := if f == "ripemd160" then "bytes20" else "bytes32"
  let R ← elabStmtsP [.decl (.named T) y (some (.field (.name b) (hashMember k)))]
  return (P ++ Q ++ R, .name y)

/-- ERC-7201 uses the existing operations, including wrapping subtraction
inside checked source code. A literal is folded by the same byte formula. -/
def hoistERC7201With (hoist : RawExpr → ElabM (SProg C × RawExpr))
    (args : List RawExpr) : ElabM (SProg C × RawExpr) := do
  let [a] := args | throw "erc7201 takes one string argument"
  if let some bs := a.bytesLit? then
    return ([], .num (ERC7201.root (bs.map UInt8.ofNat)).val)
  let first : RawExpr := .call "uint256" [.call "keccak256" [a]]
  let before : RawExpr := .binop .subW first (.num 1)
  let second : RawExpr := .call "uint256" [.call "keccak256" [.call "abi.encode" [before]]]
  hoist (.binop .band second (.num (2 ^ 256 - 256)))

/-- The kind of an argument of `abi.encode` (`AbiKind`), by its static type. -/
def abiKind (a : RawExpr) : ElabM AbiKind := do
  if a.bytesLit?.isSome then return .dyn
  let Γ ← ctx
  match synth C (← nctx) a with
  | .ok (.val .bool _) => pure .bool
  | .ok (.val .int _) => pure (.int (widthIn C Γ a))
  | .ok (.val .uint _) =>
    match bytesOf? C Γ a with
    | some n => pure (.bytesN n)
    | none =>
      -- an `address` at 20 bytes, an enum at one (`addressRows`, `enumRows`)
      match markOf? C Γ "#address" a, markOf? C Γ "#enum" a with
      | some n, _ | none, some n => pure (.uint (8 * n))
      | none, none => pure (.uint (widthIn C Γ a))
  | .ok (.mpath (.ref R) _) | .ok (.path (.ref R) _) =>
    let ws := placeShape C Γ a
    match R with
    | .array (.prim p) =>
      if ((fnRow? ws "[]").bind fnParts?).any (!·.2.2) then
        throw "ABI encoding an array of internal function values is not allowed"
      if p == .uint && lookupBy "[]#bytes" ws == some 1 then pure .dyn
      else pure (.arr (.ofValue p ws "[]"))
    | .fixed (.prim p) n =>
      if ((fnRow? ws "[]").bind fnParts?).any (!·.2.2) then
        throw "ABI encoding an array of internal function values is not allowed"
      pure (.fixed (.ofValue p ws "[]") n)
    | .struct s =>
      if (AbiKind.ofStruct s).isSome then pure (.tuple s)
      else throw s!"{a.toStr}: a struct with a member that is not a value is not ABI-encoded here"
    | _ => throw s!"{a.toStr}: an array of references or a mapping is not ABI-encoded here"
  | .ok _ => throw s!"{a.toStr}: a value of this type is not ABI-encoded here"
  | .error e => throw e

/-- The kinds of `abi.encode`'s arguments that their capture would lose,
read before it: a `bytesN` marked (`abiBytesMark`), an `address`, an enum
(`markOf?`). -/
def abiMarks (args : List RawExpr) : ElabM (List (Option AbiKind)) := do
  let Γ ← ctx
  let marked (a : RawExpr) : Option AbiKind :=
    if (markOf? C Γ "#address" a).isSome then some (.uint 160)
    else if (markOf? C Γ "#enum" a).isSome then some (.uint 8) else none
  pure (args.map fun a => match a with
    | .call g [_] =>
      match abiBytesMark? g with
      | some n => some (.bytesN n)
      | none => marked a
    | a => marked a)

/-- A typed self frame bypasses byte encoding. Integer widths share the same
word representation and may be rechecked at the requested width; fixed bytes
must retain exactly their byte width and alignment. In particular bytes2 is
not compact bytes4 or uint16, even though all erase to `PrimTy.uint`. -/
def selfReturnAbiCompatible (actual requested : String) : Bool :=
  match valueKind? actual, valueKind? requested with
  | some (.uint _), some (.uint _) => true
  | some (.int _), some (.int _) => true
  | some (.bytesN n), some (.bytesN m) => n == m
  | some .bool, some .bool => true
  | _, _ => actual == requested

/-- `try r.g(as) returns (T v) { x = v; } catch { revert(); }`: an external
call whose every failure reverts the caller, as a call outside a `try` does,
its one return landing in `res`; the types of `ps → rs`. -/
def extCallStmt (r : RawExpr) (g : String) (as : List RawExpr) (rs : List String)
    (res : Option (Var × PrimTy)) : ElabM RawStmt := do
  let mut rets : List (RawTy × String) := []
  for t in rs do rets := rets ++ [(.named t, toString (← freshCapture "se"))]
  let ok : List RawStmt := match res, rets with
    | some (x, _), [(_, v)] => [.assign (.name (toString x)) (.name v)]
    | _, _ => []
  pure (.tryCall r g as rets ok [.revert] none [.revert] [.revert])

end Elab

end Solidity
