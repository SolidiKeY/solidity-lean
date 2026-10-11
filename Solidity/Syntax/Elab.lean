import Solidity.Syntax.Resolve

/-!
# The elaborator

`sol[C]{ … }` reads Solidity statements (`Syntax.lean`'s grammar, `RawStmt`)
and this module types them against the contract `C`, into the scoped syntax
(`Syntax/Scoped.lean`): a local is the position `Idx Γ t` of the newest
local of its name in the context it is read in (`NCtx.find`), so its error
texts are `resolve`'s.  Synthesis returns a path or a value with its type;
checking takes the expected primitive type, which is how a literal gets one.
Every proof a constructor needs comes from a `match h : …` on the check that
justifies it.  A local shadows nothing: a declaration may not reuse the name
of a local in scope or of a state variable.

The passes on the raw syntax come first and are untouched by the typing:
solc's evaluation order (`hoist`, `captureExpr`: a value read before a later
operand's effect is held in a fresh local), the narrow and cast captures,
loops (`lowerLoops`), `return`s (`lowerReturns`), modifiers (`wrapMods`), a
callee's locals renamed fresh (`renameStmts`, `ElabScope.inlined`), named
arguments (`orderNamed`), `unchecked` (`uncheckStmts`) and a flat block's
locals renamed apart (`freshenBlocks`).  `hoist` returns the raw residual,
so a statement's captures are emitted first and its values typed after, in
the context the captures leave.

A statement is emitted as an `SStmt`, typed in the named context it was
elaborated in, and a block is the `SStmt`s chained into a `Prog`
(`SProg.chain`): each is placed where the one before leaves, weakened past
the locals that are in scope but no longer named (a flat block's `{ … }`,
which the elaborator closes but solkey's program keeps until its scope
ends, and a memory return's binder).  A branch, a loop's body, a `try`'s
clauses and a call's body are nested blocks, each from the context it is
entered in; a call's body from its frame, its return variables on its
parameters (`CallRet`, `Args`).

`elabStmt`, `elabStmts` keep their types, `Surface.Prog C` (the untyped
statement as written, decision 11 of `docs/intrinsic.md`): they erase the
scoped block (`Prog.erase`), for the readers not yet moved to the scoped
one.  The entry points are `Syntax/Splice.lean`'s.
-/

namespace Solidity

open Semantics

/-- What a local in scope holds. -/
inductive LocalTy where
  /-- A stack local of type `p`, `bits` wide (`uint8 x` is a `uint` 8 bits wide). -/
  | val (p : PrimTy) (bits : Nat := 256)
  | alias (R : RefTy)
  | mem (R : RefTy)
  /-- A storage variable, `old`: only a formula binds one (`old := storage`),
  and a program cannot read it. -/
  | store
  deriving DecidableEq, Repr

/-- The locals in scope, most recent first. -/
abbrev ECtx := List (Name × LocalTy)

/-- A type as read, against the contract: a primitive type (`PrimTy.ofName?`),
an enum of `C` (a `uint`, as a state variable of it is), a struct of
`structDef`.  Any other name is refused (`unknownStructMsg`: a struct
solc refuses, `refusedStructs`, or an unknown type). -/
def elabTy (C : Contract) : RawTy → Except String Ty
  | .named s =>
    match PrimTy.ofName? s with
    | some p => pure (.prim p)
    | none =>
      if (lookupBy s C.enums).isSome then pure .uint
      else if (narrowTy? s).isSome then throw (narrowNestedMsg s)
      else if (structDef s).isEmpty then throw (unknownStructMsg s)
      else pure (.struct s)
  | .mapping k v => do pure (.mapping (← elabTy C k) (← elabTy C v))
  | .array t => do pure (.array (← elabTy C t))
  | .fixed t n => do pure (.fixed (← elabTy C t) n)

/-- A declared variable's type: `elabTy`'s, or a narrow integer type
(`narrowTy?`) as its primitive type; and its width. -/
def elabDeclTy (C : Contract) : RawTy → Except String (Ty × Nat)
  | .named s =>
    match narrowTy? s with
    | some (p, n) => pure (.prim p, n)
    | none => do pure (← elabTy C (.named s), 256)
  | T => do pure (← elabTy C T, 256)

/-- `PrimTy.toStr`, under the name `Calculus/SurfaceSpec.lean` uses. -/
abbrev Surface.primName (p : PrimTy) : String := p.toStr

/-- A synthesised expression, read in `Γ`: a storage path, a memory path, or
a value. -/
inductive TExpr (C : Contract) (Γ : Ctx) where
  | path (T : Ty) (p : SPath C Γ T)
  | mpath (T : Ty) (p : MPath C Γ T)
  | val (p : PrimTy) (v : Val C Γ p)

/-- Its type. -/
def TExpr.ty {C : Contract} {Γ : Ctx} : TExpr C Γ → Ty
  | .path T _ | .mpath T _ => T
  | .val p _ => .prim p

/-- A path of primitive type is read as a value. -/
def TExpr.toVal? {C : Contract} {Γ : Ctx} : TExpr C Γ → Option ((p : PrimTy) × Val C Γ p)
  | .val p v => some ⟨p, v⟩
  | .path (.prim p) (.loc l) => some ⟨p, .read l⟩
  | .mpath (.prim p) (.loc l) => some ⟨p, .readMem l⟩
  | .path _ _ | .mpath _ _ => none

/-- A literal: a number, or a negated one (`-5`), which takes its type from
where it stands. -/
def RawExpr.isLit : RawExpr → Bool
  | .num _ | .unop .neg (.num _) => true
  | _ => false

/-! ### Traversals of the raw syntax

Every question about a raw expression is `RawExpr.any` of a question about
one node, and every rewrite `RawExpr.mapM` of a rewrite of one node; a
statement is its own expressions (`RawStmt.exprs`) and its blocks
(`RawStmt.blocks`). -/

/-- The Solidity spelling. -/
def RawTy.toStr : RawTy → String
  | .named s => s
  | .mapping k v => s!"mapping({k.toStr} => {v.toStr})"
  | .array t => t.toStr ++ "[]"
  | .fixed t n => s!"{t.toStr}[{n}]"

/-- The Solidity spelling, for messages: an operator application is
parenthesised unless it is the whole expression (`top`). -/
partial def RawExpr.toStr (e : RawExpr) (top : Bool := true) : String :=
  let paren (s : String) := if top then s else s!"({s})"
  match e with
  | .num n => toString n
  | .name x => x
  | .bool b => toString b
  | .field e f => s!"{e.toStr false}.{f}"
  | .index e k => s!"{e.toStr false}[{k.toStr}]"
  | .binop op a b => paren s!"{a.toStr false} {op.sym} {b.toStr false}"
  | .unop op a => s!"{op.sym}{a.toStr false}"
  | .ternary c a b => paren s!"{c.toStr false} ? {a.toStr false} : {b.toStr false}"
  | .incDec op e => IncDec.show op (e.toStr false)
  | .newArr T n => s!"new {T.toStr}({n.toStr})"
  | .call f as => s!"{f}({", ".intercalate (as.map (·.toStr))})"
  | .named f ns as =>
    s!"{f}(\{{", ".intercalate ((ns.zip as).map fun (n, a) => s!"{n}: {a.toStr}")}})"
  | .env k => k.toStr
  | .tuple es => s!"({", ".intercalate (es.map (·.toStr))})"

/-- Whether `p` holds of the expression or of an expression inside it. -/
def RawExpr.any (p : RawExpr → Bool) (e : RawExpr) : Bool :=
  p e || match e with
    | .field a _ | .unop _ a | .incDec _ a | .newArr _ a => a.any p
    | .index a b | .binop _ a b => a.any p || b.any p
    | .ternary c a b => c.any p || a.any p || b.any p
    | .call _ as | .named _ _ as | .tuple as => as.attach.any fun ⟨a, _⟩ => a.any p
    | .num _ | .name _ | .bool _ | .env _ => false

/-- The expression rewritten from the top down: `f` rewrites a node, then
the expressions inside what it returns are rewritten, left to right. -/
partial def RawExpr.mapM {m : Type → Type} [Monad m] [Inhabited (m RawExpr)]
    (f : RawExpr → m RawExpr) (e : RawExpr) : m RawExpr := do
  match ← f e with
  | .field a g => return .field (← a.mapM f) g
  | .index a b => return .index (← a.mapM f) (← b.mapM f)
  | .binop op a b => return .binop op (← a.mapM f) (← b.mapM f)
  | .unop op a => return .unop op (← a.mapM f)
  | .ternary c a b => return .ternary (← c.mapM f) (← a.mapM f) (← b.mapM f)
  | .incDec op a => return .incDec op (← a.mapM f)
  | .newArr T n => return .newArr T (← n.mapM f)
  | .call g as => return .call g (← as.mapM (·.mapM f))
  | .named g ns as => return .named g ns (← as.mapM (·.mapM f))
  | .tuple as => return .tuple (← as.mapM (·.mapM f))
  | e => pure e

/-- The names a raw expression reads, in order. -/
def RawExpr.names : RawExpr → List String
  | .name x => [x]
  | .field e _ | .unop _ e | .incDec _ e | .newArr _ e => e.names
  | .index a b | .binop _ a b => a.names ++ b.names
  | .ternary c a b => c.names ++ a.names ++ b.names
  | .call _ as => as.attach.flatMap fun ⟨a, _⟩ => a.names
  | .named _ _ as | .tuple as => as.attach.flatMap fun ⟨a, _⟩ => a.names
  | .num _ | .bool _ | .env _ => []

/-- Whether an index occurs in the expression: evaluating it may revert. -/
def RawExpr.hasIndex : RawExpr → Bool :=
  RawExpr.any (· matches .index ..)

/-- Whether a `.length` of an indexed base occurs in the expression
(`rows[i].length`): if the base is a fixed-size array, it is evaluated for its
bounds check although the length is a literal, so `hoist` captures it. -/
def RawExpr.hasIdxLen : RawExpr → Bool :=
  RawExpr.any fun | .field b "length" => b.hasIndex | _ => false

/-- Whether an effect occurs in the expression: an `++` or `−−`, or a call
(a cast `uint8(e)` is not one). -/
def RawExpr.hasIncDec : RawExpr → Bool :=
  RawExpr.any fun
    | .incDec .. | .named .. => true
    | .call f _ => (castTy? f).isNone
    | _ => false

/-- `f({q: b, p: a})`, a call of a function `funs` declares with named
arguments: put in its parameters' order, `f(a, b)`, as solkey's parser
does.  Any other `T({…})` is left to `hoist`, a struct's constructor. -/
def RawExpr.orderNamed (funs : List (Name × FunDecl)) : RawExpr → Except String RawExpr :=
  RawExpr.mapM fun
    | .named f ns as => match funs.find? (·.1 == f) with
      | some (_, d) => do
        let ps := d.params.map (·.1)
        unless ns.length == ps.length && ps.all ns.contains do
          throw s!"{f}(\{…}) names each parameter of {f} once: {ps}"
        if ns != ps && as.any (·.hasIncDec) then
          throw s!"{f}(\{…}): an argument with an effect, out of the parameters' order"
        pure (.call f (ps.map fun p => (lookupBy p (ns.zip as)).getD (.num 0)))
      | none => pure (.named f ns as)
    | e => pure e

/-- Whether a cast `uint8(e)` occurs in the expression: `hoist` captures it. -/
def RawExpr.hasCast : RawExpr → Bool :=
  RawExpr.any fun | .call f _ => (castTy? f).isSome | _ => false

/-- A literal's value: `5`, `-5`. -/
def RawExpr.litVal? : RawExpr → Option Int
  | .num n => some n
  | .unop .neg (.num n) => some (-(n : Int))
  | _ => none

/-- The range of `p` at `n` bits. -/
def intRange (p : PrimTy) (n : Nat) : Int × Int :=
  if p = .int then (-((2 ^ (n - 1) : Nat) : Int), ((2 ^ (n - 1) - 1 : Nat) : Int))
  else (0, ((2 ^ n - 1 : Nat) : Int))

/-- The range predicate `inTy(T, e)`, as a condition: `e` lies in `p`'s range at `n`
bits.  At `uint` only the upper bound is written: the operation's own
256-bit check has reverted below `0`. -/
def inTyCond (p : PrimTy) (n : Nat) (e : RawExpr) : RawExpr :=
  if p = .int then
    .binop .and (.binop .le (.unop .neg (.num (2 ^ (n - 1)))) e) (.binop .le e (.num (2 ^ (n - 1) - 1)))
  else .binop .le e (.num (2 ^ n - 1))

/-- Whether a call occurs in the expression. -/
def RawExpr.hasCall : RawExpr → Bool :=
  RawExpr.any (· matches .call ..)

/-- Whether the name `x` occurs in the expression. -/
def RawExpr.mentions (x : String) : RawExpr → Bool :=
  RawExpr.any fun | .name y => y == x | _ => false

/-- `e` with the names `ρ` maps renamed (a callee's locals, made fresh). -/
def RawExpr.rename (ρ : List (String × String)) (e : RawExpr) : RawExpr :=
  Id.run <| e.mapM fun
    | .name x => .name ((lookupBy x ρ).getD x)
    | e => e

/-- An expression inside `unchecked { … }`: `+ - * **` wrap (`+%` …).  An
`++`/`−−` inside it is an error: its capture (`hoist`) is checked. -/
def RawExpr.uncheck : RawExpr → Except String RawExpr :=
  RawExpr.mapM fun
    | .binop op a b =>
      let op' : BinOp := match op with
        | .add => .addW | .sub => .subW | .mul => .mulW | .pow => .powW | op => op
      pure (.binop op' a b)
    | .incDec .. => throw "`++` or `−−` inside an expression in `unchecked`"
    | e => pure e

/-- The largest index among the fresh variables an expression writes, as the
`FreshNames` in scope reads them (a file may spell `ie1` as `idx`). -/
def RawExpr.maxIdx [FreshNames] (e : RawExpr) : Nat :=
  e.names.foldl (fun n x => max n (Var.ofName x).idx) 0

def RawExpr.maxIdxs [FreshNames] (es : List RawExpr) : Nat :=
  es.foldl (fun n e => max n e.maxIdx) 0

/-- A statement's own expressions, in the order it is written (not those of
its blocks). -/
def RawStmt.exprs : RawStmt → List RawExpr
  | .assign l r | .assignPush l r | .opAssign _ l r | .assignIncDec l _ r => [l, r]
  | .decl _ _ i | .declStorage _ _ i | .declMemory _ _ i | .ret i => i.toList
  | .declStoragePush _ _ b | .delete b | .incDec _ b | .require b | .assert b | .ite b _ _ => [b]
  | .call f as => f :: as
  | .eval as => as
  | .tryCall r _ as .. => r :: as
  | .send none x r a => [x, r, a]
  | .send (some _) _ r a => [r, a]
  | .tupleDecl _ r => [r]
  | .tupleAssign ts r => ts.filterMap id ++ [r]
  | .revert | .unchecked _ | .block _ | .brk | .cont | .hole => []
  | .whileLoop a c _ | .doWhile a _ c | .loop a c _ => a.exprs ++ [c]
  | .forLoop a _ c _ _ => a.exprs ++ c.toList

/-- A statement's blocks: an `if`'s branches, an `unchecked` block's body, a
loop's body (a `for`'s initialisation, body and update). -/
def RawStmt.blocks : RawStmt → List (List RawStmt)
  | .ite _ t e => [t, e]
  | .unchecked b | .block b => [b]
  | .tryCall _ _ _ _ ok err _ pnc other => [ok, err, pnc, other]
  | .whileLoop _ _ b | .doWhile _ b _ | .loop _ _ b => [b]
  | .forLoop _ i _ u b => [i, b, u]
  | _ => []

/-- A loop's specification with its expressions rewritten by `f`. -/
def RawLoopSpec.mapM {m : Type → Type} [Monad m] (f : RawExpr → m RawExpr) (a : RawLoopSpec) :
    m RawLoopSpec :=
  return { a with inv := ← a.inv.mapM f, dec := ← a.dec.mapM f }

/-- A statement with its own expressions rewritten by `f`, left to right (its
blocks as they are). -/
def RawStmt.mapExprsM {m : Type → Type} [Monad m] (f : RawExpr → m RawExpr) :
    RawStmt → m RawStmt
  | .assign l r => return .assign (← f l) (← f r)
  | .assignPush l r => return .assignPush (← f l) (← f r)
  | .opAssign op l r => return .opAssign op (← f l) (← f r)
  | .assignIncDec l op r => return .assignIncDec (← f l) op (← f r)
  | .decl T x i => return .decl T x (← i.mapM f)
  | .declStorage T x i => return .declStorage T x (← i.mapM f)
  | .declMemory T x i => return .declMemory T x (← i.mapM f)
  | .ret i => return .ret (← i.mapM f)
  | .declStoragePush T x b => return .declStoragePush T x (← f b)
  | .delete b => return .delete (← f b)
  | .incDec op b => return .incDec op (← f b)
  | .require b => return .require (← f b)
  | .assert b => return .assert (← f b)
  | .ite c t e => return .ite (← f c) t e
  | .call g as => return .call (← f g) (← as.mapM f)
  | .eval as => return .eval (← as.mapM f)
  | .revert => pure .revert
  | .unchecked b => pure (.unchecked b)
  | .tryCall r g as rets ok err code pnc other =>
    return .tryCall (← f r) g (← as.mapM f) rets ok err code pnc other
  | .send T x r a => return .send T (← f x) (← f r) (← f a)
  | .tupleDecl vs r => return .tupleDecl vs (← f r)
  | .tupleAssign ts r => return .tupleAssign (← ts.mapM (·.mapM f)) (← f r)
  | .block b => pure (.block b)
  | .brk => pure .brk
  | .cont => pure .cont
  | .hole => pure .hole
  | .whileLoop a c b => return .whileLoop (← a.mapM f) (← f c) b
  | .doWhile a b c => return .doWhile (← a.mapM f) b (← f c)
  | .loop a c b => return .loop (← a.mapM f) (← f c) b
  | .forLoop a i c u b => return .forLoop (← a.mapM f) i (← c.mapM f) u b

/-- The name a statement declares in its own block. -/
def RawStmt.declared? : RawStmt → Option String
  | .decl _ x _ | .declStorage _ x _ | .declMemory _ x _ | .declStoragePush _ x _ => some x
  | .send (some _) (.name x) _ _ => some x
  | _ => none

/-- The names a statement binds in its blocks: a `try`'s return locals and
`Panic` code; and the variables a tuple declaration declares in its own. -/
def RawStmt.binds : RawStmt → List String
  | .tryCall _ _ _ rets _ _ code _ _ => rets.map (·.2) ++ code.toList
  | .tupleDecl vs _ => vs.filterMap (·.map (·.2))
  | _ => []

/-- Whether a `return` occurs in the statement. -/
partial def RawStmt.hasReturn (s : RawStmt) : Bool :=
  s matches .ret _ || s.blocks.any (·.any RawStmt.hasReturn)

/-- Whether the name `x` occurs in the statement, read, written or declared. -/
partial def RawStmt.mentions (x : String) (s : RawStmt) : Bool :=
  s.declared? == some x || s.binds.contains x || s.exprs.any (·.mentions x) ||
    s.blocks.any (·.any (·.mentions x))

mutual

/-- The names a raw statement reads (a function's name is not one). -/
partial def RawStmt.names (s : RawStmt) : List String :=
  let es := match s with
    | .call (.name _) as => as
    | s => s.exprs
  es.flatMap RawExpr.names ++ s.blocks.flatMap RawStmt.namesList

partial def RawStmt.namesList (ss : List RawStmt) : List String :=
  ss.flatMap RawStmt.names

end

mutual

/-- The names a raw statement declares, in either branch of an `if`. -/
partial def RawStmt.decls (s : RawStmt) : List String :=
  s.declared?.toList ++ s.binds ++ s.blocks.flatMap RawStmt.declsList

partial def RawStmt.declsList (ss : List RawStmt) : List String :=
  ss.flatMap RawStmt.decls

end

mutual

/-- The largest index among the fresh variables a raw statement writes. -/
partial def RawStmt.maxIdx [FreshNames] (s : RawStmt) : Nat :=
  max (((s.declared?.toList ++ s.binds).map fun x => (Var.ofName x).idx).foldl max 0)
    (max (RawExpr.maxIdxs s.exprs) ((s.blocks.map RawStmt.maxIdxs).foldl max 0))

partial def RawStmt.maxIdxs [FreshNames] (ss : List RawStmt) : Nat :=
  ss.foldl (fun n s => max n s.maxIdx) 0

end

/-! ### Block locals, renamed apart

The elaborator writes a raw block, a `for` loop's initialisation,
`unchecked { … }` and a modifier's `_;` flat into the untyped program, which
has no blocks, so `resolve` keeps their locals in scope until the scope that
holds them ends (a branch, a loop's body, a call's body, the program).  A
local of such a block whose name is declared again later in that scope is
renamed apart first, `x` to `x_1` (KeY's `VariableNamer` spelling, the least
index naming nothing in the program): Solidity's scope ends at the block, so
no reader after it sees the change, and the program `resolve` returns is
`Fresh` (`Prog.resolve_fresh`, `docs/intrinsic.md`, M2–M3 review). -/

/-- A statement with the blocks it holds rewritten by `f`, its own
expressions as they are. -/
def RawStmt.mapBlocks (f : List RawStmt → List RawStmt) : RawStmt → RawStmt
  | .ite c t e => .ite c (f t) (f e)
  | .unchecked b => .unchecked (f b)
  | .block b => .block (f b)
  | .tryCall r g as rets ok err code pnc other =>
    .tryCall r g as rets (f ok) (f err) code (f pnc) (f other)
  | .whileLoop a c b => .whileLoop a c (f b)
  | .doWhile a b c => .doWhile a (f b) c
  | .loop a c b => .loop a c (f b)
  | .forLoop a i c u b => .forLoop a (f i) c (f u) (f b)
  | s => s

/-- Every read of the name `x` renamed `y`, at any depth. -/
partial def RawStmt.renameName (x y : String) (s : RawStmt) : RawStmt :=
  (Id.run (s.mapExprsM (pure ∘ RawExpr.rename [(x, y)]))).mapBlocks
    (·.map (RawStmt.renameName x y))

/-- The names a statement declares in its own block. -/
def RawStmt.owns (s : RawStmt) : List String :=
  s.declared?.toList ++ (match s with | .tupleDecl .. => s.binds | _ => [])

/-- The statement declaring `y` where it declared `x`. -/
def RawStmt.renameDecl (x y : String) : RawStmt → RawStmt
  | .decl T z i => .decl T (if z == x then y else z) i
  | .declStorage T z i => .declStorage T (if z == x then y else z) i
  | .declMemory T z i => .declMemory T (if z == x then y else z) i
  | .declStoragePush T z b => .declStoragePush T (if z == x then y else z) b
  | .send (some T) (.name z) r a => .send (some T) (.name (if z == x then y else z)) r a
  | .tupleDecl vs r => .tupleDecl (vs.map (·.map fun (T, z) => (T, if z == x then y else z))) r
  | s => s

/-- Renaming apart threads the names taken. -/
abbrev FreshenM := StateT (List String) (Except String)

/-- `x_k`, for the least `k ≥ 1` naming nothing taken. -/
def FreshenM.pick (x : String) : FreshenM String := do
  let taken ← get
  let k := ((List.range (taken.length + 1)).find? fun k => !taken.contains s!"{x}_{k + 1}").getD
    taken.length
  let y := s!"{x}_{k + 1}"
  set (y :: taken)
  pure y

mutual

/-- The statements `ss` of one block, `live` the names in Solidity's scope
before them, `later` the names declared after the block in the scope
`resolve` reads it in.  A `flat` block's own local named in `later` is
renamed apart. -/
partial def freshenList (flat : Bool) (live later : List String) :
    List RawStmt → FreshenM (List RawStmt)
  | [] => pure []
  | s :: ss => do
    let mut s ← freshenStmt live (RawStmt.declsList ss ++ later) s
    let mut ss := ss
    let mut own : List String := []
    for x in s.owns do
      -- a local declared again in its own block is left to the elaborator,
      -- whose error names the statement it is in
      if flat && !live.contains x && later.contains x &&
          !(RawStmt.declsList ss).contains x then
        let y ← FreshenM.pick x
        s := s.renameDecl x y
        ss := ss.map (RawStmt.renameName x y)
        own := y :: own
      else own := x :: own
    pure (s :: (← freshenList flat (own ++ live) later ss))

/-- A statement's blocks renamed apart: a raw block, `unchecked` and a `for`
loop's initialisation are flat; a branch, a loop's body and a `try`'s
clauses are scopes of `resolve`'s, so nothing after them is `later`. -/
partial def freshenStmt (live later : List String) : RawStmt → FreshenM RawStmt
  | .block b => do pure (.block (← freshenList true live later b))
  | .unchecked b => do pure (.unchecked (← freshenList true live later b))
  | .forLoop a [] c u b => do
    pure (.forLoop a [] c (← freshenList false live [] u) (← freshenList false live [] b))
  | .forLoop a i c u b => do
    -- the initialisation's locals scope over the rest of the loop
    let out ← freshenList true live later (i ++ [.forLoop a [] c u b])
    match out.getLast? with
    | some (.forLoop a' [] c' u' b') => pure (.forLoop a' out.dropLast c' u' b')
    | _ => throw "a `for` loop's initialisation, renamed"
  | .ite c t e => do pure (.ite c (← freshenList false live [] t) (← freshenList false live [] e))
  | .whileLoop a c b => do pure (.whileLoop a c (← freshenList false live [] b))
  | .doWhile a b c => do pure (.doWhile a (← freshenList false live [] b) c)
  | .loop a c b => do pure (.loop a c (← freshenList false live [] b))
  | .tryCall r g as rets ok err code pnc other => do
    pure (.tryCall r g as rets (← freshenList false (rets.map (·.2) ++ live) [] ok)
      (← freshenList false live [] err) code (← freshenList false (code.toList ++ live) [] pnc)
      (← freshenList false live [] other))
  | s => pure s

end

/-- A block's flat locals renamed apart, from the names `live` in scope;
`avoid` are other names a new one must not take (the state variables). -/
def freshenBlocks (avoid live : List String) (ss : List RawStmt) : Except String (List RawStmt) :=
  (freshenList false live [] ss).run'
    (RawStmt.namesList ss ++ RawStmt.declsList ss ++ live ++ avoid)

/-- The elaborator's locals in scope as a named context: `old` is a
specification's storage snapshot.  A name is read as the file's
`FreshNames` spells it (`acc` may be `sp1`). -/
def ECtx.toNCtx [FreshNames] (Γ : ECtx) : NCtx :=
  Γ.map fun (x, t) => (Var.ofName x, match t with
    | .val p _ => .val p
    | .alias R => .alias R
    | .mem R => .mem R
    | .store => .old)

/-! ### Named contexts and blocks -/

/-- The type of the newest local named `x`. -/
def NCtx.lookupTy (x : Var) : NCtx → Option LTy
  | [] => none
  | (y, t) :: Γ => if y = x then some t else NCtx.lookupTy x Γ

/-- The position of the newest local named `x`, of type `t`
(`NCtx.find`, whose errors are `resolve`'s). -/
def NCtx.idx [FreshNames] (Γ : NCtx) (x : Var) (t : LTy) : Except String (Idx Γ.ctx t) :=
  (Γ.find x t).map (·.1)

/-- `Γ` thinned into the context `Δ` named `ns`: each local of `Γ` kept at
the newest local of `Δ` of its name and type that is older than the one
kept before it, every other one dropped. -/
def NCtx.thinInto : (Γ : NCtx) → (ns : List Var) → (Δ : Ctx) → Option (Thin Γ.ctx Δ)
  | [], _, [] => some .refl
  | [], ns, _ :: Δ => (NCtx.thinInto [] ns.tail Δ).map .drop
  | _ :: _, _, [] => none
  | _ :: _, [], _ :: _ => none
  | (x, t) :: Γ, y :: ns, u :: Δ =>
    if hx : x = y then
      if ht : t = u then
        (NCtx.thinInto Γ ns Δ).map fun th => by subst ht; exact .keep th
      else (NCtx.thinInto ((x, t) :: Γ) ns Δ).map .drop
    else (NCtx.thinInto ((x, t) :: Γ) ns Δ).map .drop

/-- `Γ` thinned into `Δ` (`thinInto`); a failure is the elaborator's own. -/
def NCtx.wkTo (Γ Δ : NCtx) : Except String (Thin Γ.ctx Δ.ctx) :=
  match NCtx.thinInto Γ Δ.names Δ.ctx with
  | some th => pure th
  | none => throw s!"internal: the locals {Γ.names} are not in scope in {Δ.names}"

variable {C : Contract}

/-- A statement, typed in the named context it was elaborated in. -/
structure SStmt (C : Contract) where
  Γ : NCtx
  Γ' : Ctx
  s : Stmt C Γ.ctx Γ'

/-- The statements of a block, each typed where it was elaborated. -/
abbrev SProg (C : Contract) := List (SStmt C)

/-- A statement at `Γ`. -/
abbrev SStmt.of (Γ : NCtx) {Γ' : Ctx} (s : Stmt C Γ.ctx Γ') : SStmt C := ⟨Γ, Γ', s⟩

/-- A block read in `Γ`, and the context it leaves. -/
abbrev Blk (C : Contract) (Γ : Ctx) := (Γ' : Ctx) × Prog C Γ Γ'

/-- `P` then `Q`. -/
def Prog.join {Γ Δ Ε : Ctx} : Prog C Γ Δ → Prog C Δ Ε → Prog C Γ Ε
  | .nil, Q => Q
  | .cons s P, Q => .cons s (Prog.join P Q)

/-- `a` then `b`, which must start where `a` leaves (an internal error
otherwise). -/
def Blk.append {Γ Δ : Ctx} (a : Blk C Γ) (b : Blk C Δ) : Except String (Blk C Γ) :=
  if h : Δ = a.1 then pure ⟨b.1, Prog.join a.2 (Prog.castIn h b.2)⟩
  else throw "internal: a block appended where it does not start"

variable [FreshNames]

/-- The statement placed in `Δ`, named `ns`: as it is when it was elaborated
there, else weakened past the locals in scope it does not name. -/
def SStmt.place (p : SStmt C) (ns : List Var) (Δ : Ctx) : Except String ((Δ' : Ctx) × Stmt C Δ Δ') :=
  if h : p.Γ.ctx = Δ ∧ p.Γ.names = ns then pure ⟨p.Γ', h.1 ▸ p.s⟩
  else match NCtx.thinInto p.Γ ns Δ with
    | some th => let ⟨Δ', _, s⟩ := p.s.wk th; pure ⟨Δ', s⟩
    | none => throw s!"internal: `{p.s.toStr p.Γ.names}` read in {p.Γ.names}, placed in {ns}"

/-- **A block**, from the context `Δ` named `ns`: each statement placed where
the one before leaves. -/
def SProg.chain (ns : List Var) (Δ : Ctx) : SProg C → Except String (Blk C Δ)
  | [] => pure ⟨Δ, .nil⟩
  | p :: ps => do
    let ⟨Δ₁, s⟩ ← p.place ns Δ
    let ⟨Δ₂, P⟩ ← SProg.chain (s.outNames ns) Δ₁ ps
    pure ⟨Δ₂, .cons s P⟩

/-! ### The locals a part reads, by name -/

def Simple.vars {Γ : Ctx} {p : PrimTy} (ns : List Var) : Simple C Γ p → List Var
  | .local i => [i.name ns]
  | .lit .. | .bool _ | .env .. => []

mutual

def SPath.vars {Γ : Ctx} (ns : List Var) : {T : Ty} → SPath C Γ T → List Var
  | _, .alias i => [i.name ns]
  | _, .loc l => l.vars ns

def Loc.vars {Γ : Ctx} (ns : List Var) : {T : Ty} → Loc C Γ T → List Var
  | _, .root .. => []
  | _, .field b _ _ => b.vars ns
  | _, .index _ b i => b.vars ns ++ i.vars ns

def MPath.vars {Γ : Ctx} (ns : List Var) : {T : Ty} → MPath C Γ T → List Var
  | _, .var i _ => [i.name ns]
  | _, .loc l => l.vars ns

def MLoc.vars {Γ : Ctx} (ns : List Var) : {T : Ty} → MLoc C Γ T → List Var
  | _, .field b _ _ => b.vars ns
  | _, .index _ b i => b.vars ns ++ i.vars ns

def Val.vars {Γ : Ctx} (ns : List Var) : {p : PrimTy} → Val C Γ p → List Var
  | _, .simple s => s.vars ns
  | _, .read l => l.vars ns
  | _, .binop _ _ _ a b => a.vars ns ++ b.vars ns
  | _, .unop _ _ _ a => a.vars ns
  | _, .ternary c a b => c.vars ns ++ a.vars ns ++ b.vars ns
  | _, .readMem l => l.vars ns
  | _, .len b _ => b.vars ns
  | _, .mlen b _ => b.vars ns

end

/-- The arguments of a call are separated (`Arg.separatedFrom`): no argument
that is not simple reads a parameter bound before it. -/
def Args.separated {Γ : Ctx} (ns : List Var) : {ps : Ctx} → Args C Γ ps → Bool
  | _, .nil => true
  | _, .snoc as _ _ e =>
    as.separated ns && (e.isSimple || (e.vars ns).all fun y => !as.names.contains y)

mutual
/-- A memory path that indexes nothing: a local and its members, which a
read cannot revert on (memory has no null and no mapping). -/
def MPath.indexFree {Γ : Ctx} : {T : Ty} → MPath C Γ T → Bool
  | _, .var .. => true
  | _, .loc l => l.indexFree
def MLoc.indexFree {Γ : Ctx} : {T : Ty} → MLoc C Γ T → Bool
  | _, .field b _ _ => b.indexFree
  | _, .index .. => false
end

section Elab

variable (C)

/-- A memory object of type `R` holds no mapping: solc has none in memory. -/
def memOk (R : RefTy) : Except String (PLift ((Ty.ref R).mapFree = true)) :=
  if h : (Ty.ref R).mapFree = true then pure ⟨h⟩
  else throw s!"a {Ty.ref R} in memory: it holds a mapping"

/-- The literal `n` at the numeric type `p`, if it is in `p`'s range: one
out of it is solc's compile error. -/
def litAt (Γ : NCtx) (p : PrimTy) (n : Int) : Except String (Simple C Γ.ctx p) :=
  match h : p.inRange n with
  | true => pure (.lit n h)
  | false =>
    if p.isNumeric then throw s!"the literal {n} is out of the range of {Surface.primName p}"
    else throw s!"a number where a {Surface.primName p} is expected"

/-- Arithmetic on two literals as solc folds it, exactly (a rational
constant): `+`, `-`, `*`, and `/` when it divides.  The rest is not folded. -/
def BinOp.foldLit? : BinOp → Int → Int → Option Int
  | .add, a, b | .addW, a, b => some (a + b)
  | .sub, a, b | .subW, a, b => some (a - b)
  | .mul, a, b | .mulW, a, b => some (a * b)
  | .div, a, b => if b != 0 && a % b == 0 then some (a / b) else none
  | _, _, _ => none

/-- `E.m` for an enum `E` of the contract that no local or state variable
shadows: the position of `m`. -/
def enumLit? (Γ : NCtx) : RawExpr → String → Option Nat
  | .name x, m =>
    if (Γ.lookupTy (Var.ofName x)).isNone && (C.rootType x).isNone then
      (lookupBy x C.enums).bind (·.findIdx? (· == m))
    else none
  | _, _ => none

mutual

def synth (Γ : NCtx) : RawExpr → Except String (TExpr C Γ.ctx)
  | .num n => return .val .uint (.simple (← litAt C Γ .uint n))
  | .bool b => pure (.val .bool (.simple (.bool b)))
  | .name x =>
    let v := Var.ofName x
    match Γ.lookupTy v with
    | some (.val p) => do pure (.val p (.simple (.local (← Γ.idx v (.val p)))))
    | some (.alias R) => do pure (.path (.ref R) (.alias (← Γ.idx v (.alias R))))
    | some (.mem R) =>
      match hm : (Ty.ref R).mapFree with
      | true => do pure (.mpath (.ref R) (.var (← Γ.idx v (.mem R)) hm))
      | false => throw s!"{x} is a memory local of a type that holds a mapping"
    | some .old | some .oldNet => throw s!"{x} is a storage variable, not a program value"
    | none =>
      match hr : C.rootType x with
      | some T => pure (.path T (.loc (.root x hr)))
      | none => throw s!"unknown name {x}"
  | .field e f => do
    if let some i := enumLit? C Γ e f then return .val .uint (.simple (← litAt C Γ .uint i))
    match ← synth Γ e with
    | .path (.ref (.array _)) b =>
      if f == "length" then pure (.val .uint (.len b rfl))
      else throw s!"member access .{f} on an array"
    | .mpath (.ref (.array _)) b =>
      if f == "length" then pure (.val .uint (.mlen b rfl))
      else throw s!"member access .{f} on an array"
    -- a fixed-size array's length is its type's: the literal, as solc folds
    -- it.  A base that indexes is evaluated first (it may revert), so
    -- `hoist` captured it; one left is where no capture may go.
    | .path (.ref (.fixed _ n)) _ | .mpath (.ref (.fixed _ n)) _ =>
      if f != "length" then throw s!"member access .{f} on an array"
      else if e.hasIndex then
        throw "the length of an indexed fixed-size array under a short-circuit operator or in a conditional's branch"
      else return .val .uint (.simple (← litAt C Γ .uint n))
    | .path (.ref (.struct s)) b =>
      match h : C.fieldType s f with
      | some T => pure (.path T (.loc (.field b f h)))
      | none => throw s!"struct {s} has no member {f}"
    | .mpath (.ref (.struct s)) b =>
      match h : C.fieldType s f with
      | some T => pure (.mpath T (.loc (.field b f h)))
      | none => throw s!"struct {s} has no member {f}"
    | _ => throw s!"member access .{f} on a non-struct"
  | .index e k => do
    match ← synth Γ e with
    | .path (.ref (.mapping (.prim kp) V)) b => pure (.path V (.loc (.index .map b (← check Γ kp k))))
    | .path (.ref (.array E)) b => pure (.path E (.loc (.index (.arr .dyn) b (← check Γ .uint k))))
    | .mpath (.ref (.array E)) b => pure (.mpath E (.loc (.index .dyn b (← check Γ .uint k))))
    -- a literal index past a fixed-size array's end is solc's compile error
    | .path (.ref (.fixed E n)) b =>
      if let .num i := k then if n ≤ i then throw s!"index {i} out of bounds of a length-{n} array"
      pure (.path E (.loc (.index (.arr .fixed) b (← check Γ .uint k))))
    | .mpath (.ref (.fixed E n)) b =>
      if let .num i := k then if n ≤ i then throw s!"index {i} out of bounds of a length-{n} array"
      pure (.mpath E (.loc (.index .fixed b (← check Γ .uint k))))
    | t => throw s!"{e.toStr} is indexed, but it is a {t.ty}, not a mapping or an array"
  | .binop op a b => do
    -- the operand type: the first operand that is not a literal gives it
    let t ← if a.isLit then synth Γ b else synth Γ a
    let some ⟨p, _⟩ := t.toVal? |
      throw s!"{(if a.isLit then b else a).toStr}: an operand of reference type {t.ty}"
    match h : op.accepts p with
    | true => pure (.val _ (.binop op h rfl (← check Γ p a) (← check Γ p b)))
    | false => throw s!"operator {BinOp.sym op} does not take {Surface.primName p}"
  | .ternary c a b => do
    let t ← if a.isLit then synth Γ b else synth Γ a
    let some ⟨p, _⟩ := t.toVal? | throw "a conditional of reference type"
    pure (.val p (.ternary (← check Γ .bool c) (← check Γ p a) (← check Γ p b)))
  | .unop op a => do
    let t ← synth Γ a
    let some ⟨p, v⟩ := t.toVal? | throw s!"{a.toStr}: an operand of reference type {t.ty}"
    match h : op.accepts p with
    | true => pure (.val _ (.unop op h rfl v))
    | false => throw s!"operator {UnOp.sym op} does not take {Surface.primName p}"
  | .incDec .. => throw "`++` or `−−` under a short-circuit operator or in a conditional's branch"
  | .newArr .. => throw "`new` stands only on the right of `=`"
  | .call f _ => throw s!"the call {f}(…) under a short-circuit operator or in a conditional's branch"
  | .named f .. => throw s!"the constructor {f}(\{…}) under a short-circuit operator or in a conditional's branch"
  | .env k => pure (.val .uint (.simple (.env k rfl)))
  | .tuple _ => throw "a tuple is the right-hand side of a tuple assignment or of a `return`"
termination_by e => (sizeOf e, 0)

/-- `e` checked at `p` through its synthesised type. -/
def checkVia (Γ : NCtx) (p : PrimTy) (e : RawExpr) : Except String (Val C Γ.ctx p) := do
  let some ⟨q, v⟩ := (← synth Γ e).toVal? |
    throw s!"a storage reference where a {Surface.primName p} is expected"
  if h : q = p then pure (h ▸ v) else throw s!"a {Surface.primName q} where a {Surface.primName p} is expected"
termination_by (sizeOf e, 1)

def check (Γ : NCtx) (p : PrimTy) : RawExpr → Except String (Val C Γ.ctx p)
  | .num n => return .simple (← litAt C Γ p n)
  -- a negative literal takes the type it is checked at: `int e = -5;`
  | .unop .neg (.num n) =>
    if p = .int then return .simple (← litAt C Γ p (-(n : Int)))
    else checkVia Γ p (.unop .neg (.num n))
  -- so does arithmetic on literals alone: `int e = -5 + 2;`; an operand out
  -- of `p`'s range is folded as solc folds a constant (`foldLit?`):
  -- `uint x = 2**256 - 1` written out is the literal `2**256 - 1`
  | .binop op a b =>
    if a.isLit && b.isLit && op.isArith then
      match h : op.accepts p with
      | true =>
        if hq : op.ret p = p then
          match (do pure (.binop op h hq (← check Γ p a) (← check Γ p b)) :
              Except String (Val C Γ.ctx p)) with
          | .ok v => pure v
          | .error e =>
            match a.litVal?, b.litVal? with
            | some x, some y =>
              match op.foldLit? x y with
              | some v => if p.inRange v then return .simple (← litAt C Γ p v) else throw e
              | none => throw e
            | _, _ => throw e
        else checkVia Γ p (.binop op a b)
      | false => checkVia Γ p (.binop op a b)
    else checkVia Γ p (.binop op a b)
  | e => checkVia Γ p e
termination_by e => (sizeOf e, 2)

end

/-- `e` as a storage path of type `T`. -/
def checkPath (Γ : NCtx) (T : Ty) (e : RawExpr) : Except String (SPath C Γ.ctx T) := do
  match ← synth C Γ e with
  | .path T' p =>
    if h : T' = T then pure (h ▸ p)
    else throw s!"{e.toStr}: a storage reference to a {T'} where a {T} is expected"
  | .mpath .. | .val .. => throw "a value where a storage reference is expected"

/-- `e` as a memory path of type `T`. -/
def checkMPath (Γ : NCtx) (T : Ty) (e : RawExpr) : Except String (MPath C Γ.ctx T) := do
  match ← synth C Γ e with
  | .mpath T' p =>
    if h : T' = T then pure (h ▸ p)
    else throw s!"{e.toStr}: a memory reference to a {T'} where a {T} is expected"
  | .path .. | .val .. => throw "a memory reference is expected"

/-- What a memory local is bound to: a memory path by identity, or a storage
path deep-copied. -/
def elabMRhs (Γ : NCtx) (R : RefTy) (e : RawExpr) : Except String (MRhs C Γ.ctx R) := do
  match ← synth C Γ e with
  | .mpath T p =>
    if h : T = .ref R then pure (.alias (h ▸ p))
    else throw s!"{e.toStr}: a memory reference to a {T} where a {Ty.ref R} is expected"
  | .path T p =>
    if h : T = .ref R then
      match hm : (Ty.ref R).mapFree with
      | true => pure (.copy (h ▸ p) hm)
      | false => throw "a copy into memory of a type that holds a mapping"
    else throw s!"{e.toStr}: a storage reference to a {T} where a {Ty.ref R} is expected"
  | .val .. => throw "a value where a memory reference is expected"

/-- The slot `b.push()` appends, as what an alias of `R` is bound to. -/
def elabPush (Γ : NCtx) (R : RefTy) (b : RawExpr) : Except String (ARhs C Γ.ctx R) := do
  match hd : (Ty.ref R).defaultOkS with
  | true => pure (.push (← checkPath C Γ (.array (.ref R)) b) hd)
  | false => throw "push() of an element whose default is not well-formed"

/-- `x` may be declared: it is neither a local in scope nor a state variable. -/
def checkFresh (Γ : ECtx) (x : Name) : Except String Unit :=
  if (lookupBy x Γ).isSome || (C.rootType x).isSome then
    throw s!"{x} is already declared, or names a state variable"
  else pure ()

/-- What elaboration reads: the functions a call may name — the contract's,
and in a function's body the ones declared before it — and whether the block
is a program's own statements (`top`), where `constructor(args);` may stand,
rather than an inlined body or a branch, loop or block of the program. -/
structure ElabScope where
  funs : List (Name × FunDecl)
  top : Bool := true
  /-- The fresh indices each enclosing inlined call gave its callee's locals
  (`elabCallRet`: its parameters, return variables, renamed locals, its
  modifiers' parameters, its loops' flags), `[k₀, k₁)` per call.  A fresh
  name in one is a local, which an effect may write, not a capture
  (`captureExpr`). -/
  inlined : List (Nat × Nat) := []

/-- Elaboration threads the locals in scope, newest first, and the index of
the next variable a capture declares, and reads its scope (`ElabScope`). -/
abbrev ElabM := ReaderT ElabScope (StateT (ECtx × Nat) (Except String))

/-- A checking step, in the elaborator. -/
def ElabM.lift {α : Type} (x : Except String α) : ElabM α := fun _ => StateT.lift x

/-- A fresh variable for a capture, `ie1`, `sp2`: numbered past every
variable the program itself writes. -/
def freshCapture (base : String) : ElabM Var := do
  let (Γ, k) ← get
  set (Γ, k + 1)
  pure (.fresh base k)

/-- The locals in scope. -/
def ctx : ElabM ECtx := do pure (← get).1

/-- The locals in scope, named: the context a statement elaborated now is
read in. -/
def nctx : ElabM NCtx := do pure (ECtx.toNCtx (← get).1)

/-- `synth`, in the locals in scope, with them. -/
def synthM (e : RawExpr) : ElabM ((Γ : NCtx) × TExpr C Γ.ctx) := do
  let Γ ← nctx
  pure ⟨Γ, ← ElabM.lift (synth C Γ e)⟩

/-- `check`, in the locals in scope `Γ`. -/
def checkIn (Γ : NCtx) (p : PrimTy) (e : RawExpr) : ElabM (Val C Γ.ctx p) :=
  ElabM.lift (check C Γ p e)

/-- Declare `x` in scope, the newest local. -/
def declare (x : Name) (t : LocalTy) : ElabM Unit := do
  let (Γ, k) ← get
  checkFresh C Γ x
  set ((x, t) :: Γ, k)

/-- A capture: a fresh `base` variable (`freshCapture`), declared at `t`. -/
def captureAs (base : String) (t : LocalTy) : ElabM Var := do
  let x ← freshCapture base
  declare C (toString x) t
  pure x

/-- What `Γ` is read as after a capture, and the capture's position. -/
def afterCapture (Γ : NCtx) (x : Var) (t : LTy) : ElabM ((Γ' : NCtx) × Thin Γ.ctx Γ'.ctx × Idx Γ'.ctx t) := do
  let Γ' ← nctx
  pure ⟨Γ', ← ElabM.lift (Γ.wkTo Γ'), ← ElabM.lift (Γ'.idx x t)⟩

/-- A compound assignment's target, with a non-simple index captured into a
fresh `ie` first: `values[i + 1] += 1;` is `uint ie1 = i + 1; values[ie1] += 1;`.
The target is read in the context the capture leaves. -/
def elabOpTarget (l : RawExpr) :
    ElabM (SProg C × (Γ : NCtx) × (p : PrimTy) × OpLoc C Γ.ctx p) := do
  let ⟨Γ, t⟩ ← synthM C l
  match t with
  | .val p (.simple (.local x)) => pure ([], ⟨Γ, p, .local x⟩)
  | .path (.prim p) (.loc (.root r h)) => pure ([], ⟨Γ, p, .root r h⟩)
  | .path (.prim p) (.loc (.field b f h)) => pure ([], ⟨Γ, p, .field b f h⟩)
  | .path (.prim p) (.loc (@Loc.index _ _ _ k _ it b i)) =>
    match i.toSimple? with
    | some ie => pure ([], ⟨Γ, p, .index it b ie⟩)
    | none =>
      let x ← captureAs C "ie" (.val k)
      let ⟨Γ', th, ix⟩ ← afterCapture Γ x (.val k)
      pure ([.of Γ (.declLocal k x (some i))], ⟨Γ', p, .index it (b.wk th) (.local ix)⟩)
  | .mpath (.prim p) (.loc (.field b f h)) => pure ([], ⟨Γ, p, .mfield b f h⟩)
  | .mpath (.prim p) (.loc (.index a b i)) =>
    match i.toSimple? with
    | some ie => pure ([], ⟨Γ, p, .mindex a b ie⟩)
    | none =>
      let x ← captureAs C "ie" (.val .uint)
      let ⟨Γ', th, ix⟩ ← afterCapture Γ x (.val .uint)
      pure ([.of Γ (.declLocal .uint x (some i))], ⟨Γ', p, .mindex a (b.wk th) (.local ix)⟩)
  | _ => throw "a compound assignment needs a local or a place of value type"

/-- An inc/dec target for the assignment form, with a non-simple receiver
captured into a fresh `sp` or `mv` first: `y = folks[i].age++;` is
`Person storage sp1 = folks[i]; y = sp1.age++;`. -/
def elabIncTarget (l : RawExpr) :
    ElabM (SProg C × (Γ : NCtx) × (p : PrimTy) × (t : OpLoc C Γ.ctx p) ×' t.recvSimple = true) := do
  let (pre, ⟨Γ, p, t⟩) ← elabOpTarget C l
  match hs : t.recvSimple with
  | true => pure (pre, ⟨Γ, p, t, hs⟩)
  | false =>
    match t with
    | @OpLoc.field _ _ s _ b f h =>
      let x ← captureAs C "sp" (.alias (.struct s))
      let ⟨Γ', _, ix⟩ ← afterCapture Γ x (.alias (.struct s))
      pure (pre ++ [.of Γ (.declStorage (.struct _) x (some (.path b)))],
        ⟨Γ', p, .field (.alias ix) f h, rfl⟩)
    | @OpLoc.index _ _ R _ _ it b i =>
      let x ← captureAs C "sp" (.alias R)
      let ⟨Γ', th, ix⟩ ← afterCapture Γ x (.alias R)
      pure (pre ++ [.of Γ (.declStorage _ x (some (.path b)))], ⟨Γ', p, .index it (.alias ix) (i.wk th), rfl⟩)
    | @OpLoc.mfield _ _ s _ b f h =>
      let x ← captureAs C "mv" (.mem (.struct s))
      let ⟨Γ', _, ix⟩ ← afterCapture Γ x (.mem (.struct s))
      pure (pre ++ [.of Γ (.declMem (.struct _) x (some (.alias b)) rfl b.mapFree)],
        ⟨Γ', p, .mfield (.var ix b.mapFree) f h, rfl⟩)
    | @OpLoc.mindex _ _ R _ a b i =>
      let x ← captureAs C "mv" (.mem R)
      let ⟨Γ', th, ix⟩ ← afterCapture Γ x (.mem R)
      pure (pre ++ [.of Γ (.declMem _ x (some (.alias b)) rfl b.mapFree)],
        ⟨Γ', p, .mindex a (.var ix b.mapFree) (i.wk th), rfl⟩)
    | .local _ | .root .. => nomatch hs

/-- `e` as a simple value of type `p`, captured into a fresh local first
when it is not one: read in the context the capture leaves. -/
def simpleOf (p : PrimTy) (e : RawExpr) : ElabM (SProg C × (Γ : NCtx) × Simple C Γ.ctx p) := do
  let Γ ← nctx
  let v ← checkIn C Γ p e
  match v.toSimple? with
  | some se => pure ([], ⟨Γ, se⟩)
  | none =>
    let x ← captureAs C "se" (.val p)
    let ⟨Γ', _, ix⟩ ← afterCapture Γ x (.val p)
    pure ([.of Γ (.declLocal p x (some v))], ⟨Γ', .local ix⟩)

/-- The size of `new T[](n)` as a simple value: a size that is not one is
captured into a fresh `uint` first (KeY's `memoryArrayFreshAlloc` takes a
`SimpleExpression`). -/
def elabSize (n : RawExpr) : ElabM (SProg C × (Γ : NCtx) × Simple C Γ.ctx .uint) :=
  simpleOf C .uint n

/-- The array type `new T(n)` allocates, if it may be allocated. -/
def elabNewTy (T : RawTy) : ElabM ((R : RefTy) ×' R.newArrOk = true) := do
  let .ref R ← ElabM.lift (elabTy C T) | throw "`new` of a value type"
  match h : R.newArrOk with
  | true => pure ⟨R, h⟩
  | false => throw "`new` of an array whose elements a memory array cannot hold"

/-! ### Narrow widths -/

/-- Two operands' type: a literal takes the other's, and the wider wins (solc
converts a `uint8` to a `uint16` implicitly). -/
def joinIT : Option (PrimTy × Nat) → Option (PrimTy × Nat) → Option (PrimTy × Nat)
  | none, t => t
  | t, none => t
  | some (p, n), some (_, m) => some (p, max n m)

/-- The integer type solc gives `e`: `some (p, n)` for `n` bits (a value not
built from a narrow variable or a cast is 256 bits wide), `none` for a literal,
which takes the type of what it meets.  `a ** b`, `a << b` and `a >> b` have
`a`'s type (a literal base is 256 bits wide, solc ≥ 0.7). -/
def intTyOf (Γ : ECtx) : RawExpr → Option (PrimTy × Nat)
  | .num _ => none
  | .name x =>
    match lookupBy x Γ with
    | some (.val p n) => some (p, n)
    | some _ => some (.uint, 256)
    | none =>
      match C.rootType x with
      | some (.prim p) => some (p, (lookupBy x C.widths).getD 256)
      | _ => some (.uint, 256)
  | .unop .not _ => some (.bool, 256)
  | .unop _ a => intTyOf Γ a
  | .binop op a b =>
    if !op.isArith then some (.bool, 256)
    else if op matches .pow | .powW | .shl | .shr then
      match a.litVal? with
      | some v => some (if v < 0 then .int else .uint, 256)
      | none => intTyOf Γ a
    else joinIT (intTyOf Γ a) (intTyOf Γ b)
  | .ternary _ a b => joinIT (intTyOf Γ a) (intTyOf Γ b)
  | .incDec _ e => intTyOf Γ e
  | .call f _ => some ((castTy? f).getD (.uint, 256))
  | .bool _ => some (.bool, 256)
  | _ => some (.uint, 256)

/-- `e`'s width in bits: `intTyOf`'s, `256` for a literal. -/
def widthIn (Γ : ECtx) (e : RawExpr) : Nat := ((intTyOf C Γ e).map (·.2)).getD 256

/-- `e`, an operation that can leave its narrow type — `+ - * **`, and `/` and
unary `-` at `int` (`-128 / -1` at `int8`) — with that type. -/
def checkedNarrow? (Γ : ECtx) (e : RawExpr) : Option (PrimTy × Nat) :=
  match e, intTyOf C Γ e with
  | .binop op _ _, some (p, n) =>
    if n < 256 && ((op matches .add | .sub | .mul | .pow) || (op == .div && p == .int))
    then some (p, n) else none
  | .unop .neg _, some (.int, n) => if n < 256 then some (.int, n) else none
  | _, _ => none

/-- Whether a narrow operation (`checkedNarrow?`) occurs in `e`. -/
def hasNarrow (Γ : ECtx) (e : RawExpr) : Bool :=
  e.any fun n => (checkedNarrow? C Γ n).isSome

/-- `r` may be written where a `p` of `n` bits is expected: a literal fits it,
and a value is not wider (solc converts only to a wider type implicitly). -/
def fitCheck (Γ : ECtx) (p : PrimTy) (n : Nat) (r : RawExpr) : Except String Unit := do
  if 256 ≤ n then return
  match r.litVal?, intTyOf C Γ r with
  | some v, _ =>
    let (lo, hi) := intRange p n
    unless lo ≤ v && v ≤ hi do throw s!"{v} does not fit {tyName p n}"
  | none, some (q, m) =>
    if q != .bool && n < m then
      throw s!"a {tyName q m} where a {tyName p n} is expected: write {tyName p n}(…)"
  | none, none => pure ()

/-- One node at a narrow `uintN`, read as solc reads it: the wrapping
`+% -% *% **%` of `unchecked` and `<<` are taken modulo `2^N` (solc truncates
them to the type), `~a` is `(2^N - 1) -% a`; and a literal operand must fit the
type. -/
def narrowWrapNode (Γ : ECtx) (e : RawExpr) : Except String RawExpr := do
  let some (p, n) := intTyOf C Γ e | return e
  if 256 ≤ n then return e
  match e with
  | .binop op a b =>
    -- `%` too: the modulus this rewrite writes may meet it again
    unless op matches .pow | .powW | .shl | .shr | .mod do
      for l in [a, b] do
        if let some v := l.litVal? then
          let (lo, hi) := intRange p n
          unless lo ≤ v && v ≤ hi do throw s!"{v} does not fit {tyName p n}"
    if op matches .addW | .subW | .mulW | .powW | .shl then
      return .binop .mod e (.num (2 ^ n))
    return e
  | .unop .bnot a => return .binop .subW (.num (2 ^ n - 1)) a
  | _ => return e

/-- `narrowWrapNode` at every node of `e`, bottom up. -/
partial def narrowPure (Γ : ECtx) : RawExpr → Except String RawExpr
  | .binop op a b => do narrowWrapNode C Γ (.binop op (← narrowPure Γ a) (← narrowPure Γ b))
  | .unop op a => do narrowWrapNode C Γ (.unop op (← narrowPure Γ a))
  | .field e f => do pure (.field (← narrowPure Γ e) f)
  | .index e k => do pure (.index (← narrowPure Γ e) (← narrowPure Γ k))
  | .ternary c a b => do pure (.ternary (← narrowPure Γ c) (← narrowPure Γ a) (← narrowPure Γ b))
  | .incDec op e => do pure (.incDec op (← narrowPure Γ e))
  | .newArr T e => do pure (.newArr T (← narrowPure Γ e))
  | .call f as => do pure (.call f (← as.mapM (narrowPure Γ)))
  | .named f ns as => do pure (.named f ns (← as.mapM (narrowPure Γ)))
  | e => pure e

/-- `require(inTy)` of `e` at `p`'s `n` bits, when `n` is narrow. -/
def narrowCheck (p : PrimTy) (n : Nat) (e : RawExpr) : ElabM (SProg C) := do
  if 256 ≤ n then return []
  let Γ ← nctx
  pure [.of Γ (.require (← checkIn C Γ .bool (inTyCond p n e)))]

/-- What follows a write of `r` to the variable `l`: the check of `r`'s narrow
operation, on `l` (`c = a + b;` at `uint8` is `c = a + b; require(c <= 255);`:
a revert discards the write, so checking after it is checking before it); and,
when `l` is narrow, `r` fitting it (`fitCheck`) and arithmetic on literals
alone checked at `l`'s type (solc folds it at compile time). -/
def narrowPost (l r : RawExpr) : ElabM (SProg C) := do
  let Γ ← ctx
  let tl := intTyOf C Γ l
  if let some (p, n) := tl then ElabM.lift (fitCheck C Γ p n r)
  match checkedNarrow? C Γ r, tl, intTyOf C Γ r, r.litVal? with
  | some (p, n), _, _, _ => narrowCheck C p n l
  | none, some (p, n), none, none => narrowCheck C p n l
  | _, _, _, _ => pure []

/-- A narrow operation inside an expression, its operands' captures made:
held in a fresh local and checked there, before the statement
(`x = a + b > c;` at `uint8` is `uint se1 = a + b; require(se1 <= 255);
x = se1 > c;`). -/
def narrowCapture (e : RawExpr) : ElabM (SProg C × RawExpr) := do
  let some (p, n) := checkedNarrow? C (← ctx) e | return ([], e)
  let Γ ← nctx
  let v ← checkIn C Γ p e
  let x ← captureAs C "se" (.val p n)
  let e' : RawExpr := .name (toString x)
  pure (.of Γ (.declLocal p x (some v)) :: (← narrowCheck C p n e'), e')

/-- A cast `T(e)`, `e`'s captures made: a fresh local of type `T` holding `e`.
Narrowing a `uint` keeps the low bits (`e % 2^N`, as solc truncates); a cast
between `uint` and `int`, and one narrowing an `int`, are refused. -/
def castCapture (f : String) (e : RawExpr) : ElabM (SProg C × RawExpr) := do
  let some (p, n) := castTy? f | throw s!"{f} is not a type"
  let Γ ← ctx
  let r ← match intTyOf C Γ e, e.litVal? with
    | _, some _ => do ElabM.lift (fitCheck C Γ p n e); pure e
    | some (q, m), none =>
      if q != p then throw s!"{f}({e.toStr}): a cast between uint and int is not modelled"
      else if m ≤ n then pure e
      else if p == .int then throw s!"{f}({e.toStr}): a cast narrowing an int is not modelled"
      else pure (.binop .mod e (.num (2 ^ n)))
    | none, none =>
      if 256 ≤ n then pure e
      else if p == .int then throw s!"{f}({e.toStr}): a cast narrowing an int is not modelled"
      else pure (.binop .mod e (.num (2 ^ n)))
  let Γn ← nctx
  let v ← checkIn C Γn p r
  let x ← captureAs C "se" (.val p n)
  pure ([.of Γn (.declLocal p x (some v))], .name (toString x))

/-- `e`'s value, or the reference it names, held in a fresh local before a
later operand's effect: `x = i++ + i;` reads the right `i` first (solc
evaluates a binary operator's right operand first), so it is
`uint se1 = i; uint se2; se2 = i++; x = se2 + se1;`.  A literal needs no
capture, nor does a name bound to a reference (an effect cannot rebind it).
Nor does a capture already made, which holds its value: a fresh name the
elaborator declared as one, or a line's written-out capture.  A fresh name
the inliner gave a callee's local (`ElabScope.inlined`) is a local like any
other, and is captured: in `function f(uint a) … { return a++ + a; }` the
right `a` is read before the `++`. -/
def captureExpr (e : RawExpr) : ElabM (SProg C × RawExpr) := do
  if e.isLit || e matches .bool _ then return ([], e)
  if let .name x := e then
    if let .fresh _ i := Var.ofName x then
      unless (← read).inlined.any fun (k₀, k₁) => k₀ ≤ i && i < k₁ do return ([], e)
  let ⟨Γ, t⟩ ← synthM C e
  match e, t with
  | .name _, .path (.ref _) _ | .name _, .mpath (.ref _) _ => return ([], e)
  | _, .path (.ref R) sp =>
    let x ← captureAs C "sp" (.alias R)
    return ([.of Γ (.declStorage R x (some (.path sp)))], .name (toString x))
  | _, .mpath (.ref R) mp =>
    let x ← captureAs C "mv" (.mem R)
    return ([.of Γ (.declMem R x (some (.alias mp)) rfl mp.mapFree)], .name (toString x))
  | _, t =>
    let some ⟨p, v⟩ := t.toVal? | throw s!"{e.toStr}: a value or a reference is expected"
    let x ← captureAs C "se" (.val p (widthIn C (← ctx) e))
    return ([.of Γ (.declLocal p x (some v))], .name (toString x))

/-! ### Inlining a call -/

/-- A callee's body with its locals renamed fresh, each declaration's name
numbered as a capture of its kind is (`se`, `sp`, `mv`), and the names `ρ`
maps (its parameters and return variable) renamed: inlined, it binds no
name the caller uses. -/
partial def renameStmts (ρ : List (String × String)) : List RawStmt → ElabM (List RawStmt)
  | [] => pure []
  | s :: ss => do
    let r := RawExpr.rename ρ
    let ra (a : RawLoopSpec) : RawLoopSpec := Id.run (a.mapM (pure ∘ r))
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
    | .send (some T) (.name x) e a =>
      let (y, ρ') ← fresh "se" x
      pure (.send (some T) (.name y) (r e) (r a) :: (← renameStmts ρ' ss))
    | .ite c t e =>
      pure (.ite (r c) (← renameStmts ρ t) (← renameStmts ρ e) :: (← renameStmts ρ ss))
    | .unchecked b => pure (.unchecked (← renameStmts ρ b) :: (← renameStmts ρ ss))
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
partial def RawStmt.hasJump (s : RawStmt) : Bool :=
  s.isJump || s.blocks.any (·.any RawStmt.hasJump)

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
  let spec := if spec.inv.isEmpty then spec else
    { spec with inv := spec.inv ++ heads.map fun f => .binop .or (.name f) (.unop .not (.name f)) }
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
partial def RawStmt.hasHole (s : RawStmt) : Bool :=
  s matches .hole || s.blocks.any (·.any RawStmt.hasHole)

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
renamed fresh, so the body cannot see them.  A `return` in a modifier is
not read; one in the body is its last statement (`lowerReturns`), so the
code after `_;` runs after it, as it does in solc.  A body run by several
`_;` (or by one in a loop) is run again in the same locals, its parameters
and return variables not reset: solc's legacy pipeline (via-IR resets
them). -/
partial def wrapMods (body : List RawStmt) : List ModApp → ElabM (List RawStmt)
  | [] => pure body
  | m :: ms => do
    let inner ← wrapMods body ms
    unless m.params.length == m.args.length do
      throw s!"modifier {m.name} takes {m.params.length} arguments, not {m.args.length}"
    if m.body.any RawStmt.hasReturn then throw s!"modifier {m.name}: `return` in a modifier"
    let mut ρ : List (String × String) := []
    let mut decls : List RawStmt := []
    for ((n, T), a) in m.params.zip m.args do
      let .prim p := T | throw s!"modifier {m.name}: the parameter {n} has a reference type"
      let y := toString (← freshCapture "se")
      decls := decls ++ [.decl (.named (Surface.primName p)) y (some a)]
      ρ := (n, y) :: ρ
    let code ← renameStmts ρ m.body
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
      | .ite c t e => do pure (.ite (← c.uncheck) (← uncheckStmts t) (← uncheckStmts e))
      | .unchecked b => do pure (.unchecked (← uncheckStmts b))
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
the memory return `r`. -/
inductive RetKind where
  | none
  | val (p : PrimTy) (r : Var)
  | rets (rs : List (PrimTy × Var))
  | mem (R : RefTy) (r : Var)

mutual

/-- **Captures before a statement**: an `++`/`−−` inside an expression, and a
conditional of references, are evaluated before the statement that holds
them, in solc's order (an assignment's right-hand side before its target, a
binary operator's right operand before its left, an index's base before the
index: an operand read before an effect is captured with `captureExpr`),
into fresh locals (KeY's captures): `values[i++] = 1;`
is `uint se1; se1 = i++; values[se1] = 1;`, and
`Person storage p = c ? alice : bob;` is
`Person storage sp1; if (c) { sp1 = alice; } else { sp1 = bob; }
Person storage p = sp1;`, the alias declared before the branches, which are
scopes (`Syntax/Resolve.lean`).  A memory one is `Person memory mv1 = mx;
if (c) { mv1 = mx; } else { mv1 = my; }`: declared bound to a branch that
indexes nothing (`MPath.indexFree`, a read that cannot revert), or, when
both index, to a fresh default object (`Person memory mv1;`, an object
nothing reaches), and rebound in each branch.  Under the right
operand of `&&`/`||` or in a branch of a conditional an effect would be
evaluated where the program does not evaluate it, so there it is an error. -/
partial def hoist : RawExpr → ElabM (SProg C × RawExpr)
  | .field e f => do
    let (P, e) ← hoist e
    -- `rows[i].length` of a fixed-size `rows[i]`: the base is evaluated (and
    -- may revert) although the length is the literal, so it is captured
    if f == "length" && e.hasIndex then
      match synth C (← nctx) e with
      | .ok (.path (.ref (.fixed ..)) _) | .ok (.mpath (.ref (.fixed ..)) _) =>
        let (Pc, e) ← captureExpr C e
        return (P ++ Pc, .field e f)
      | _ => pure ()
    pure (P, .field e f)
  | .index e k => do
    -- the base first, then the index: `matrix[k][k++]` indexes `matrix[0]`
    let (P, e) ← hoist e
    if k.hasIncDec then
      let (Pc, e) ← captureExpr C e
      let (Q, k) ← hoist k
      pure (P ++ Pc ++ Q, .index e k)
    else if k.hasIdxLen || k.hasCast || hasNarrow C (← ctx) k then
      let (Q, k) ← hoist k
      pure (P ++ Q, .index e k)
    else pure (P, .index e k)
  | .binop op a b => do
    if op.shortCircuits then
      let (P, a) ← hoist a
      if b.hasCall then throw "a call under a short-circuit operator"
      if b.hasIncDec then throw "`++` or `−−` under a short-circuit operator"
      if hasNarrow C (← ctx) b then
        throw "narrow arithmetic under a short-circuit operator: its check would run where the program does not evaluate it"
      pure (P, .binop op a b)
    else
      let (P, e) ← hoistBinop op a b
      let (Q, e) ← narrowCapture C e
      pure (P ++ Q, e)
  | .unop op a => do
    let (P, a) ← hoist a
    let (Q, e) ← narrowCapture C (.unop op a)
    pure (P ++ Q, e)
  | .ternary c a b => do
    let (P, c) ← hoist c
    if a.hasCall || b.hasCall then throw "a call in a conditional's branch"
    if a.hasIncDec || b.hasIncDec then throw "`++` or `−−` in a conditional's branch"
    if hasNarrow C (← ctx) a || hasNarrow C (← ctx) b then
      throw "narrow arithmetic in a conditional's branch: its check would run where the program does not evaluate it"
    let Γ ← nctx
    match synth C Γ a, synth C Γ b with
    | .ok (.path (.ref R) pa), .ok (.path (.ref R') pb) =>
      if hR : R' = R then
        let c ← checkIn C Γ .bool c
        let x ← captureAs C "sp" (.alias R)
        let ⟨Γ', th, ix⟩ ← afterCapture Γ x (.alias R)
        pure (P ++ [.of Γ (.declStorage R x none),
          .of Γ' (.ite (c.wk th) (.cons (.rebind ix (.path (pa.wk th))) .nil)
            (.cons (.rebind ix (.path ((hR ▸ pb).wk th))) .nil))], .name (toString x))
      else throw "a conditional of two reference types"
    | .ok (.mpath (.ref R) pa), .ok (.mpath (.ref R') pb) =>
      if hR : R' = R then
        let pb := hR ▸ pb
        let c ← checkIn C Γ .bool c
        let x ← captureAs C "mv" (.mem R)
        -- declared before the branches, bound to a branch whose read cannot
        -- revert (or, both indexing, to a fresh default object), then rebound
        -- in each branch to the one the condition takes
        let decl : Stmt C Γ.ctx (.mem R :: Γ.ctx) ←
          match (if pa.indexFree then some pa else if pb.indexFree then some pb else none) with
          | some p => pure (Stmt.declMem R x (some (.alias p)) rfl pa.mapFree)
          | none => match hd : (Ty.ref R).defaultOkS with
            | true => pure (Stmt.declMem R x none (by simp only [Option.isSome_none, hd, Bool.or_true]) pa.mapFree)
            | false => throw s!"a conditional of two indexed memory {Ty.ref R}s, whose default is not well-formed"
        let ⟨Γ', th, ix⟩ ← afterCapture Γ x (.mem R)
        pure (P ++ [.of Γ decl, .of Γ' (.ite (c.wk th) (.cons (.rebindMem ix (.alias (pa.wk th))) .nil)
            (.cons (.rebindMem ix (.alias (pb.wk th))) .nil))],
          .name (toString x))
      else throw "a conditional of two reference types"
    | .ok (.path (.ref _) _), .ok (.mpath ..) | .ok (.mpath ..), .ok (.path (.ref _) _) =>
      throw "a conditional of a storage and a memory reference"
    | _, _ => pure (P, .ternary c a b)
  | .incDec op e => do
    let (P, e) ← hoist e
    let (pre, ⟨Γ, p, t, hs⟩) ← elabIncTarget C e
    match hp : p.isNumeric with
    | true =>
      let n := widthIn C (← ctx) e
      let x ← captureAs C "se" (.val p n)
      let ⟨Γ', th, ix⟩ ← afterCapture Γ x (.val p)
      pure (P ++ pre ++ [.of Γ (.declLocal p x none),
          .of Γ' (.assignIncDec ix op hp (t.wk th) ((OpLoc.recvSimple_wk th t).trans hs))] ++
          (← narrowCheck C p n e),
        .name (toString x))
    | false => throw s!"++ or −− at {Surface.primName p}"
  | .named f ns args => do
    -- the members' order; an effect may not move
    let flds := (structDef f).map (·.1)
    if flds.isEmpty then throw s!"{f}(\{…}): {f} is not a struct or a function declared before this one"
    unless ns.length == flds.length && flds.all ns.contains do
      throw s!"{f}(\{…}) names each member of {f} once: {flds}"
    if ns != flds && args.any (·.hasIncDec) then
      throw s!"{f}(\{…}): an argument with an effect, out of the members' order"
    hoist (.call f (flds.map fun g => (lookupBy g (ns.zip args)).getD (.num 0)))
  | .call f args => do
    if (castTy? f).isSome then
      let [a] := args | throw s!"a cast {f}(…) takes one argument"
      let (P, a) ← hoist a
      let (Q, e) ← castCapture C f a
      return (P ++ Q, e)
    -- a struct's constructor (no function of that name): a fresh memory
    -- object, its members written in order, after the arguments are evaluated
    -- left to right (`T memory mv1; mv1.a = x; mv1.b = y;`)
    let flds := structDef f
    if (← read).funs.all (·.1 != f) && !flds.isEmpty then
      let (P, args) ← hoistArgs args
      unless flds.length == args.length do
        throw s!"{f} has {flds.length} members, not {args.length}"
      let x := toString (← freshCapture "mv")
      let Q ← elabStmtsP (.declMemory (.named f) x none ::
        (flds.zip args).map fun ((g, _), a) => .assign (.field (.name x) g) a)
      return (P ++ Q, .name x)
    -- a call inside an expression runs before the statement, into a fresh local
    let (P, args) ← hoistArgs args
    let some (_, d) := (← read).funs.find? (·.1 == f) | throw s!"{f} is not a function declared before this one"
    match d.ret with
      | some (r, .prim p) =>
        let n := (lookupBy r d.widths).getD 256
        let Γ ← nctx
        let x ← freshCapture "se"
        let Q ← elabCall f args (some (x, p)) n (resNew := true)
        declare C (toString x) (.val p n)
        pure (P ++ [.of Γ (.declLocal p x none)] ++ Q, .name (toString x))
      | some (_, .ref R) =>
        -- `Account memory mv1 = makeAccount();`
        let x ← freshCapture "mv"
        let Q ← elabMemCall f args R fun Γ r hm =>
          pure (.of ((r, .mem R) :: Γ) (.declMem R x (some (.alias (.var .here hm))) rfl hm))
        declare C (toString x) (.mem R)
        pure (P ++ Q, .name (toString x))
      | none =>
        if d.rets.isEmpty then throw s!"{f} returns no value"
        else throw s!"{f} returns {d.rets.length} values, which a tuple assignment takes"
  | .tuple _ => throw "a tuple is the right-hand side of a tuple assignment or of a `return`"
  | e => pure ([], e)

/-- `a ⊕ b`'s captures: the right operand first (solc evaluates it first: `i++ +
i` is `1 + 1`), the left one's after it, and the right one held before an
effect of the left. -/
partial def hoistBinop (op : BinOp) (a b : RawExpr) : ElabM (SProg C × RawExpr) := do
  let (Q, b) ← hoist b
  if a.hasIncDec then
    let (Qc, b) ← captureExpr C b
    let (P, a) ← hoist a
    pure (Q ++ Qc ++ P, .binop op a b)
  else if a.hasIdxLen || a.hasCast || hasNarrow C (← ctx) a then
    -- captures that may only revert: the right operand need not be held
    let (P, a) ← hoist a
    pure (Q ++ P, .binop op a b)
  else pure (Q, .binop op a b)

/-- `hoist`, but an operation at the top is left to the statement, which
checks its narrow width after the write (`narrowPost`). -/
partial def hoistTop : RawExpr → ElabM (SProg C × RawExpr)
  | .binop op a b => if op.shortCircuits then hoist (.binop op a b) else hoistBinop op a b
  | .unop op a => do
    let (P, a) ← hoist a
    pure (P, .unop op a)
  | e => hoist e

/-- `l = r;`: the right-hand side's captures, then the target's; an operation at
the top of `r` stays there when `l` is a variable (`hoistTop`). -/
partial def hoistAssign (l r : RawExpr) : ElabM (SProg C × RawStmt) := do
  let (P, r) ← if l matches .name _ then hoistTop r else hoist r
  let (Pc, r) ← if l.hasIncDec then captureExpr C r else pure ([], r)
  let (Q, l) ← hoist l
  pure (P ++ Pc ++ Q, .assign l r)

/-- A call's arguments, left to right: one read before a later argument's
effect is captured first, as a binary operator's operand is. -/
partial def hoistArgs : List RawExpr → ElabM (SProg C × List RawExpr)
  | [] => pure ([], [])
  | a :: as => do
    let (P, a) ← hoist a
    let (Pc, a) ← if as.any (·.hasIncDec) then captureExpr C a else pure ([], a)
    let (Q, as) ← hoistArgs as
    pure (P ++ Pc ++ Q, a :: as)

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
  let (P, r, _) ← elabCallRet f args none
  match r with
  | some ⟨Γ, R', r⟩ =>
    unless R' = R do throw s!"{f} returns a {Ty.ref R'}, not a {Ty.ref R}"
    let ⟨hm⟩ ← ElabM.lift (memOk R)
    pure (P ++ [← ElabM.lift (bind Γ r hm)])
  | none => throw s!"{f} does not return a memory reference"

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
    (resW : Nat := 256) (targets : Bool := false) (ctor : Bool := false) (resNew : Bool := false) :
    ElabM (SProg C × Option (NCtx × RefTy × Var) × List (PrimTy × Var × Nat)) := do
  let funs := (← read).funs
  -- the callee and the functions its body may call: the constructor (`elabCtor`)
  -- may call every function, a function those declared before it
  let (d, scope) ← if ctor then pure (C.ctor.getD { params := [], body := [] }, C.funs) else
    let some i := funs.findIdx? (·.1 == f) | throw s!"{f} is not a function declared before this one"
    pure ((funs[i]?.map (·.2)).getD default, funs.take i)
  unless d.params.length == args.length do
    throw s!"{f} takes {d.params.length} arguments, not {args.length}"
  let Γ ← ctx
  let Γn ← nctx
  -- the callee's locals are numbered from here to `k₁` (`ElabScope.inlined`)
  let k₀ := (← get).2
  let mut targs : (ps : Ctx) × Args C Γn.ctx ps := ⟨[], .nil⟩
  let mut ρ : List (String × String) := []
  -- the frame: the parameters, then the return variables, each newest first
  let mut Γp : ECtx := []
  for ((n, T), a) in d.params.zip args do
    let .prim p := T | throw s!"{f}: the parameter {n} has a reference type"
    let w := (lookupBy n d.widths).getD 256
    ElabM.lift (fitCheck C Γ p w a)
    let e ← checkIn C Γn p a
    let x ← freshCapture "se"
    targs := ⟨_, targs.2.snoc p x e⟩
    ρ := (n, toString x) :: ρ
    Γp := (toString x, .val p w) :: Γp
  let mut mret : Option (RefTy × Var) := none
  let mut mrets : List (PrimTy × Var × Nat) := []
  let mut Γr : ECtx := []
  let kind ← match d.rets, res with
    -- a void call with targets (a void function's obligation, `f(x̄)@C;`)
    -- is a `FunctionBodyStatement` all the same
    | [], none => pure (if targets then RetKind.rets [] else RetKind.none)
    | [], some _ => throw s!"{f} returns no value"
    | [(n, .ref R)], none => do
      if targets then throw s!"{f} returns a {Ty.ref R}, which a tuple assignment does not take"
      unless d.retMem do throw s!"{f}: its return of reference type {Ty.ref R} needs the location `memory`"
      let r ← freshCapture "mv"
      ρ := (n, toString r) :: ρ
      Γr := [(toString r, .mem R)]
      mret := some ⟨R, r⟩
      pure (RetKind.mem R r)
    | [(_, .ref R)], some (_, q) => throw s!"{f} returns a memory {Ty.ref R}, not a {Surface.primName q}"
    | [(n, .prim p)], res => do
      if d.retMem then throw s!"{f}: `memory` on its return of value type {Surface.primName p}"
      if let some (_, q) := res then
        unless q = p do throw s!"{f} returns a {Surface.primName p}, not a {Surface.primName q}"
      let w := (lookupBy n d.widths).getD 256
      if resW < w then throw s!"{f} returns a {tyName p w}, where a {tyName p resW} is expected"
      let r ← freshCapture "se"
      ρ := (n, toString r) :: ρ
      Γr := [(toString r, .val p w)]
      if targets then
        mrets := [(p, r, w)]
        pure (RetKind.rets [(p, r)])
      else pure (RetKind.val p r)
    | rs, some _ => throw s!"{f} returns {rs.length} values, which a tuple assignment takes"
    | rs, none => do
      if d.retMem then throw s!"{f}: `memory` on a return of a function of several returns"
      for (n, T) in rs do
        let .prim p := T | throw s!"{f}: its return {n} has a reference type"
        let w := (lookupBy n d.widths).getD 256
        let r ← freshCapture "se"
        ρ := (n, toString r) :: ρ
        Γr := (toString r, .val p w) :: Γr
        mrets := mrets ++ [(p, r, w)]
      if targets then pure (RetKind.rets (mrets.map fun (p, r, _) => (p, r))) else pure RetKind.none
  let Γf := Γr ++ Γp
  let body ← renameStmts ρ d.body
  let body ← lowerLoops (some (d.rets.map fun (n, _) => (lookupBy n ρ).getD n)) body
  let body ← ElabM.lift (lowerReturns (d.rets.map fun (n, _) => (lookupBy n ρ).getD n) body)
  let body ← wrapMods body (d.mods.map fun m => { m with args := m.args.map (·.rename ρ) })
  -- a constructor's initializers: after its parameters are bound, before its
  -- modifiers, in declaration order (solkey's `ExpandFunctionBody`)
  let body := (if ctor then C.inits.map fun (x, e) => RawStmt.assign (.name x) e else []) ++ body
  -- a block's locals renamed apart (a modifier's `_;` twice repeats the body's)
  let body ← ElabM.lift (freshenBlocks (C.vars.map (·.1)) (Γf.map (·.1)) body)
  let k₁ := (← get).2
  modify fun (_, k) => (Γf, k)
  let P ← withReader (fun sc => { funs := scope, top := false, inlined := (k₀, k₁) :: sc.inlined })
    (elabStmtsP body)
  modify fun (_, k) => (Γ, k)
  -- the call's context: the caller's, with `res` pushed when the statement
  -- before the call declares it
  let ⟨ps, as⟩ := targs
  let Γs : NCtx := match res with
    | some (x, p) => if resNew then (x, .val p) :: Γn else Γn
    | none => Γn
  let as := as.wk (← ElabM.lift (Γn.wkTo Γs))
  let call : SStmt C ← match kind with
    | .none =>
      -- several returns of a call that is a statement: declared on entry, at
      -- their defaults
      let (decls, _) := mrets.foldl (fun (acc : SProg C × NCtx) (p, r, _) =>
        (acc.1 ++ [.of acc.2 (.declLocal p r none)], (r, .val p) :: acc.2)) ([], ECtx.toNCtx Γp)
      let ⟨_, b⟩ ← ElabM.lift (SProg.chain as.names ([] ++ ps) (decls ++ P))
      pure (.of Γs (.call f as .none b))
    | .val p r =>
      let res' ← match res with
        | some (x, _) => do pure (some (← ElabM.lift (Γs.idx x (.val p))))
        | none => pure none
      let ⟨_, b⟩ ← ElabM.lift (SProg.chain (r :: as.names) ([.val p] ++ ps) P)
      pure (.of Γs (.call f as (.val p r res') b))
    | .rets l =>
      let ⟨ρs, bs⟩ := Binders.ofList l
      let ⟨_, b⟩ ← ElabM.lift (SProg.chain (bs.names ++ as.names) (ρs ++ ps) P)
      pure (.of Γs (.call f as (.rets bs) b))
    | .mem R r =>
      -- a memory return variable: declared on entry, a fresh default object
      let ⟨hm⟩ ← ElabM.lift (memOk R)
      match hd : (Ty.ref R).defaultOkS with
      | true =>
        let ⟨_, b⟩ ← ElabM.lift (SProg.chain (r :: as.names) ([.mem R] ++ ps) P)
        pure (.of Γs (.call f as (.mem R r hd hm) b))
      | false => throw s!"{f} returns a {Ty.ref R}, whose default is not well-formed"
  unless as.separated Γs.names do throw s!"{f}: an argument reads a parameter"
  pure ([call], mret.map fun (R, r) => (Γs, R, r), mrets)

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
partial def hoistStmt : RawStmt → ElabM (SProg C × RawStmt)
  | .assign l r => do
    -- `m = f(a);` to a memory local: its arguments only (`elabStmt1`)
    if let .call f args := r then
      if (← read).funs.any (·.1 == f) && synth C (← nctx) l matches .ok (.mpath (.ref _) (.var ..)) then
        let (P, args) ← hoistArgs args
        return (P, .assign l (.call f args))
    match r, synth C (← nctx) l with
    | .incDec op e, .ok (.val _ (.simple (.local _))) =>
      let (P, e) ← hoist e
      pure (P, .assignIncDec l op e)
    | .newArr T n, _ =>
      let (Q, l) ← hoist l
      pure (Q, .assign l (.newArr T n))
    | .call f args, .ok (.val _ (.simple (.local _))) =>
      if (castTy? f).isSome then hoistAssign l r
      else
        let (P, args) ← hoistArgs args
        pure (P, .assign l (.call f args))
    | _, _ => hoistAssign l r
  | .decl T x (some (.call f args)) => do
    if (castTy? f).isSome then
      let (P, r) ← hoist (.call f args)
      return (P, .decl T x (some r))
    let (P, args) ← hoistArgs args
    pure (P, .decl T x (some (.call f args)))
  | .decl T x (some r) => do
    let (P, r) ← hoistTop r
    pure (P, .decl T x (some r))
  | .declMemory T x (some (.newArr T' n)) => pure ([], .declMemory T x (some (.newArr T' n)))
  -- a statement of one expression: its captures, then the statement
  | s@(.decl ..) | s@(.declStorage ..) | s@(.declMemory ..) | s@(.declStoragePush ..)
  | s@(.delete _) | s@(.incDec ..) | s@(.ite ..) | s@(.require _) | s@(.assert _)
  | s@(.tryCall ..) => do
    -- `T memory x = f(a);`: its arguments only (`elabStmt1`)
    if let .declMemory T x (some (.call f args)) := s then
      if (← read).funs.any (·.1 == f) then
        let (P, args) ← hoistArgs args
        return (P, .declMemory T x (some (.call f args)))
    let (s, P) ← (s.mapExprsM fun e => do
      let (Q, e) ← hoist e
      modify (· ++ Q)
      pure e : StateT (SProg C) ElabM RawStmt).run []
    pure (P, s)
  | .opAssign op l r => do
    let (P, r) ← hoist r
    let (Pc, r) ← if l.hasIncDec then captureExpr C r else pure ([], r)
    let (Q, l) ← hoist l
    pure (P ++ Pc ++ Q, .opAssign op l r)
  | .assignIncDec x op l => do
    let (P, l) ← hoist l
    pure (P, .assignIncDec x op l)
  | .call (.field e m) args => do
    -- the receiver first, then the arguments
    let (P, e) ← hoist e
    let (Pc, e) ← if args.any (·.hasIncDec) && !(e matches .name _) then captureExpr C e
      else pure ([], e)
    let mut Q := P ++ Pc
    let mut args' := []
    for a in args do
      let (Q', a) ← hoist a
      Q := Q ++ Q'
      args' := args' ++ [a]
    pure (Q, .call (.field e m) args')
  | .call (.name f) args => do
    let (P, args) ← hoistArgs args
    pure (P, .call (.name f) args)
  | .assignPush l b => do
    let (P, b) ← hoist b
    let (Q, l) ← hoist l
    pure (P ++ Q, .assignPush l b)
  | .send T x r a => do
    -- the receiver first, then the amount, as `transfer`'s
    let (P, r) ← hoist r
    let (Pc, r) ← if a.hasIncDec && !(r matches .name _) then captureExpr C r
      else pure ([], r)
    let (Q, a) ← hoist a
    pure (P ++ Pc ++ Q, .send T x r a)
  | .eval args => do
    -- the effects captured, left to right; then what may still revert is
    -- evaluated into a fresh local, which nothing reads
    let (P, args) ← hoistArgs args
    let mut Q := P
    for a in args do
      unless a.isPure do Q := Q ++ (← captureExpr C a).1
    pure (Q, .eval [])
  | s => pure ([], s)

/-- A statement, as a block: its narrow rewrites (`narrowPure`), its captures
(`hoistStmt`), then the statement,
whose compound target may need a capture of its own. -/
partial def elabStmtP (s : RawStmt) : ElabM (SProg C) := do
  let s ← ElabM.lift (s.mapExprsM (RawExpr.orderNamed (← read).funs))
  -- a loop outside a function's body, lowered here (`lowerLoops`)
  if s matches .whileLoop .. | .forLoop .. | .doWhile .. then
    return ← elabStmtsP (← lowerLoops none [s])
  let s ← ElabM.lift (s.mapExprsM (narrowPure C (← ctx)))
  let (P, s) ← hoistStmt s
  pure (P ++ (← elabStmt1 s))

/-- A statement whose expressions have no effect left. -/
partial def elabStmt1 : RawStmt → ElabM (SProg C)
  | .assign l (.newArr T n) => do
    let ⟨R, hR⟩ ← elabNewTy C T
    let (P, ⟨Γ, se⟩) ← elabSize C n
    match ← ElabM.lift (synth C Γ l) with
    | .mpath (.ref R') (.var x _) =>
      if h : R' = R then pure (P ++ [.of Γ (.rebindMem (h ▸ x) (.newArr se hR))])
      else throw "`new` of another type than the memory local's"
    | .mpath T' (.loc ml) =>
      if hT : T' = .ref R then pure (P ++ [.of Γ (.assignNew (.mem (hT ▸ ml)) se hR)])
      else throw "`new` of another type than the member's"
    | .path T' (.loc sl) =>
      if hT : T' = .ref R then pure (P ++ [.of Γ (.assignNew (.store (hT ▸ sl)) se hR)])
      else throw "`new` of another type than the location's"
    | .path _ (.alias _) => throw "a storage pointer bound to a memory array"
    | .val .. => throw "`new` assigned to a value"
  | .assign l (.call f args) => do
    let ⟨Γ, t⟩ ← synthM C l
    match t with
    | .val p (.simple (.local x)) => elabCall f args (some (x.name Γ.names, p)) (widthIn C (← ctx) l)
    | .mpath (.ref R) (.var x _) =>
      let xn := x.name Γ.names
      elabMemCall f args R fun Γ' r hm => do
        let Γr : NCtx := (r, .mem R) :: Γ'
        pure (.of Γr (.rebindMem (← Γr.idx xn (.mem R)) (.alias (.var .here hm))))
    | _ => throw "a call's value is assigned to a stack local"
  | .assign l r => do
    let post ← narrowPost C l r
    let ⟨Γ, t⟩ ← synthM C l
    let P : SProg C ← match t with
      | .val p (.simple (.local x)) => do pure [.of Γ (.assignLocal x (← checkIn C Γ p r))]
      | .val p _ => throw s!"{l.toStr} is a {p.toStr} value, not a place to assign to"
      | .path (.prim p) (.loc l) => do pure [.of Γ (.assign l (.val (← checkIn C Γ p r)))]
      | .path (.ref R) (.loc l) => do
        match ← ElabM.lift (synth C Γ r) with
        | .mpath T mp =>
          if hT : T = .ref R then pure [.of Γ (.assignFromMem l (hT ▸ mp))]
          else throw s!"{r.toStr}: a memory reference to a {T} where a {Ty.ref R} is expected"
        | _ =>
          match h : (Ty.ref R).mapFree with
          | true => do pure [.of Γ (.assign l (.copy (← ElabM.lift (checkPath C Γ (.ref R) r)) h))]
          | false => throw "a storage copy of a type that holds a mapping"
      | .path (.ref R) (.alias x) => do
        pure [.of Γ (.rebind x (.path (← ElabM.lift (checkPath C Γ (.ref R) r))))]
      | .mpath (.ref R) (.var x _) => do pure [.of Γ (.rebindMem x (← ElabM.lift (elabMRhs C Γ R r)))]
      | .mpath (.prim p) (.loc l) => do pure [.of Γ (.assignMem l (.val (← checkIn C Γ p r)))]
      | .mpath (.ref R) (.loc l) => do
        pure [.of Γ (.assignMem l (.ref (← ElabM.lift (checkMPath C Γ (.ref R) r))))]
    pure (P ++ post)
  | .decl T x (some (.call f args)) => do
    let (.prim p, n) ← ElabM.lift (elabDeclTy C T) | throw s!"{x}: a reference type needs a data location"
    let Γ ← nctx
    let P ← elabCall f args (some (Var.ofName x, p)) n (resNew := true)
    declare C x (.val p n)
    pure (.of Γ (.declLocal p (Var.ofName x) none) :: P)
  | .decl T x init => do
    let (.prim p, n) ← ElabM.lift (elabDeclTy C T) | throw s!"{x}: a reference type needs a data location"
    let Γ ← nctx
    let v ← init.mapM (checkIn C Γ p)
    declare C x (.val p n)
    let post ← match init with
      | some r => narrowPost C (.name x) r
      | none => pure []
    pure (.of Γ (.declLocal p (Var.ofName x) v) :: post)
  | .declStorage T x init => do
    let .ref R ← ElabM.lift (elabTy C T) | throw s!"{x}: `storage` on a value type"
    let Γ ← nctx
    let init ← ElabM.lift (init.mapM fun e => ARhs.path <$> checkPath C Γ (.ref R) e)
    declare C x (.alias R)
    pure [.of Γ (.declStorage R (Var.ofName x) init)]
  | .declStoragePush T x b => do
    let .ref R ← ElabM.lift (elabTy C T) | throw s!"{x}: `storage` on a value type"
    let Γ ← nctx
    let r ← ElabM.lift (elabPush C Γ R b)
    declare C x (.alias R)
    pure [.of Γ (.declStorage R (Var.ofName x) (some r))]
  | .assignPush l b => do
    let ⟨Γ, t⟩ ← synthM C l
    match t with
    | .path (.ref R) (.alias x) => pure [.of Γ (.rebind x (← ElabM.lift (elabPush C Γ R b)))]
    | _ => throw "`= b.push()` binds a storage pointer"
  | .declMemory T x (some (.newArr T' n)) => do
    let .ref R ← ElabM.lift (elabTy C T) | throw s!"{x}: `memory` on a value type"
    let ⟨R', hR⟩ ← elabNewTy C T'
    unless R' = R do throw s!"{x}: `new` of another type"
    let (P, ⟨Γ, se⟩) ← elabSize C n
    declare C x (.mem R')
    pure (P ++ [.of Γ (.declMem R' (Var.ofName x) (some (.newArr se hR)) rfl
      (MRhs.newArr (C := C) se hR).mapFree)])
  | .declMemory T x (some (.call f args)) => do
    let .ref R ← ElabM.lift (elabTy C T) | throw s!"{x}: `memory` on a value type"
    let P ← elabMemCall f args R fun Γ r hm =>
      pure (.of ((r, .mem R) :: Γ) (.declMem R (Var.ofName x) (some (.alias (.var .here hm))) rfl hm))
    declare C x (.mem R)
    pure P
  | .declMemory T x init => do
    let .ref R ← ElabM.lift (elabTy C T) | throw s!"{x}: `memory` on a value type"
    let Γ ← nctx
    let s : Stmt C Γ.ctx (.mem R :: Γ.ctx) ← match init with
      | some e =>
        let r ← ElabM.lift (elabMRhs C Γ R e)
        pure (Stmt.declMem R (Var.ofName x) (some r) rfl r.mapFree)
      | none =>
        let ⟨hm⟩ ← ElabM.lift (memOk R)
        match hd : (Ty.ref R).defaultOkS with
        | true => pure (Stmt.declMem R (Var.ofName x) none (by simp only [Option.isSome_none, hd, Bool.or_true]) hm)
        | false => throw s!"{x}: a memory object whose default is not well-formed"
    declare C x (.mem R)
    pure [.of Γ s]
  | .delete e => do
    let ⟨Γ, t⟩ ← synthM C e
    match t with
    | .path T (.loc l) =>
      if T matches .ref (.mapping ..) then throw "a mapping cannot be deleted"
      else pure [.of Γ (.delete l)]
    | .path _ (.alias _) => throw "`delete` on a storage pointer"
    | .mpath T p =>
      match hd : T.defaultOkS with
      | true => pure [.of Γ (.deleteMem p hd)]
      | false => throw "`delete` of a memory object whose default is not well-formed"
    | .val .. => throw "`delete` needs a storage or a memory location"
  | .opAssign op l r => do
    -- `&= |= ^= <<= >>=` and a wrapping `+=`: `l = l ⊕ r`, the target's
    -- effects already captured (`hoistStmt`), so reading it twice is safe
    if op.isArith && !op.hasCompoundAssign && op != .pow then
      return ← elabStmt1 (.assign l (← ElabM.lift (narrowWrapNode C (← ctx) (.binop op l r))))
    let (pre, ⟨Γ, p, t⟩) ← elabOpTarget C l
    -- at a narrow target, what `l ⊕ r` may leave the type by is checked after
    let n := widthIn C (← ctx) l
    ElabM.lift (fitCheck C (← ctx) p n r)
    let post ← if (op matches .add | .sub | .mul) || (op == .div && p == .int) then
      narrowCheck C p n l else pure []
    match hop : op.hasCompoundAssign, hp : p.isNumeric with
    | true, true => pure (pre ++ [.of Γ (.opAssign op hop hp t (← checkIn C Γ p r))] ++ post)
    | false, _ => throw s!"no compound assignment for {BinOp.sym op}"
    | _, false => throw s!"a compound assignment at {Surface.primName p}"
  | .incDec op l => do
    let (pre, ⟨Γ, p, t⟩) ← elabOpTarget C l
    match hp : p.isNumeric with
    | true => pure (pre ++ [.of Γ (.incDec op hp t)] ++ (← narrowCheck C p (widthIn C (← ctx) l) l))
    | false => throw s!"++ or −− at {Surface.primName p}"
  | .assignIncDec x op l => do
    let (pre, ⟨Γ, p, t, hs⟩) ← elabIncTarget C l
    match ← ElabM.lift (synth C Γ x) with
    | .val q (.simple (.local y)) =>
      ElabM.lift (fitCheck C (← ctx) q (widthIn C (← ctx) x) l)
      match hp : p.isNumeric with
      | true => if h : q = p then
                  pure (pre ++ [.of Γ (.assignIncDec (h ▸ y) op hp t hs)] ++
                    (← narrowCheck C p (widthIn C (← ctx) l) l))
                else throw s!"a {Surface.primName p} assigned to a {Surface.primName q}"
      | false => throw s!"++ or −− at {Surface.primName p}"
    | _ => throw "the result of ++ or −− goes to a stack local"
  | .call (.field e "push") args => do
    let ⟨Γ, t⟩ ← synthM C e
    let .path (.ref (.array E)) b := t | throw "push on something that is not an array"
    match args with
    | [] =>
      match hd : E.defaultOkS with
      | true => pure [.of Γ (.push b none (by simp only [Option.isSome_none, hd, Bool.or_true]))]
      | false => throw "push() of an element whose default is not well-formed"
    | [a] =>
      match E with
      | .prim p => pure [.of Γ (.push b (some (.val (← checkIn C Γ p a))) rfl)]
      | .ref R =>
        -- a memory object (a struct's constructor): a default slot pushed,
        -- then written with its copy
        if (← ElabM.lift (synth C Γ a)) matches .mpath .. then
          return ← elabStmtsP [.call (.field e "push") [],
            .assign (.index e (.binop .sub (.field e "length") (.num 1))) a]
        match h : (Ty.ref R).mapFree with
        | true => pure [.of Γ (.push b (some (.copy (← ElabM.lift (checkPath C Γ (.ref R) a)) h)) rfl)]
        | false => throw "a push copying a type that holds a mapping"
    | _ => throw "push takes at most one argument"
  | .call (.field e "pop") [] => do
    let ⟨Γ, t⟩ ← synthM C e
    let .path (.ref (.array _)) b := t | throw "pop on something that is not an array"
    pure [.of Γ (.pop b)]
  | .call (.field e "transfer") [a] => do
    let Γ ← nctx
    pure [.of Γ (.transfer (← checkIn C Γ .uint e) (← checkIn C Γ .uint a))]
  | .send T x e a => do
    let Γ ← nctx
    let r ← checkIn C Γ .uint e
    let v ← checkIn C Γ .uint a
    match T, x with
    | some T, .name n =>
      let (.prim .bool, w) ← ElabM.lift (elabDeclTy C T)
        | throw s!"{n}: `send` returns a bool"
      declare C n (.val .bool w)
      let ⟨Γ', th, ix⟩ ← afterCapture Γ (Var.ofName n) (.val .bool)
      pure [.of Γ (.declLocal .bool (Var.ofName n) none), .of Γ' (.send ix (r.wk th) (v.wk th))]
    | some _, _ => throw "`T x = r.send(a);` declares a name"
    | none, x =>
      match ← ElabM.lift (synth C Γ x) with
      | .val .bool (.simple (.local y)) => pure [.of Γ (.send y r v)]
      | _ => throw s!"{x.toStr}: a send's result goes to a bool local"
  | .call (.name "constructor") args => elabCtor args
  | .call (.name f) args => elabCall f args none
  | .call .. => throw "only push, pop and transfer are calls on a receiver"
  | .ret _ => throw "`return` outside a function's body"
  | .brk => throw "`break` outside a loop"
  | .cont => throw "`continue` outside a loop"
  | .hole => throw "`_;` outside a modifier's body"
  | s@(.whileLoop ..) | s@(.forLoop ..) | s@(.doWhile ..) => do elabStmtsP (← lowerLoops none [s])
  | .loop a c body => do
    -- evaluated again each iteration, so it is not captured before the loop
    let Γ ← nctx
    let c ← loopExpr Γ .bool c "condition"
    let a : LoopAnn C Γ.ctx ← match a.inv, a.unwind with
      | [], u => do
        if a.dec.isSome then throw "a loop's `decreases` clause without an `invariant`"
        pure (LoopAnn.unwind (u.getD 0))
      | i :: is, none => do
        let I ← loopExpr Γ .bool (RawExpr.andAll (i :: is).dropLast ((i :: is).getLast?.getD i))
          "invariant"
        pure (.inv I (← a.dec.mapM fun d => loopExpr Γ .uint d "variant"))
      | _ :: _, some _ => throw "a loop has an `invariant` or an `unwind` clause, not both"
    pure [.of Γ (.loop a c (← elabScope Γ body).2)]
  | .block b => elabBranch b
  | .tupleAssign ts rhs => elabTuple ts rhs
  | .tupleDecl vs rhs => do
    -- `T x;` for each variable, then the tuple assigned to them
    for (_, x) in vs.filterMap id do
      if rhs.mentions x then throw s!"{rhs.toStr} reads {x}, which the tuple declares"
    let P ← elabStmtsP (vs.filterMap fun v => v.map fun (T, x) => .decl T x none)
    pure (P ++ (← elabTuple (vs.map fun v => v.map fun (_, x) => .name x) rhs (direct := true)))
  | .ite c thn els => do
    let Γ ← nctx
    let c ← checkIn C Γ .bool c
    let thn ← elabScope Γ thn
    let els ← elabScope Γ els
    pure [.of Γ (.ite c thn.2 els.2)]
  | .require c => do
    let Γ ← nctx
    pure [.of Γ (.require (← checkIn C Γ .bool c))]
  | .assert c => do
    let Γ ← nctx
    pure [.of Γ (.assert (← checkIn C Γ .bool c))]
  | .revert => do pure [.of (← nctx) .revert]
  | .eval _ => pure []
  | .unchecked ss => do elabBranch (← ElabM.lift (uncheckStmts ss))
  | .tryCall e g as rets ok err code pnc other => do
    -- `I(a)` is `a`
    let funs := (← read).funs
    let e := match e with
      | .call h [a] => if funs.any (·.1 == h) then e else a
      | e => e
    let (P, addr) ← simpleOf C .uint e
    let mut Q := P
    let mut args : List ((Γ : NCtx) × ExtArg C Γ.ctx) := []
    for a in as do
      let some ⟨p, _⟩ := (← synthM C a).2.toVal? | throw s!"{a.toStr}: an external call's argument is a value"
      let (Q', ⟨Γa, se⟩) ← simpleOf C p a
      Q := Q ++ Q'
      args := args ++ [⟨Γa, ⟨p, se⟩⟩]
    let mut rets' : List (PrimTy × Var) := []
    for (T, x) in rets do
      let (.prim p, n) ← ElabM.lift (elabDeclTy C T) | throw s!"{x}: an external call returns a value"
      unless n == 256 do throw s!"{x}: a narrow return value of an external call"
      rets' := rets' ++ [(p, Var.ofName x)]
    -- the call is read where its arguments' captures leave
    let Γ ← nctx
    let addr' := addr.2.wk (← ElabM.lift (addr.1.wkTo Γ))
    let args' ← args.mapM fun ⟨Γa, a⟩ => do
      pure (⟨a.1, a.2.wk (← ElabM.lift (Γa.wkTo Γ))⟩ : ExtArg C Γ.ctx)
    let ⟨ρ, bs⟩ := Binders.ofList rets'
    let ⟨κ, cb⟩ := CodeBinder.ofOption (code.map Var.ofName)
    let (Γe, _) ← get
    for (p, x) in rets' do declare C (toString x) (.val p)
    let ok ← elabStmtsP ok
    let ok ← ElabM.lift (SProg.chain (bs.names ++ Γ.names) (ρ ++ Γ.ctx) ok)
    let (_, k) ← get
    set (Γe, k)
    let err ← elabScope Γ err
    if let some c := code then declare C c (.val .uint)
    let pnc ← elabStmtsP pnc
    let pnc ← ElabM.lift (SProg.chain (cb.names ++ Γ.names) (κ ++ Γ.ctx) pnc)
    let (_, k) ← get
    set (Γe, k)
    let other ← elabScope Γ other
    pure (Q ++ [.of Γ (.tryCall ⟨addr', g, args'⟩ bs ok.2 err.2 cb pnc.2 other.2)])

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

/-- **A tuple assignment** `(t₀, , t₂) = e;`, written out as solkey's
`ParserUtils.tupleAssignment` writes it.  From a call of a function of several
returns: the call (`CallRet.rets`), then `tᵢ = rᵢ;` for each target, left to
right (a component left out is not read).  From a tuple `(e₀, e₁, e₂)`: each
component with a target into a fresh temporary, left to right, then each
target assigned its temporary, left to right; a component left out is
dropped if it can neither revert nor have an effect, and evaluated
otherwise (solc's; solkey keeps only a call).  Targets that may alias (the same name
twice, two that are not stack locals, one that reads another) are refused:
solc's order of their writes is not KeY's.  The variables of a tuple
declaration, which no component reads, are assigned directly (`direct`). -/
partial def elabTuple (ts : List (Option RawExpr)) (rhs : RawExpr) (direct : Bool := false) :
    ElabM (SProg C) := do
  let tgts := ts.filterMap id
  let mut nonLocal := 0
  for t in tgts do
    if t.hasIncDec then throw s!"{t.toStr}: a tuple's target with an effect"
    unless (← synthM C t).2 matches .val _ (.simple (.local _)) do nonLocal := nonLocal + 1
    for u in tgts do
      if let .name x := u then
        if t.toStr != u.toStr && t.mentions x then throw s!"{t.toStr}: a tuple's target that reads {x}, another"
  if nonLocal > 1 then throw "a tuple assignment to two targets that are not stack locals"
  unless (tgts.map (·.toStr)).eraseDups.length == tgts.length do
    throw "a tuple assignment to the same target twice"
  match rhs with
  | .call f args =>
    -- a function not declared before this one is `elabCallRet`'s error
    unless (castTy? f).isNone do
      throw s!"{f}(…): the right-hand side of a tuple assignment is a call of a function"
    let (P, args) ← hoistArgs args
    let (Q, _, rs) ← elabCallRet f args none (targets := true)
    unless rs.length == ts.length do throw s!"{f} returns {rs.length} values, not {ts.length}"
    for (p, r, w) in rs do declare C (toString r) (.val p w)
    let R ← elabStmtsP ((ts.zip rs).filterMap fun (t, (_, r, _)) =>
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
        let p ← match (← synthM C t).2 with
          | .val p _ | .path (.prim p) _ | .mpath (.prim p) _ => pure p
          | _ => throw s!"{t.toStr}: a tuple's component of a reference type"
        let x := toString (← freshCapture "se")
        tmps := tmps ++ [.decl (.named (tyName p (widthIn C (← ctx) t))) x (some e)]
        asgs := asgs ++ [.assign t (.name x)]
      | none => unless e.isPure do tmps := tmps ++ [.eval [e]]
    elabStmtsP (tmps ++ asgs)
  | _ => throw s!"{rhs.toStr}: the right-hand side of a tuple assignment is a tuple or a call"

end

/-! ### The statement as written

The readers not yet moved to the scoped syntax read a block's erasure
(`Prog.erase`, `Syntax/Resolve.lean`), from the names of the locals in
scope: the same statements `Syntax.lean`'s elaborator wrote. -/

/-- A block of statements, from the locals in scope. -/
def elabStmtsS (ss : List RawStmt) : ElabM ((Γ : NCtx) × Blk C Γ.ctx) := do
  let Γ ← nctx
  pure ⟨Γ, ← ElabM.lift (SProg.chain Γ.names Γ.ctx (← elabStmtsP C ss))⟩

/-- A statement, as written (`Surface.Prog C`). -/
def elabStmt (s : RawStmt) : ElabM (Surface.Prog C) := do
  let Γ ← nctx
  let ⟨_, P⟩ ← ElabM.lift (SProg.chain Γ.names Γ.ctx (← elabStmtP C s))
  pure (P.erase Γ.names)

/-- A block, as written (`Surface.Prog C`). -/
def elabStmts (ss : List RawStmt) : ElabM (Surface.Prog C) := do
  let ⟨Γ, _, P⟩ ← elabStmtsS C ss
  pure (P.erase Γ.names)

end Elab

end Solidity
