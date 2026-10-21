import Solidity.Syntax.Scoped
import Solidity.Syntax.Checked
import Solidity.Keccak

/-!
# The elaborator

`sol[C]{ … }` reads Solidity statements (`Syntax.lean`'s grammar, `RawStmt`)
and this module types them against the contract `C`, into the scoped syntax
(`Syntax/Scoped.lean`): a local is the position `Idx Γ t` of the newest
local of its name in the context it is read in (`NCtx.find`), which says
when a name is not declared or is declared at another type.  Synthesis returns a path or a value with its type;
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

The entry points are `Syntax/Splice.lean`'s.
-/

namespace Solidity

open Semantics

/-! ## Named contexts -/

/-- Named locals, innermost first: a context with its names beside it. -/
abbrev NCtx := List (Var × LTy)

/-- The types. -/
abbrev NCtx.ctx (Γ : NCtx) : Ctx := Γ.map (·.2)

/-- The names. -/
abbrev NCtx.names (Γ : NCtx) : List Var := Γ.map (·.1)

/-- How a declaration writes the type: `uint`, `Person storage`, `Person memory`. -/
def LTy.toStr : LTy → String
  | .val p => p.toStr
  | .alias R => s!"{Ty.ref R} storage"
  | .mem R => s!"{Ty.ref R} memory"
  | .old => "storage"
  | .oldNet => "ledger"
  | .kint => "int (KeY)"

/-- The newest local named `x`, which must be of type `t`. -/
def NCtx.find [FreshNames] (x : Var) (t : LTy) :
    (Γ : NCtx) → Except String {i : Idx Γ.ctx t // i.name Γ.names = x}
  | [] => .error s!"{x} is not declared"
  | (y, u) :: Γ =>
    if hy : y = x then
      if hu : u = t then by subst hu hy; exact .ok ⟨.here, rfl⟩
      else .error s!"{x} is declared as {u.toStr}, used as {t.toStr}"
    else
      match NCtx.find x t Γ with
      | .ok ⟨i, h⟩ => .ok ⟨.there i, h⟩
      | .error e => .error e

/-- `bs` with the locals `l` bound after it, in order. -/
def Binders.snocAll {ρ : Ctx} (bs : Binders ρ) : List (PrimTy × Var) → (ρ' : Ctx) × Binders ρ'
  | [] => ⟨ρ, bs⟩
  | (p, x) :: l => (bs.snoc p x).snocAll l

/-- The locals `l` bound in order. -/
def Binders.ofList (l : List (PrimTy × Var)) : (ρ : Ctx) × Binders ρ := Binders.nil.snocAll l

def CodeBinder.ofOption : Option Var → (κ : Ctx) × CodeBinder κ
  | Option.none => ⟨[], .none⟩
  | Option.some x => ⟨[.val .uint], .some x⟩

/-- A block read in a context equal to its own (an appended context `ρ ++ Γ`
read as the named context built for it, equal to it but not by
definition). -/
def Prog.castIn {C : Contract} {Γ₁ Γ₂ Δ : Ctx} (h : Γ₁ = Γ₂) (P : Prog C Γ₁ Δ) : Prog C Γ₂ Δ :=
  h ▸ P

/-- What a local in scope holds. -/
inductive LocalTy where
  /-- A stack local of type `p`, `bits` wide (`uint8 x` is a `uint` 8 bits wide). -/
  | val (p : PrimTy) (bits : Nat := 256)
  | alias (R : RefTy)
  | mem (R : RefTy)
  /-- A storage variable, `old`: only a formula binds one (`old := storage`),
  and a program cannot read it. -/
  | store
  /-- A logical variable of KeY's `int`: only a formula binds one (a
  parameter read beside the ledger), and a program cannot read it. -/
  | kint
  /-- Not a local: the narrow positions inside the alias or memory local `x`,
  under the name `#x` (`declareShape`), keyed by their path below `x` as
  `Contract.widths` keys a state variable's (`uint8[] memory m` is `[]` at
  `8`).  A reference type has no width, so a local's rides beside it;
  `ECtx.toNCtx` drops it. -/
  | shape (ws : List (String × Nat))
  deriving DecidableEq, Repr

/-- The locals in scope, most recent first. -/
abbrev ECtx := List (Name × LocalTy)

/-- The narrow positions below the key `k` of a width table, keyed by their
path below it: `small[]` is `[]` under `small` (`Contract.widths`,
`FunDecl.widths`, `structWidths`). -/
def shapeUnder (tb : List (String × Nat)) (k : String) : List (String × Nat) :=
  tb.filterMap fun (k', n) =>
    if k'.startsWith (k ++ "[") || k'.startsWith (k ++ "{") || k'.startsWith (k ++ "#") then
      some (k'.drop k.length, n)
    else none

/-- Two shapes name the same narrow positions at the same widths. -/
def sameShape (a b : List (String × Nat)) : Bool :=
  -- the ABI's markers, which no conversion of a reference type depends on
  let abiOnly (r : String × Nat) : Bool :=
    r.1.endsWith "#address" || r.1.endsWith "#enum" || r.1.endsWith "#string"
  let a := a.filter (!abiOnly ·)
  let b := b.filter (!abiOnly ·)
  a.all (b.contains ·) && b.all (a.contains ·)

/-- The entry beside a reference local `x` holding its narrow positions, if it has any. -/
def shapeEntry (x : Name) (ws : List (String × Nat)) : List (Name × LocalTy) :=
  if ws.isEmpty then [] else [("#" ++ x, .shape ws)]

/-- Parameters retain their declared data locations in the function frame; a
reference one its narrow positions (`shapeEntry`). -/
def FunDecl.paramCtx (d : FunDecl) : Except String ECtx := do
  let rows ← d.params.reverse.mapM fun (n, T) => match T with
    | .prim p =>
      if (lookupBy n d.paramLocs).isSome then
        .error s!"data location on value parameter {n}"
      else .ok (shapeEntry n (shapeUnder d.widths n) ++ [(n, .val p ((lookupBy n d.widths).getD 256))])
    | .ref R => match lookupBy n d.paramLocs with
      | some .storage => .ok (shapeEntry n (shapeUnder d.widths n) ++ [(n, .alias R)])
      | some .memory =>
        if (Ty.ref R).mapFree then .ok (shapeEntry n (shapeUnder d.widths n) ++ [(n, .mem R)])
        else .error s!"memory parameter {n} holds a mapping"
      | some .calldata => .error s!"calldata parameter {n} is not supported"
      | none => .error s!"reference parameter {n} needs a data location"
  pure rows.flatten

/-- A type as read, against the contract: a primitive type (`PrimTy.ofName?`),
an enum of `C` (a `uint`, as a state variable of it is), a struct of `C`
or of the table (`Contract.structName?`).  Any other name is refused (`unknownStructMsg`: a struct
solc refuses, `refusedStructs`, or an unknown type). -/
def elabTy (C : Contract) : RawTy → Except String Ty
  | .named s =>
    match PrimTy.ofName? s with
    | some p => pure (.prim p)
    | none =>
      if (lookupBy s C.enums).isSome then pure .uint
      else if (narrowTy? s).isSome || (bytesTy? s).isSome || dynBytesTy s || fnTy? s then
        throw (narrowNestedMsg s)
      else match C.structName? s with
        | some e => pure (.struct e)
        | none => throw (unknownStructMsg s)
  | .mapping k v => do
    if let .named s := k then
      if dynBytesTy s then return .mapping .uint (← elabTy C v)
    match ← elabTy C k with
    | .prim p => pure (.mapping p (← elabTy C v))
    | t => throw s!"a mapping's key is a value type, not {t.toStr}"
  | .array t => do pure (.array (← elabTy C t))
  | .fixed t n => do pure (.fixed (← elabTy C t) n)

/-- A declared variable's type: `elabTy`'s, or a narrow integer type
(`narrowTy?`) as its primitive type; and its width. -/
def elabDeclTy (C : Contract) : RawTy → Except String (Ty × Nat)
  | .named s =>
    match narrowTy? s, bytesTy? s with
    | some (p, n), _ => pure (.prim p, n)
    | none, some n => pure (.uint, 8 * n)
    | none, none =>
      -- a function type: its tag, a `uint` ("Function types", `Syntax.lean`)
      if fnTy? s then pure (.uint, 256) else do pure (← elabTy C (.named s), 256)
  | T => do pure (← elabTy C T, 256)

/-- The marker of a value type: `[("#bytes", N)]` for a `bytesN`,
`[("#function(…)…", 0)]` for a function type. -/
def bytesRowsOf (C : Contract) : RawTy → Except String (List (String × Nat))
  | .named s =>
    if fnTy? s then pure [("#" ++ s, 0)]
    else if s == "address" then pure addressRows
    else if (lookupBy s C.enums).isSome then pure enumRows
    else pure ((bytesTy? s).toList.map fun n => ("#bytes", n))
  | _ => pure []

/-- A local's or a `new`'s type, where a narrow type may stand inside it: its
`Ty`, and the widths of its narrow positions keyed by their path below it, as
`expandStateTyW` reads a state variable's (`uint8[]` is `[("[]", 8)]`, a
mapping's key `{}`). -/
def elabTyW (C : Contract) : RawTy → Except String (Ty × List (String × Nat))
  | .named s =>
    if dynBytesTy s then pure (.array .uint, dynBytesRowsOf s) else
    if (lookupBy s C.enums).isSome then pure (.uint, enumRows) else
    match valueRows? s with
    | some (p, ws) => pure (.prim p, ws)
    | none => do pure (← elabTy C (.named s), [])
  | .mapping k v => do
    if let .named s := k then
      if dynBytesTy s then
        let (vt, vw) ← elabTyW C v
        return (.mapping .uint vt, hashKeyRows ++ vw.map fun (k, n) => ("[]" ++ k, n))
    let (kt, kw) ← elabTyW C k
    let .prim p := kt | throw s!"a mapping's key is a value type, not {kt.toStr}"
    let (vt, vw) ← elabTyW C v
    pure (.mapping p vt, kw.map (fun (k, n) => ("{}" ++ k, n)) ++ vw.map fun (k, n) => ("[]" ++ k, n))
  | .array t => do
    let (t, w) ← elabTyW C t
    pure (.array t, w.map fun (k, n) => ("[]" ++ k, n))
  | .fixed t m => do
    let (t, w) ← elabTyW C t
    pure (.fixed t m, w.map fun (k, n) => ("[]" ++ k, n))

/-- The name of the value type at the key `k` of the width table `ws`: a
`bytesN` where it has a marker row (`valueRows?`), else `p` at its width. -/
def declTyName (ws : List (String × Nat)) (k : String) (p : PrimTy) : String :=
  match lookupBy (k ++ "#bytes") ws with
  | some n => s!"bytes{n}"
  | none =>
    if (lookupBy (k ++ "#address") ws).isSome then "address" else tyName p ((lookupBy k ws).getD 256)

/-- `T` written back as a declared type, its narrow positions at their widths
in `ws`, keyed by their path below `k` (`elabTyW`'s inverse: a modifier's
reference parameter, declared as a local of its type). -/
partial def rawTyW (ws : List (String × Nat)) : Ty → String → RawTy
  | .prim p, k => .named (declTyName ws k p)
  | .ref (.struct s), _ => .named s
  | .ref (.array E), k => .array (rawTyW ws E (k ++ "[]"))
  | .ref (.fixed E n), k => .fixed (rawTyW ws E (k ++ "[]")) n
  | .ref (.mapping p V), k =>
    .mapping (.named (if (lookupBy (k ++ "{}#hash") ws).isSome then "string"
      else declTyName ws (k ++ "{}") p)) (rawTyW ws V (k ++ "[]"))

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
  | .unop op a => op.show (a.toStr (op matches .toInt | .toUint))
  | .ternary c a b => paren s!"{c.toStr false} ? {a.toStr false} : {b.toStr false}"
  | .incDec op e => IncDec.show op (e.toStr false)
  | .newArr T n => s!"new {T.toStr}({n.toStr})"
  | .call f as => s!"{f}({", ".intercalate (as.map (·.toStr))})"
  | .modular op a b k => s!"{op.toStr}({a.toStr}, {b.toStr}, {k.toStr})"
  | .named f ns as =>
    s!"{f}(\{{", ".intercalate ((ns.zip as).map fun (n, a) => s!"{n}: {a.toStr}")}})"
  | .env k => k.toStr
  | .tuple es => s!"({", ".intercalate (es.map (·.toStr))})"
  | .assign l r => s!"({l.toStr} = {r.toStr})"
  | .opAssign op l r => s!"({l.toStr} {op.sym}= {r.toStr})"

/-- Whether `p` holds of the expression or of an expression inside it. -/
def RawExpr.any (p : RawExpr → Bool) (e : RawExpr) : Bool :=
  p e || match e with
    | .field a _ | .unop _ a | .incDec _ a | .newArr _ a => a.any p
    | .index a b | .binop _ a b | .assign a b | .opAssign _ a b => a.any p || b.any p
    | .ternary c a b => c.any p || a.any p || b.any p
    | .modular _ a b k => a.any p || b.any p || k.any p
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
  | .modular op a b k => return .modular op (← a.mapM f) (← b.mapM f) (← k.mapM f)
  | .named g ns as => return .named g ns (← as.mapM (·.mapM f))
  | .tuple as => return .tuple (← as.mapM (·.mapM f))
  | .assign l r => return .assign (← l.mapM f) (← r.mapM f)
  | .opAssign op l r => return .opAssign op (← l.mapM f) (← r.mapM f)
  | e => pure e

/-- The names a raw expression reads, in order. -/
def RawExpr.names : RawExpr → List String
  | .name x => [x]
  | .field e _ | .unop _ e | .incDec _ e | .newArr _ e => e.names
  | .index a b | .binop _ a b | .assign a b | .opAssign _ a b => a.names ++ b.names
  | .ternary c a b => c.names ++ a.names ++ b.names
  | .call _ as => as.attach.flatMap fun ⟨a, _⟩ => a.names
  | .modular _ a b k => a.names ++ b.names ++ k.names
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

/-- Whether an effect occurs in the expression: an `++` or `−−`, an
assignment, or a call (a cast `uint8(e)` is not one). -/
def RawExpr.hasIncDec : RawExpr → Bool :=
  RawExpr.any fun
    | .incDec .. | .named .. | .assign .. | .opAssign .. => true
    | .call f _ => (castTy? f).isNone && f != bytesLitName && (bytesTy? f).isNone
    | _ => false

/-- `f({q: b, p: a})`, a call of a function `funs` declares with named
arguments: put in its parameters' order, `f(a, b)`, as solkey's parser
does.  Any other `T({…})` is left to `hoist`, a struct's constructor. -/
def RawExpr.orderNamed (funs : List (Name × FunDecl)) : RawExpr → Except String RawExpr :=
  RawExpr.mapM fun
    | .call f as =>
      if funs.any (·.1 == f) then pure (.call f as)
      else if let some op := ModOp.ofName? f then
        match as with
        | [a, b, k] => pure (.modular op a b k)
        | _ => throw s!"{f} takes three uint arguments"
      else pure (.call f as)
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
  RawExpr.any fun | .name y | .call y _ => y == x | _ => false

/-- `e` with the names `ρ` maps renamed (a callee's locals, made fresh). -/
def RawExpr.rename (ρ : List (String × String)) (e : RawExpr) : RawExpr :=
  Id.run <| e.mapM fun
    | .name x => .name ((lookupBy x ρ).getD x)
    -- a call through a local of a function type (`fnDispatch`)
    | .call g as => .call ((lookupBy g ρ).getD g) as
    | e => e

/-- A quantified clause with the names of `ρ` renamed, but not below a
binder of the same name (its own local). -/
def RawInv.rename (ρ : List (String × String)) : RawInv → RawInv
  | .expr e => .expr (e.rename ρ)
  | .imp a c => .imp (a.rename ρ) (c.rename ρ)
  | .all p x b => .all p x (RawInv.rename (ρ.filter (·.1 != x)) b)

/-- A loop's quantified clauses renamed by `ρ` (`RawInv.rename`); other
statements as they are. -/
def RawStmt.renameQInv (ρ : List (String × String)) : RawStmt → RawStmt
  | .whileLoop a c b => .whileLoop { a with qinv := a.qinv.map (RawInv.rename ρ) } c b
  | .doWhile a b c => .doWhile { a with qinv := a.qinv.map (RawInv.rename ρ) } b c
  | .loop a c b => .loop { a with qinv := a.qinv.map (RawInv.rename ρ) } c b
  | .forLoop a i c u b => .forLoop { a with qinv := a.qinv.map (RawInv.rename ρ) } i c u b
  | s => s

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
  | .assign l r | .assignPush l r | .opAssign _ l r | .pushOpAssign _ l r | .assignIncDec l _ r => [l, r]
  | .decl _ _ i | .declStorage _ _ i | .declMemory _ _ i | .ret i => i.toList
  | .declStoragePush _ _ b | .declPush _ _ b | .delete b | .incDec _ b | .pushIncDec _ b | .require b | .assert b
  | .ite b _ _ => [b]
  | .call f as => f :: as
  | .eval as => as
  | .tryCall r _ as .. => r :: as
  | .send none x r a _ => [x, r, a]
  | .send (some _) _ r a _ => [r, a]
  | .tupleDecl _ r => [r]
  | .tupleAssign ts r => ts.filterMap id ++ [r]
  | .revert | .assumeFalse | .unchecked _ | .checked .. | .block _ | .brk | .cont | .hole => []
  | .whileLoop a c _ | .doWhile a _ c | .loop a c _ => a.exprs ++ [c]
  | .forLoop a _ c _ _ => a.exprs ++ c.toList

/-- A statement's blocks: an `if`'s branches, an `unchecked` block's body, a
loop's body (a `for`'s initialisation, body and update). -/
def RawStmt.blocks : RawStmt → List (List RawStmt)
  | .ite _ t e => [t, e]
  | .unchecked b | .checked _ b | .block b => [b]
  | .tryCall _ _ _ _ ok err _ pnc other => [ok, err, pnc, other]
  | .whileLoop _ _ b | .doWhile _ b _ | .loop _ _ b => [b]
  | .forLoop _ i _ u b => [i, b, u]
  | _ => []

/-- A loop's specification with its expressions rewritten by `f`; its
quantified clauses are left as they are, renamed only by `RawInv.rename`,
which knows their binders. -/
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
  | .pushOpAssign op b r => return .pushOpAssign op (← f b) (← f r)
  | .assignIncDec l op r => return .assignIncDec (← f l) op (← f r)
  | .decl T x i => return .decl T x (← i.mapM f)
  | .declStorage T x i => return .declStorage T x (← i.mapM f)
  | .declMemory T x i => return .declMemory T x (← i.mapM f)
  | .ret i => return .ret (← i.mapM f)
  | .declStoragePush T x b => return .declStoragePush T x (← f b)
  | .declPush T x b => return .declPush T x (← f b)
  | .delete b => return .delete (← f b)
  | .incDec op b => return .incDec op (← f b)
  | .pushIncDec op b => return .pushIncDec op (← f b)
  | .require b => return .require (← f b)
  | .assert b => return .assert (← f b)
  | .ite c t e => return .ite (← f c) t e
  | .call g as => return .call (← f g) (← as.mapM f)
  | .eval as => return .eval (← as.mapM f)
  | .revert => pure .revert
  | .assumeFalse => pure .assumeFalse
  | .unchecked b => pure (.unchecked b)
  | .checked o b => pure (.checked o b)
  | .tryCall r g as rets ok err code pnc other =>
    return .tryCall (← f r) g (← as.mapM f) rets ok err code pnc other
  | .send T x r a g => return .send T (← f x) (← f r) (← f a) g
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
  | .decl _ x _ | .declStorage _ x _ | .declMemory _ x _ | .declStoragePush _ x _
  | .declPush _ x _ => some x
  | .send (some _) (.name x) _ _ _ => some x
  | _ => none

/-- The names a statement binds in its blocks: a `try`'s return locals and
`Panic` code; and the variables a tuple declaration declares in its own. -/
def RawStmt.binds : RawStmt → List String
  | .tryCall _ _ _ rets _ _ code _ _ => rets.map (·.2) ++ code.toList
  | .tupleDecl vs _ => vs.filterMap (·.map (·.2))
  | _ => []

/-- Whether `p` holds of the statement or of one in its blocks, at any depth. -/
partial def RawStmt.anyDeep (p : RawStmt → Bool) (s : RawStmt) : Bool :=
  p s || s.blocks.any (·.any (RawStmt.anyDeep p))

/-- `f` of the statement, then of each one in its blocks, at any depth. -/
partial def RawStmt.flatMapDeep {α : Type} (f : RawStmt → List α) (s : RawStmt) : List α :=
  f s ++ s.blocks.flatMap (·.flatMap (RawStmt.flatMapDeep f))

/-- Whether a `return` occurs in the statement. -/
def RawStmt.hasReturn (s : RawStmt) : Bool :=
  s.anyDeep (· matches .ret _)

/-- Whether the name `x` occurs in the statement, read, written or declared. -/
def RawStmt.mentions (x : String) (s : RawStmt) : Bool :=
  s.anyDeep fun s => s.declared? == some x || s.binds.contains x || s.exprs.any (·.mentions x)

/-- The names a raw statement reads (a function's name is not one). -/
def RawStmt.names (s : RawStmt) : List String :=
  s.flatMapDeep fun s =>
    let es := match s with
      | .call (.name _) as => as
      | s => s.exprs
    es.flatMap RawExpr.names

def RawStmt.namesList (ss : List RawStmt) : List String :=
  ss.flatMap RawStmt.names

/-- The names a raw statement declares, in either branch of an `if`. -/
def RawStmt.decls (s : RawStmt) : List String :=
  s.flatMapDeep fun s => s.declared?.toList ++ s.binds

def RawStmt.declsList (ss : List RawStmt) : List String :=
  ss.flatMap RawStmt.decls

/-- The largest index among the fresh variables a raw statement writes. -/
def RawStmt.maxIdx [FreshNames] (s : RawStmt) : Nat :=
  (s.flatMapDeep fun s =>
    RawExpr.maxIdxs s.exprs :: (s.declared?.toList ++ s.binds).map fun x => (Var.ofName x).idx).foldl
    max 0

def RawStmt.maxIdxs [FreshNames] (ss : List RawStmt) : Nat :=
  ss.foldl (fun n s => max n s.maxIdx) 0

/-! ### Block locals, renamed apart

The elaborator writes a raw block, a `for` loop's initialisation,
`unchecked { … }` and a modifier's `_;` flat into the block around them, so
their locals stay in scope (hidden, `SProg.chain`) until the scope that
holds them ends (a branch, a loop's body, a call's body, the program).  A
local of such a block whose name is declared again later in that scope is
renamed apart first, `x` to `x_1` (KeY's `VariableNamer` spelling, the least
index naming nothing in the program): Solidity's scope ends at the block, so
no reader after it sees the change, and no local of the program shadows
another (`docs/intrinsic.md`, M2–M3 review). -/

/-- A statement with the blocks it holds rewritten by `f`, its own
expressions as they are. -/
def RawStmt.mapBlocks (f : List RawStmt → List RawStmt) : RawStmt → RawStmt
  | .ite c t e => .ite c (f t) (f e)
  | .unchecked b => .unchecked (f b)
  | .checked o b => .checked o (f b)
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
  ((Id.run (s.mapExprsM (pure ∘ RawExpr.rename [(x, y)]))).renameQInv [(x, y)]).mapBlocks
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
  | .declPush T z b => .declPush T (if z == x then y else z) b
  | .send (some T) (.name z) r a g => .send (some T) (.name (if z == x then y else z)) r a g
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
that holds it.  A `flat` block's own local named in `later` is
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
clauses are scopes of their own, so nothing after them is `later`. -/
partial def freshenStmt (live later : List String) : RawStmt → FreshenM RawStmt
  | .block b => do pure (.block (← freshenList true live later b))
  | .unchecked b => do pure (.unchecked (← freshenList true live later b))
  | .checked o b => do pure (.checked o (← freshenList true live later b))
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

/-! ### Recursion

A function is recursive when its body reaches a call of itself, through the
bodies (and modifiers) of the functions it calls.  A call of a recursive
function is `Stmt.callRec`: its body elaborated once per frame, lazily, in a
frame whose names every frame shares (`ElabScope.recs`). -/

/-- The functions an expression calls, by name. -/
partial def RawExpr.callees (e : RawExpr) : List String :=
  match e with
  | .call g as => g :: as.flatMap RawExpr.callees
  | .named g _ as => g :: as.flatMap RawExpr.callees
  | .field a _ | .unop _ a | .incDec _ a | .newArr _ a => a.callees
  | .index a b | .binop _ a b | .assign a b | .opAssign _ a b => a.callees ++ b.callees
  | .ternary c a b => c.callees ++ a.callees ++ b.callees
  | .modular _ a b k => a.callees ++ b.callees ++ k.callees
  | .tuple as => as.flatMap RawExpr.callees
  | .num _ | .name _ | .bool _ | .env _ => []

/-- The functions a block calls, at any depth: a statement `g(a);` too. -/
def RawStmt.calleesList (ss : List RawStmt) : List String :=
  ss.flatMap (RawStmt.flatMapDeep fun s =>
    (match s with | .call (.name g) _ => [g] | _ => []) ++ s.exprs.flatMap RawExpr.callees)

/-- The functions a function's body and its modifiers call. -/
def FunDecl.callees (d : FunDecl) : List String :=
  RawStmt.calleesList d.body ++
    d.mods.flatMap fun m => RawStmt.calleesList m.body ++ m.args.flatMap RawExpr.callees

/-- The functions of `funs` reachable from `f` by one call or more, a
function's calls as `callees` lists them. -/
def reachableBy (callees : FunDecl → List String) (funs : List (Name × FunDecl)) (f : String) :
    List String := Id.run do
  let mut seen : List String := []
  let mut todo : List String := ((lookupBy f funs).map callees).getD []
  for _ in [0:funs.length + 1] do
    let next := todo.filter (fun g => !seen.contains g && (lookupBy g funs).isSome)
    if next.isEmpty then break
    seen := seen ++ next.eraseDups
    todo := next.flatMap fun g => ((lookupBy g funs).map callees).getD []
  return seen

/-- The functions of `funs` reachable from `f` by one call or more. -/
def reachable (funs : List (Name × FunDecl)) (f : String) : List String :=
  reachableBy FunDecl.callees funs f

/-- Whether `f` calls itself, directly or through other functions of `funs`. -/
def isRecursive (funs : List (Name × FunDecl)) (f : String) : Bool :=
  (reachable funs f).contains f

/-- The functions mutually recursive with `f` (`f` among them, if recursive). -/
def recPartners (funs : List (Name × FunDecl)) (f : String) : List String :=
  (reachable funs f).filter fun g => (reachable funs g).contains f

/-- A frame of a recursive call's unrolling, its contract forgotten
(`ElabScope` does not know it): the body below, behind its thunk. -/
structure RecThunk where
  ctr : Contract
  frame : Ctx
  thunk : Unit → Prog ctr frame frame

instance {C : Contract} {F : Ctx} : Inhabited (Unit → Prog C F F) := ⟨fun _ => Prog.recBase⟩

private unsafe def RecThunk.getImpl (C : Contract) (F : Ctx) (r : RecThunk) :
    Unit → Prog C F F :=
  unsafeCast r.thunk

/-- The thunk at the elaborator's contract, which is the one it was made at
(the elaborator elaborates one contract; the kernel checks what is quoted). -/
@[implemented_by RecThunk.getImpl]
opaque RecThunk.get (C : Contract) (F : Ctx) (r : RecThunk) : Unit → Prog C F F

/-- A recursive function whose body is being elaborated, at one frame of its
unrolling: its parameters' and return variables' names, which every frame
shares, the frame's context, how many frames are left below, and the body of
the frame below (`Stmt.callRec`). -/
structure RecFrame where
  name : String
  params : List Var
  rets : List Var
  depth : Nat
  below : RecThunk

/-- The elaborator's locals in scope as a named context: `old` is a
specification's storage snapshot.  A name is read as the file's
`FreshNames` spells it (`acc` may be `sp1`). -/
def ECtx.toNCtx [FreshNames] (Γ : ECtx) : NCtx :=
  Γ.filterMap fun (x, t) => (Var.ofName x, ·) <$> match t with
    | .val p _ => some (.val p)
    | .alias R => some (.alias R)
    | .mem R => some (.mem R)
    | .store => some .old
    | .kint => some .kint
    | .shape _ => none

/-! ### Named contexts and blocks -/

/-- The type of the newest local named `x`. -/
def NCtx.lookupTy (x : Var) : NCtx → Option LTy
  | [] => none
  | (y, t) :: Γ => if y = x then some t else NCtx.lookupTy x Γ

/-- The position of the newest local named `x`, of type `t`
(`NCtx.find`, with its errors). -/
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

/-- A statement inside `checked { … }` or `ignoringOverflow { … }`: its
guard's statement first, the programs it holds guarded (`Stmt.guard`,
`Stmt.withOF`). -/
def SStmt.withOF (o : OFMode) (s : SStmt C) : SProg C :=
  match s.s.guard with
  | none => [⟨s.Γ, s.Γ', s.s.withOF o⟩]
  | some g => [.of s.Γ (o.guardStmt g), ⟨s.Γ, s.Γ', s.s.withOF o⟩]

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
  | _, .keccak b _ => b.vars ns
  | _, .modular _ a b k => a.vars ns ++ b.vars ns ++ k.vars ns

end

/-- The arguments of a call are separated: no argument that is not simple
reads a parameter bound before it.  Inlined, the parameters are bound one
after another (KeY's `expand_function_body`), and an argument captured
before the call (`functionCallArgCapture`) is read before any of them; the
two agree on a separated call. -/
def Args.separated {Γ : Ctx} (ns : List Var) : {ps : Ctx} → Args C Γ ps → Bool
  | _, .nil => true
  | _, .snoc as _ _ e =>
    as.separated ns && (e.isSimple || (e.vars ns).all fun y => !as.names.contains y)
  | _, .snocStorage as _ _ e =>
    as.separated ns && (e.vars ns).all fun y => !as.names.contains y
  | _, .snocMemory as _ _ e =>
    as.separated ns && (e.vars ns).all fun y => !as.names.contains y

mutual
/-- A memory path that indexes nothing: a local and its members, which a
read cannot revert on when the local is set (memory has no null and no
mapping); an unset one, which only a hidden binder holds (decision 17'),
reverts. -/
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
    if p.isNumeric then throw s!"the literal {n} is out of the range of {p.toStr}"
    else throw s!"a number where a {p.toStr} is expected"

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
      (lookupBy x C.enums).bind fun ms =>
        -- `type(E).min`, `type(E).max` (the macro's `type(min)`, `type(max)`)
        if m == "type(min)" then (if ms.isEmpty then none else some 0)
        else if m == "type(max)" then (if ms.isEmpty then none else some (ms.length - 1))
        else ms.findIdx? (· == m)
    else none
  | _, _ => none

/-! ### Function values

A function's value is its tag, its position in `C.funs` from `1`
("Function types", `Syntax.lean`); a call through a value is a dispatch over
the functions of its signature (`fnDispatch`). -/

/-- The functions of `C` named as a value somewhere in its code (not as a
callee): only these may be reached through a value taken inside `C`. -/
def fnTaken : List String :=
  let stmts : List RawStmt := C.funs.flatMap (fun (_, d) => d.body ++ d.mods.flatMap (·.body)) ++
    (C.ctor.map (·.body)).getD []
  let es : List RawExpr := C.funs.flatMap (fun (_, d) => d.mods.flatMap (·.args)) ++
    C.inits.map (·.2)
  let ns := RawStmt.namesList stmts ++ es.flatMap RawExpr.names
  (C.funs.map (·.1)).filter ns.contains

/-- Whether the function `d` (its modifiers too) calls through a name that is
not a function: a parameter, a local or a state variable, possibly of a
function type. -/
def callsThroughValue (d : FunDecl) : Bool :=
  let own := d.params.map (·.1) ++ RawStmt.declsList d.body ++ C.vars.map (·.1) ++
    d.mods.flatMap fun m => m.params.map (·.1) ++ RawStmt.declsList m.body
  (FunDecl.callees d).any fun h => own.contains h && !C.funs.any (·.1 == h)

/-- Whether a value of the function `g` may exist: `g` is named as a value
in the contract, or no function declared before it (nor it) calls through a
value (`fnTag` refuses `g`'s value elsewhere). -/
def fnReachable (g : String) : Bool :=
  (fnTaken C).contains g ||
    match C.funs.findIdx? (·.1 == g) with
    | some i => !(C.funs.take (i + 1)).any (callsThroughValue C ·.2)
    | none => false

/-- The tag of the function `g`.  One named as a value only outside `C`'s code
(a `sol{ … }` program) is refused when a function declared before it, or it,
calls through a value: that function's dispatch leaves `g` out
(`fnDispatch`), as `g` is not declared before it. -/
def fnTag (g : String) : Except String (Option Nat) := do
  let some i := C.funs.findIdx? (·.1 == g) | return none
  unless fnReachable C g do
    throw s!"{g} is taken as a value only outside the contract's functions, and a function \
        declared before it calls through a function value: name it as a value in the contract"
  return some (i + 1)

/-- The spelling of a function type at the key `k` of the width table `ws`
(its marker row, `valueRows?`). -/
def fnRow? (ws : List (String × Nat)) (k : String) : Option String :=
  ws.findSome? fun (k', _) =>
    if k'.startsWith (k ++ "#function(") then some (k'.drop (k.length + 1)) else none

/-- The function type of the value local `x`: its marker, recorded after it
(`declareShape`). -/
def localFn? (Γ : ECtx) (x : Name) : Option String := do
  let i ← Γ.findIdx? (·.1 == x)
  let j ← Γ.findIdx? (·.1 == "#" ++ x)
  guard (j < i)
  match Γ[j]? with
  | some (_, .shape ws) => fnRow? ws ""
  | _ => none

/-- The function type of the name `h` (a value local, else a state
variable), as `canonFnTy` reads it. -/
def fnTyOf? (Γ : ECtx) (h : String) : Option String :=
  (match lookupBy h Γ with
    | some (.val ..) => localFn? Γ h
    | some _ => none
    | none => fnRow? C.widths h).map (canonFnTy (C.enums.map fun (e : Name × List Name) => e.1))

/-- The signature of the function `d`, as a function type spelled
(`canonFnTy`); none if a parameter or a return is a reference. -/
def FunDecl.sigTy? (d : FunDecl) : Option String := do
  let comp (k : String) : Ty → Option String
    | .prim p => some ((fnRow? d.widths k).getD (declTyName d.widths k p))
    | .ref _ => none
  let ps ← d.params.mapM fun (n, T) => comp n T
  let rs ← d.rets.mapM fun (n, T) => comp n T
  pure (canonFnTy (C.enums.map fun (e : Name × List Name) => e.1) (fnTyStr ps rs false))

/-- The functions a call through a value in `d` (or its modifiers) may
reach: for a callee whose function type is known (a parameter's, a local's,
a state variable's marker) the functions of that type a value may name
(`fnReachable`); for another (`callValueName`, a call statement through a
member or an element) every function the contract names as a value. -/
def FunDecl.valueCallees (d : FunDecl) : List String :=
  let fns := C.funs.map (·.1)
  let stmts := d.body ++ d.mods.flatMap (·.body)
  let locals : List (String × String) := stmts.flatMap (RawStmt.flatMapDeep fun s =>
    match s with
    | .decl (.named t) x _ => if fnTy? t then [(x, t)] else []
    | _ => [])
  let enums := C.enums.map fun (e : Name × List Name) => e.1
  let typed (ty : String) : List String :=
    C.funs.filterMap fun (g, e) =>
      if FunDecl.sigTy? C e == some (canonFnTy enums ty) && fnReachable C g then some g else none
  let viaStmt := stmts.any fun st => !(RawStmt.flatMapDeep (fun s => match s with
      | .call (.name _) _ => []
      | .call (.field _ m) _ => if ["push", "pop", "transfer"].contains m then [] else [()]
      | .call _ _ => [()]
      | _ => []) st).isEmpty
  let hs := (FunDecl.callees d).filter (!fns.contains ·)
  let some' := hs.flatMap fun h =>
    if h == callValueName then fnTaken C else
    match fnRow? d.widths h, lookupBy h locals, fnRow? C.widths h with
    | some ty, _, _ | none, some ty, _ | none, none, some ty => typed ty
    | none, none, none => []
  (if viaStmt then fnTaken C else []) ++ some'

/-- The functions of `C` reachable from `f`, a call through a value a call of
each function it may reach (`FunDecl.valueCallees`). -/
def reachableC (f : String) : List String :=
  reachableBy (fun d => FunDecl.callees d ++ FunDecl.valueCallees C d) C.funs f

/-- Whether `f` calls itself, through values too (`reachableC`). -/
def isRecursiveC (f : String) : Bool := (reachableC C f).contains f

/-- The functions mutually recursive with `f`, through values too. -/
def recPartnersC (f : String) : List String :=
  (reachableC C f).filter fun g => (reachableC C g).contains f

/-- A function type's component as a value: its primitive type and width. -/
def fnCompTy? (c : String) : Option (PrimTy × Nat) :=
  if fnTy? c then some (.uint, 256) else
  match narrowTy? c, bytesTy? c, PrimTy.ofName? c with
  | some t, _, _ => some t
  | none, some n, _ => some (.uint, 8 * n)
  | none, none, some p => some (p, 256)
  | none, none, none => if (lookupBy c C.enums).isSome then some (.uint, 256) else none

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
    | some .kint => throw s!"{x} is a logical variable (KeY's `int`), not a program value"
    | none =>
      match hr : C.rootType x with
      | some T => pure (.path T (.loc (.root x hr)))
      | none => do
        -- a function as a value: its tag
        match ← fnTag C x with
        | some t => return .val .uint (.simple (← litAt C Γ .uint t))
        | none => throw s!"unknown name {x}"
  | .field e f => do
    if let some i := enumLit? C Γ e f then return .val .uint (.simple (← litAt C Γ .uint i))
    match ← synth Γ e with
    | .path (.ref (.array _)) b =>
      if f == "length" then pure (.val .uint (.len b rfl))
      else throw s!"member access .{f} on an array"
    | .mpath (.ref (.array _)) b =>
      if f == "length" then pure (.val .uint (.mlen b rfl))
      -- `keccak256(b)`, as `hoist` leaves it (`keccakMember`)
      else if f == keccakMember then pure (.val .uint (.keccak b rfl))
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
    | .path (.ref (.mapping kp V)) b => pure (.path V (.loc (.index .map b (← check Γ kp k))))
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
    | false => throw s!"operator {BinOp.sym op} does not take {p.toStr}"
  | .ternary c a b => do
    -- two literals: an `int` where one is negative (`c ? -1 : -127`, `mobileTy`)
    if let (some u, some v) := (a.litVal?, b.litVal?) then
      let p : PrimTy := if u < 0 || v < 0 then .int else .uint
      return .val p (.ternary (← check Γ .bool c) (← check Γ p a) (← check Γ p b))
    let t ← if a.isLit then synth Γ b else synth Γ a
    let some ⟨p, _⟩ := t.toVal? | throw "a conditional of reference type"
    pure (.val p (.ternary (← check Γ .bool c) (← check Γ p a) (← check Γ p b)))
  | .unop op a => do
    let t ← synth Γ a
    let some ⟨p, v⟩ := t.toVal? | throw s!"{a.toStr}: an operand of reference type {t.ty}"
    match h : op.accepts p with
    | true => pure (.val _ (.unop op h rfl v))
    | false => throw s!"operator {UnOp.sym op} does not take {p.toStr}"
  | .incDec .. => throw "`++` or `−−` under a short-circuit operator or in a conditional's branch"
  | .assign .. | .opAssign .. =>
    throw "an assignment inside an expression in a conditional's branch"
  | .newArr .. => throw "`new` stands only on the right of `=`"
  | .modular op a b k => do
    let m ← check Γ .uint k
    if let .simple (.lit n _) := m then
      if n == 0 then throw s!"{op.toStr}: arithmetic modulo zero"
    pure (.val .uint (.modular op (← check Γ .uint a) (← check Γ .uint b) m))
  | .call f _ => throw s!"the call {f}(…) under a short-circuit operator or in a conditional's branch"
  | .named f .. => throw s!"the constructor {f}(\{…}) under a short-circuit operator or in a conditional's branch"
  | .env k => pure (.val .uint (.simple (.env k rfl)))
  | .tuple _ => throw "a tuple is the right-hand side of a tuple assignment or of a `return`"
termination_by e => (sizeOf e, 0)

/-- `e` checked at `p` through its synthesised type. -/
def checkVia (Γ : NCtx) (p : PrimTy) (e : RawExpr) : Except String (Val C Γ.ctx p) := do
  let some ⟨q, v⟩ := (← synth Γ e).toVal? |
    throw s!"a storage reference where a {p.toStr} is expected"
  if h : q = p then pure (h ▸ v) else throw s!"a {q.toStr} where a {p.toStr} is expected"
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

/-- A storage-copy source, retaining a compatible fixed-array shape change
as one intrinsic source rather than expanding it into element writes. -/
def checkStorageCopy (Γ : NCtx) (R : RefTy) (e : RawExpr) : Except String (Src C Γ.ctx (.ref R)) := do
  match ← synth C Γ e with
  | .path T p =>
    if ht : T = .ref R then
      match hm : (Ty.ref R).mapFree with
      | true => pure (.copy (ht ▸ p) hm)
      | false => throw "a storage copy of a type that holds a mapping"
    else match T, p with
      | .ref (.fixed E n), p =>
        match hm : E.mapFree with
        | false => throw "a storage copy of a type that holds a mapping"
        | true =>
          match R with
          | .array E' =>
            if he : E = E' then
              if hb : n < 2 ^ 256 then
                pure (he ▸ Src.fixedCopy p (.dynamic hb) hm)
              else throw "a fixed-array length exceeds the dynamic-array bound"
            else throw "an array copy changes its element type"
          | .fixed E' m =>
            if he : E = E' then
              if hf : n ≤ m then pure (he ▸ Src.fixedCopy p (.fixed m hf) hm)
              else throw "a fixed-array copy would truncate source elements"
            else throw "an array copy changes its element type"
          | _ => throw s!"{e.toStr}: incompatible storage-copy shapes {T} and {Ty.ref R}"
      | _, _ => throw s!"{e.toStr}: a storage reference to a {T} where a {Ty.ref R} is expected"
  | _ => throw "a value where a storage reference is expected"

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

/-- The typed array `y = b.push();` grows. Receiver capture belongs to the
calculus so its named rule remains visible in a derivation. -/
def elabPrimPush (Γ : NCtx) (p : PrimTy) (b : RawExpr) :
    Except String (SPath C Γ.ctx (.array (.prim p))) :=
  checkPath C Γ (.array (.prim p)) b

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
  /-- Names supplied by imported source, including fresh-shaped user locals
  such as `se1`. They are mutable values, never written-out captures. -/
  mutableFreshNames : List String := []
  /-- Inside `checked { … }` or `ignoringOverflow { … }`: a narrow type's
  check is the mode's guard statement (`narrowCheck`). -/
  overflow : Option OFMode := none
  /-- Inside `unchecked { … }`: signed `-` and `/` wrap (`narrowWrapNode`);
  an inlined callee's body is checked again. -/
  unchecked : Bool := false
  /-- Inside the body of a function called externally by the contract itself
  (`this.f()`, `trySelfBody`): `msg.sender` is `address(this)` and
  `msg.value` is `0` (`RawStmt.selfFrame`), in its inlined calls too. -/
  selfFrame : Bool := false
  /-- What `msg.value` reads in a self-call's frame (`RawExpr.selfFrame`):
  `0` for a `try`; in the calls a `receive` run by a value call to the
  contract inlines, a name no frame has, so that a callee reading it is not
  run (`receiveSelfBody`). -/
  selfValue : RawExpr := .num 0
  /-- The recursive functions whose bodies are being elaborated, innermost
  first: a call of one is the frame below (`elabCallRet`). -/
  recs : List RecFrame := []

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

/-- Record the narrow positions of the reference local `x` (`LocalTy.shape`). -/
def declareShape (x : Name) (ws : List (String × Nat)) : ElabM Unit :=
  modify fun (Γ, k) => (shapeEntry x ws ++ Γ, k)

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

/-- The narrow positions of the reference local `x` (`LocalTy.shape`). -/
def localShape (Γ : ECtx) (x : Name) : List (String × Nat) :=
  match lookupBy ("#" ++ x) Γ with
  | some (.shape ws) => ws
  | _ => []

/-- Where the widths of the place `e` are kept: a width table, `e`'s key in
it, and `e`'s type.  A state variable's table is `Contract.widths`
(`values[i]` is `values[]`), a reference local's its shape (`m[i]` is `[]`,
`localShape`), a struct member's its struct's (`structWidths`: `p.xs[i]` is
`xs[]` of `Packed`).  A local shadows a state variable. -/
def widthPath? (Γ : ECtx) : RawExpr → Option (List (String × Nat) × String × Ty)
  | .name x =>
    match lookupBy x Γ with
    | some (.alias R) | some (.mem R) => some (localShape Γ x, "", .ref R)
    | some _ => none
    | none => (C.rootType x).map (C.widths, x, ·)
  | .index e _ => do
    let (tb, k, t) ← widthPath? Γ e
    match t with
    | .ref (.array E) | .ref (.fixed E _) | .ref (.mapping _ E) => some (tb, k ++ "[]", E)
    | _ => none
  | .field e f => do
    let (_, _, .ref (.struct s)) ← widthPath? Γ e | none
    let T ← lookupBy f (structDef s)
    pure (structWidths s, f, T)
  | _ => none

/-- The type of a place of primitive type, at its width (`widthPath?`). -/
def pathWidth? (Γ : ECtx) (e : RawExpr) : Option (PrimTy × Nat) := do
  let (tb, k, .prim p) ← widthPath? C Γ e | none
  pure (p, (lookupBy k tb).getD 256)

/-- The narrow positions below the place `e` of reference type, keyed by their
path below it: `small` of `uint8[] small` is `[("[]", 8)]`. -/
def placeShape (Γ : ECtx) (e : RawExpr) : List (String × Nat) :=
  match widthPath? C Γ e with
  | some (tb, k, .ref _) => shapeUnder tb k
  | _ => []

/-- The narrow positions of a value of reference type: a place's
(`placeShape`), a `new`'s type's, a function's return's, a conditional's
first branch's (`narrowWholeAt?` admits one whose branches agree). -/
def exprShape (Γ : ECtx) : RawExpr → List (String × Nat)
  | .newArr T _ => ((elabTyW C T).toOption.map (·.2)).getD []
  | .ternary _ a _ => exprShape Γ a
  | .call f _ =>
    if f == bytesLitName || (encodeBuiltin f && (lookupBy f C.funs).isNone) then dynBytesRows else
    match lookupBy f C.funs with
    | some d => match d.ret with
      | some (r, .ref _) => shapeUnder d.widths r
      | _ => []
    | none => []
  | e => placeShape C Γ e

/-- The narrow positions of `ws`, below a place written `·` (`·[]` 8 bits wide). -/
def shapeStr (ws : List (String × Nat)) : String :=
  if ws.isEmpty then "none" else ", ".intercalate (ws.map fun (k, n) => s!"·{k} {n} bits wide")

/-- A whole use of `e` where `ws` is expected: the narrow positions must agree
(solc converts no reference type to one of another element type). -/
def shapeCheck (Γ : ECtx) (ws : List (String × Nat)) : RawExpr → Except String Unit
  | .ternary _ a b => do shapeCheck Γ ws a; shapeCheck Γ ws b
  | e => do
  let got := exprShape C Γ e
  unless sameShape got ws do
    throw s!"{e.toStr} has narrow positions {shapeStr got} where {shapeStr ws} are expected: \
      solc converts no reference type to one of another element type"

/-- Whether `e` names, whole, a place with a narrow position below it (`small`
of `uint8[] small`, `lists[i]` of `mapping(uint => uint8[]) lists`, a
`uint8[] memory m`). -/
def narrowWhole (Γ : ECtx) (e : RawExpr) : Bool := !(placeShape C Γ e).isEmpty

/-! ### Selectors and external function values

An external function's value is its address and its selector, packed as
solc packs them in the ABI's `bytes24`: `address * 2^32 + selector`
(`docs/semantic-gaps.md`, "Function types").  A selector is the first four
bytes of the Keccak-256 of the function's canonical signature, folded here
as solc folds it (`Keccak.selector`); a signature's types are read off the
width table's markers (`#address`, `#bytes`, `#enum`, `#string`, a function
type's). -/

/-- `2^32`: an external function value's address is above its selector. -/
def selShift : Nat := 2 ^ 32

/-- The canonical ABI name of the type `T` at the key `k` of the width table
`ws`, as a signature writes it: `uint256`, `address`, `bytes4`, `string`,
`uint8[]`, a struct as the tuple of its members.  None for a mapping. -/
partial def abiTyName (ws : List (String × Nat)) (k : String) : Ty → Option String
  | .prim .bool => some "bool"
  | .prim .int => some s!"int{(lookupBy k ws).getD 256}"
  | .prim .uint =>
    if (lookupBy (k ++ "#address") ws).isSome then some "address"
    else if let some n := lookupBy (k ++ "#bytes") ws then some s!"bytes{n}"
    else if (lookupBy (k ++ "#enum") ws).isSome then some "uint8"
    else if (fnRow? ws k).isSome then some "function"
    else some s!"uint{(lookupBy k ws).getD 256}"
  | .ref (.array E) =>
    if lookupBy (k ++ "[]#bytes") ws == some 1 then
      some (if (lookupBy (k ++ "#string") ws).isSome then "string" else "bytes")
    else (abiTyName ws (k ++ "[]") E).map (· ++ "[]")
  | .ref (.fixed E n) => (abiTyName ws (k ++ "[]") E).map (s!"{·}[{n}]")
  | .ref (.struct s) => do
    let ms ← (structDef s).mapM fun (f, T) => abiTyName (structWidths s) f T
    pure s!"({",".intercalate ms})"
  | .ref (.mapping ..) => none

/-- The canonical signature of the function `g` of `C`, `g(uint256,address)`. -/
def fnSignature? (g : String) : Option String := do
  let d ← lookupBy g C.funs
  let ps ← d.params.mapM fun (n, T) => abiTyName d.widths n T
  pure s!"{g}({",".intercalate ps})"

/-- The selector of the function `g` of `C` (`Keccak.selector`). -/
def fnSelector? (g : String) : Option Nat := (fnSignature? C g).map Keccak.selector

/-- The external function type of `g`, as `canonFnTy` spells it. -/
def FunDecl.extTy? (d : FunDecl) : Option String :=
  (FunDecl.sigTy? C d).map fun ty =>
    match fnParts? ty with
    | some (ps, rs, _) => fnTyStr ps rs true
    | none => ty

/-- Whether `r` in `r.g` is a receiver, not a struct: `this`, or a value. -/
def extRecv? (Γ : ECtx) (r : RawExpr) : Option RawExpr :=
  match r with
  | .name "this" | .env .selfAddress => some (.env .selfAddress)
  | _ => match synth C (Γ.toNCtx) r with
    | .ok (.val .uint _) => some r
    | _ => none

/-- `r.g` names the function `g` of `C` at the address `r` (`extRecv?`):
the receiver and `g`. -/
def extMember? (Γ : ECtx) : RawExpr → Option (RawExpr × String)
  | .field r g =>
    if (lookupBy g C.funs).isSome then (extRecv? C Γ r).map (·, g) else none
  | _ => none

/-- The function type of the expression `e`, as `canonFnTy` spells it: a
name's (`fnTyOf?`), a place's marker (a struct member, an element), a
call's return's, a conditional's first branch's, `r.g`'s external type. -/
partial def fnTyOfExpr (Γ : ECtx) (e : RawExpr) : Option String :=
  let canon := canonFnTy (C.enums.map fun (e : Name × List Name) => e.1)
  match e with
  | .name x => fnTyOf? C Γ x
  | .ternary _ a _ => fnTyOfExpr Γ a
  | .call g _ => do
    let d ← lookupBy g C.funs
    let (r, .prim _) ← d.ret | none
    (fnRow? d.widths r).map canon
  | e =>
    match extMember? C Γ e with
    | some (_, g) => (lookupBy g C.funs).bind (FunDecl.extTy? C)
    | none => do
      let (tb, k, .prim _) ← widthPath? C Γ e | none
      (fnRow? tb k).map canon

/-- External function values and their members, as `uint`s: `r.g` (`g` a
function of `C`, `r` an address or `this`) is `r * 2^32 + selector(g)`;
`h.selector` of an external function value `h` is `h % 2^32`, `h.address`
`h / 2^32` (`r.g.selector` the literal, `r.g.address` `r`), the remainder
written `h - h / 2^32 * 2^32`.  The callee of
a call through a value (`callValueName`) is left as written. -/
partial def fnPure (Γ : ECtx) : RawExpr → Except String RawExpr
  | .call f (h :: as) =>
    if f == callValueName then do
      let h' ← match extMember? C Γ h with
        | some (r, g) => do pure (.field (← fnPure Γ r) g)
        | none => fnPure Γ h
      pure (.call f (h' :: (← as.mapM (fnPure Γ))))
    else do pure (.call f ((← fnPure Γ h) :: (← as.mapM (fnPure Γ))))
  | .field e m => do
    if m == "selector" || m == "address" then
      if let some (r, g) := extMember? C Γ e then
        if m == "address" then return ← fnPure Γ r
        let some sel := fnSelector? C g | throw s!"{g}: its signature has a type the ABI does not name"
        return .num sel
      if let some ty := fnTyOfExpr C Γ e then
        if let some (_, _, true) := fnParts? ty then
          let e' ← fnPure Γ e
          -- the selector as `h - h / 2^32 * 2^32`, which the closers read as
          -- linear arithmetic over the quotient (a remainder they do not)
          let a : RawExpr := .binop .div e' (.num selShift)
          return if m == "selector" then .binop .sub e' (.binop .mul a (.num selShift)) else a
    match extMember? C Γ (.field e m) with
    | some (r, g) =>
      let some sel := fnSelector? C g | throw s!"{g}: its signature has a type the ABI does not name"
      pure (.binop .add (.binop .mul (← fnPure Γ r) (.num selShift)) (.num sel))
    | none => do pure (.field (← fnPure Γ e) m)
  | .call f as => do pure (.call f (← as.mapM (fnPure Γ)))
  | .index a b => do pure (.index (← fnPure Γ a) (← fnPure Γ b))
  | .binop op a b => do pure (.binop op (← fnPure Γ a) (← fnPure Γ b))
  | .unop op a => do pure (.unop op (← fnPure Γ a))
  | .ternary c a b => do pure (.ternary (← fnPure Γ c) (← fnPure Γ a) (← fnPure Γ b))
  | .incDec op e => do pure (.incDec op (← fnPure Γ e))
  | .newArr T e => do pure (.newArr T (← fnPure Γ e))
  | .modular op a b k => do pure (.modular op (← fnPure Γ a) (← fnPure Γ b) (← fnPure Γ k))
  | .named f ns as => do pure (.named f ns (← as.mapM (fnPure Γ)))
  | .tuple as => do pure (.tuple (← as.mapM (fnPure Γ)))
  | .assign l r => do pure (.assign l (← fnPure Γ r))
  | .opAssign op l r => do pure (.opAssign op l (← fnPure Γ r))
  | e => pure e

/-- A capture of the reference `e`, declared at `t`, with its narrow positions
(`exprShape`, `LocalTy.shape`). -/
def captureRef (base : String) (t : LocalTy) (e : RawExpr) : ElabM Var := do
  let ws := exprShape C (← ctx) e
  let x ← captureAs C base t
  declareShape (toString x) ws
  pure x

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
  let .ref R ← ElabM.lift ((·.1) <$> elabTyW C T) | throw "`new` of a value type"
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

/-- A reference type. -/
def isRefTy : Ty → Bool
  | .ref _ => true
  | .prim _ => false

mutual
/-- A use of a place `narrowWhole` names other than through an index, a
member (`.length`, `.push`, `.pop`), `delete`, or where its narrow positions
are checked against the target's (a reference local's initializer, a
reference assignment, a function's reference argument: `shapeCheck`).  A
reference type has no width (`uint[]` is `uint8[]`'s `Ty`), so any other use
(an operand of a conditional, a tuple, a named argument) would lose it. -/
partial def narrowWholeUse? (Γ : ECtx) : RawExpr → Option RawExpr
  | e@(.name _) => if narrowWhole C Γ e then some e else none
  | e@(.index b k) =>
    if narrowWhole C Γ e then some e else (narrowBase? Γ b).orElse fun _ => narrowWholeUse? Γ k
  | e@(.field b _) => if narrowWhole C Γ e then some e else narrowBase? Γ b
  -- a function's reference argument: its shape is checked against the
  -- parameter's (`elabCallRet`); a struct constructor's arguments, each
  -- against its member's, by the member writes it is lowered to (`hoist`)
  | .call f as =>
    if (lookupBy f C.funs).isNone && !(C.structFields f).isEmpty then
      as.findSome? (narrowWholeAt? Γ)
    -- a byte string read whole by `keccak256` or the ABI (`abiKind` admits
    -- no other array)
    else if (lookupBy f C.funs).isNone && byteBuiltin f then as.findSome? (narrowBase? Γ)
    else
    let refs : List Bool := ((lookupBy f C.funs).map fun d => d.params.map fun (_, T) => isRefTy T).getD []
    as.zipIdx.findSome? fun (a, i) =>
      if refs.getD i false then narrowWholeAt? Γ a else narrowWholeUse? Γ a
  | .binop _ a b | .assign a b | .opAssign _ a b => (narrowWholeUse? Γ a).orElse fun _ => narrowWholeUse? Γ b
  | .unop _ a | .incDec _ a | .newArr _ a => narrowWholeUse? Γ a
  | .ternary c a b =>
    ((narrowWholeUse? Γ c).orElse fun _ => narrowWholeUse? Γ a).orElse fun _ => narrowWholeUse? Γ b
  | .named f _ as =>
    if (lookupBy f C.funs).isNone && !(C.structFields f).isEmpty then as.findSome? (narrowWholeAt? Γ)
    else as.findSome? (narrowWholeUse? Γ)
  | .tuple as => as.findSome? (narrowWholeUse? Γ)
  | .modular _ a b k => [a, b, k].findSome? (narrowWholeUse? Γ)
  | _ => none

/-- `narrowBase?` at a whole use whose shape is checked (`shapeCheck`): a
conditional's branches too, when their narrow positions agree (solc has no
common type of `uint8[]` and `uint[]`). -/
partial def narrowWholeAt? (Γ : ECtx) : RawExpr → Option RawExpr
  | e@(.ternary c a b) =>
    if sameShape (exprShape C Γ a) (exprShape C Γ b) then
      ((narrowWholeUse? Γ c).orElse fun _ => narrowWholeAt? Γ a).orElse fun _ => narrowWholeAt? Γ b
    else some e
  | e => narrowBase? Γ e

/-- `narrowWholeUse?` of an index's or a member's base, or of a use whose
shape is checked (`shapeCheck`): its own indices only. -/
partial def narrowBase? (Γ : ECtx) : RawExpr → Option RawExpr
  | .index b k => (narrowBase? Γ b).orElse fun _ => narrowWholeUse? Γ k
  | .field b _ => narrowBase? Γ b
  | .name _ => none
  | e => narrowWholeUse? Γ e
end

/-- The smallest integer type holding the literals `u` and `v` (solc's mobile
type, of both): `uintN` when neither is negative, else `intN`. -/
def mobileTy (u v : Int) : PrimTy × Nat :=
  let signed := u < 0 || v < 0
  let fits (n : Nat) (w : Int) : Bool :=
    if signed then -((2 ^ (n - 1) : Nat) : Int) ≤ w && w < ((2 ^ (n - 1) : Nat) : Int)
    else w < ((2 ^ n : Nat) : Int)
  let n := ((List.range 32).map (8 * · + 8)).find? (fun n => fits n u && fits n v) |>.getD 256
  (if signed then .int else .uint, n)

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
  | .unop .toInt _ => some (.int, 256)
  | .unop .toUint _ => some (.uint, 256)
  | .unop _ a => intTyOf Γ a
  | .binop op a b =>
    if !op.isArith then some (.bool, 256)
    else if op matches .pow | .powW | .shl | .shr then
      match a.litVal? with
      | some v => some (if v < 0 then .int else .uint, 256)
      | none => intTyOf Γ a
    else joinIT (intTyOf Γ a) (intTyOf Γ b)
  -- solc's conditional has the common type of its branches' mobile types: a
  -- literal's is the smallest type holding it (`c ? 63 : 255` is a `uint8`,
  -- `c ? x : 300` a `uint16` at `uint8 x`)
  | .ternary _ a b =>
    match a.litVal?, b.litVal? with
    | some u, some v => some (mobileTy u v)
    | some u, none => joinIT (some (mobileTy u u)) (intTyOf Γ b)
    | none, some v => joinIT (intTyOf Γ a) (some (mobileTy v v))
    | none, none => joinIT (intTyOf Γ a) (intTyOf Γ b)
  | .incDec _ e => intTyOf Γ e
  | .call f _ =>
    -- a cast's type, else a declared function's return at its width
    match castTy? f, lookupBy f C.funs with
    | some t, _ => some t
    | none, some d =>
      match d.ret with
      | some (r, .prim p) => some (p, (lookupBy r d.widths).getD 256)
      | _ => some (.uint, 256)
    | none, none => some (.uint, 256)
  | .bool _ => some (.bool, 256)
  -- an element or a member: its declared width (`uint8[] values`, `p.a` of a
  -- `Packed p`)
  | .index e k => (pathWidth? C Γ (.index e k)).orElse fun _ => some (.uint, 256)
  | .field e f => (pathWidth? C Γ (.field e f)).orElse fun _ => some (.uint, 256)
  | _ => some (.uint, 256)

/-- `e`'s width in bits: `intTyOf`'s, `256` for a literal. -/
def widthIn (Γ : ECtx) (e : RawExpr) : Nat := ((intTyOf C Γ e).map (·.2)).getD 256

/-! ### Byte types

A `bytesN` is a `uint` of `8N` bits (`valueRows?`, `Syntax.lean`); what solc
does differently from a `uint8N` is rewritten before the statement is
elaborated (`bytesPure`), where the marker rows tell which positions hold
bytes. -/

/-- The `bytesN` of the value local `x`: its marker, recorded after it
(`declareShape`), not an outer `x`'s. -/
def localBytes? (Γ : ECtx) (x : Name) : Option Nat := do
  let i ← Γ.findIdx? (·.1 == x)
  let j ← Γ.findIdx? (·.1 == "#" ++ x)
  guard (j < i)
  match Γ[j]? with
  | some (_, .shape ws) => lookupBy "#bytes" ws
  | _ => none

/-- Two operands' `bytesN`: a literal takes the other's, the longer wins. -/
def joinBytes : Option Nat → Option Nat → Option Nat
  | none, t => t
  | t, none => t
  | some n, some m => some (max n m)

/-- The `N` of `e` when solc types it `bytesN`: a variable, an element, a
member or a function's return marked so, a conversion `bytesN(…)`, an
element `b[i]` of a `bytesN` (a `bytes1`), and the bitwise operators of
them. -/
partial def bytesOf? (Γ : ECtx) : RawExpr → Option Nat
  | .name x =>
    match lookupBy x Γ with
    | some (.val ..) => localBytes? Γ x
    | some _ => none
    | none => lookupBy (x ++ "#bytes") C.widths
  | e@(.index b _) =>
    if (bytesOf? Γ b).isSome then some 1 else do
      let (tb, k, .prim _) ← widthPath? C Γ e | none
      lookupBy (k ++ "#bytes") tb
  | .field _ "length" => none
  | e@(.field _ _) => do
    let (tb, k, .prim _) ← widthPath? C Γ e | none
    lookupBy (k ++ "#bytes") tb
  | .call f _ =>
    match bytesTy? f with
    | some n => some n
    | none => do
      let d ← lookupBy f C.funs
      let (r, .prim _) ← d.ret | none
      lookupBy (r ++ "#bytes") d.widths
  | .binop op a b =>
    if op matches .band | .bor | .bxor then joinBytes (bytesOf? Γ a) (bytesOf? Γ b)
    else if op matches .shl | .shr then bytesOf? Γ a
    else none
  | .unop .bnot a => bytesOf? Γ a
  | .ternary _ a b => joinBytes (bytesOf? Γ a) (bytesOf? Γ b)
  | .assign l _ | .opAssign _ l _ => bytesOf? Γ l
  | _ => none

/-- The bytes `bs` as a `bytesN`: left-aligned, the rest zero. -/
def bytesAlign (n : Nat) (bs : List Nat) : Except String Nat := do
  if n < bs.length then throw s!"a literal of {bs.length} bytes does not fit bytes{n}"
  pure ((bs ++ List.replicate (n - bs.length) 0).foldl (fun a b => 256 * a + b) 0)

/-- A `bytesM` as a `bytesN`, `M < N`: padded on the right. -/
def widenBytes (m n : Nat) (e : RawExpr) : RawExpr :=
  .binop .shl (.call (tyName .uint (8 * n)) [e]) (.num (8 * (n - m)))

/-- `e`, rewritten from `o`, where a `bytesN` is expected (solc's implicit
conversion): a literal of bytes left-aligned, a shorter `bytesM` padded on
the right; a longer one is refused, as solc refuses it. -/
def toBytesAt (Γ : ECtx) (n : Nat) (o e : RawExpr) : Except String RawExpr := do
  if let some bs := o.bytesLit? then return .num (← bytesAlign n bs)
  match bytesOf? C Γ o with
  | some m =>
    if m == n then pure e
    else if m < n then pure (widenBytes m n e)
    else throw s!"{o.toStr}: a bytes{m} where a bytes{n} is expected: write bytes{n}(…)"
  | none => pure e

/-- `toBytesAt` where the expected type is a `bytesN`, else `e`. -/
def toBytesAt? (Γ : ECtx) (n : Option Nat) (o e : RawExpr) : Except String RawExpr :=
  match n with
  | some n => toBytesAt C Γ n o e
  | none => pure e

/-- The byte `i` of the `bytesN` `b`, a `bytes1`: `b`'s byte counted from the
left, `b >> 8((N-1) -% i)` cut to 8 bits, divided by `i < N ? 1 : 0` so that
an index out of range reverts, as an array's does (`Storage.checkIndex`); a
literal index is checked here. -/
def bytesAt (n : Nat) (b i : RawExpr) : Except String RawExpr :=
  match i.litVal? with
  | some k =>
    -- a literal index: in range, or solc's compile error
    if 0 ≤ k && k < n then
      pure (.call "uint8" [.binop .mod (.binop .shr b (.num (8 * (n - 1 - k.toNat)))) (.num 256)])
    else throw s!"index {k} out of range of a bytes{n}"
  | none =>
    let sh : RawExpr := .binop .mulW (.num 8) (.binop .subW (.num (n - 1)) i)
    pure (.call "uint8" [.binop .div (.binop .mod (.binop .shr b sh) (.num 256))
      (.ternary (.binop .lt i (.num n)) (.num 1) (.num 0))])

/-- The mark of a `bytesN` argument of `abi.encode`/`encodePacked`/
`bytes.concat`, put by `bytesPure` (which rewrites the value to a `uint`)
and read by `hoist`. -/
def abiBytesMark (n : Nat) : String := s!"#abiBytes{n}"

/-- The width a mark names. -/
def abiBytesMark? (f : String) : Option Nat :=
  if f.startsWith "#abiBytes" then (f.drop 9).toNat? else none

/-- Solc's operations on `bytesN` that are not `uint8N`'s, as `uint`
operations (`docs/semantic-gaps.md`, "Bytes and strings"): a conversion, an
index, `.length`, a literal of bytes, an implicit widening; read bottom up,
the types from the expression as written. -/
partial def bytesPure (Γ : ECtx) : RawExpr → Except String RawExpr
  | .call f as => do
    let as' ← as.mapM (bytesPure Γ)
    if let some n := bytesTy? f then
      let ([o], [a]) := (as, as') | throw s!"a conversion {f}(…) takes one argument"
      if let some bs := o.bytesLit? then return .num (← bytesAlign n bs)
      return match bytesOf? C Γ o with
        | some m =>
          if m == n then a
          else if m < n then widenBytes m n a
          else .call (tyName .uint (8 * n)) [.binop .shr a (.num (8 * (m - n)))]
        | none => .call (tyName .uint (8 * n)) [a]
    if dynBytesTy f then
      let [a] := as' | throw s!"a conversion {f}(…) takes one argument"
      return a
    -- an argument of the ABI's that is a `bytesN`: marked, its width lost to
    -- the rewrite (`abiBytesMark`)
    if encodeBuiltin f && (lookupBy f C.funs).isNone then
      return .call f ((as.zip as').map fun (o, a) =>
        match bytesOf? C Γ o with
        | some n => .call (abiBytesMark n) [a]
        | none => a)
    match lookupBy f C.funs with
    | some d =>
      if d.params.length != as.length then return .call f as'
      let as'' ← ((d.params.zip as).zip as').mapM fun (((n, _), o), a) =>
        toBytesAt? C Γ (lookupBy (n ++ "#bytes") d.widths) o a
      pure (.call f as'')
    | none => pure (.call f as')
  | .index b i => do
    let b' ← bytesPure Γ b
    let i' ← bytesPure Γ i
    if let some n := bytesOf? C Γ b then
      if i.hasIncDec then throw s!"{(RawExpr.index b i).toStr}: an index of a bytes{n} with an effect"
      return ← bytesAt n b' i'
    -- a mapping's `bytesN` key; a byte string key hashed (`hashKeyRows`)
    let (key, hashed) := match widthPath? C Γ b with
      | some (tb, k, .ref (.mapping ..)) =>
        (lookupBy (k ++ "{}#bytes") tb, (lookupBy (k ++ "{}#hash") tb).isSome)
      | _ => (none, false)
    if hashed then return .index b' (.call "keccak256" [i'])
    pure (.index b' (← toBytesAt? C Γ key i i'))
  | .field b "length" => do
    if let some n := bytesOf? C Γ b then
      if b.hasIncDec then throw s!"{b.toStr}.length: a bytes{n} with an effect"
      return .num n
    pure (.field (← bytesPure Γ b) "length")
  | .field b f => do pure (.field (← bytesPure Γ b) f)
  | .binop op a b => do
    let a' ← bytesPure Γ a
    let b' ← bytesPure Γ b
    if op matches .lt | .gt | .le | .ge | .eqB | .neB | .band | .bor | .bxor then
      let n := joinBytes (bytesOf? C Γ a) (bytesOf? C Γ b)
      return .binop op (← toBytesAt? C Γ n a a') (← toBytesAt? C Γ n b b')
    pure (.binop op a' b')
  | .unop op a => do pure (.unop op (← bytesPure Γ a))
  | .ternary c a b => do
    let n := joinBytes (bytesOf? C Γ a) (bytesOf? C Γ b)
    pure (.ternary (← bytesPure Γ c) (← toBytesAt? C Γ n a (← bytesPure Γ a))
      (← toBytesAt? C Γ n b (← bytesPure Γ b)))
  | .incDec op e => do pure (.incDec op (← bytesPure Γ e))
  | .newArr T e => do pure (.newArr T (← bytesPure Γ e))
  | .modular op a b k => do
    pure (.modular op (← bytesPure Γ a) (← bytesPure Γ b) (← bytesPure Γ k))
  | .named f ns as => do pure (.named f ns (← as.mapM (bytesPure Γ)))
  | .tuple as => do pure (.tuple (← as.mapM (bytesPure Γ)))
  | .assign l r => do
    pure (.assign (← bytesPure Γ l) (← toBytesAt? C Γ (bytesOf? C Γ l) r (← bytesPure Γ r)))
  | .opAssign op l r => do
    pure (.opAssign op (← bytesPure Γ l) (← toBytesAt? C Γ (bytesOf? C Γ l) r (← bytesPure Γ r)))
  | e => pure e

/-- `bytesPure` of a statement's expressions, and a value written where a
`bytesN` is expected converted to it: a declaration's initializer, an
assignment's right-hand side, a pushed element. -/
def bytesStmt (Γ : ECtx) (s : RawStmt) : Except String RawStmt := do
  let s' ← s.mapExprsM (bytesPure C Γ)
  match s, s' with
  | .decl (.named T) _ (some o), .decl T' x (some r) =>
    pure (.decl T' x (some (← toBytesAt? C Γ (bytesTy? T) o r)))
  | .assign l o, .assign l' r => pure (.assign l' (← toBytesAt? C Γ (bytesOf? C Γ l) o r))
  | .opAssign op l o, .opAssign _ l' r =>
    pure (.opAssign op l' (← toBytesAt? C Γ (bytesOf? C Γ l) o r))
  | .call (.field b "push") [o], .call f [r] =>
    pure (.call f [← toBytesAt? C Γ (bytesOf? C Γ (.index b (.num 0))) o r])
  | _, s' => pure s'

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
def narrowWrapNode (unc : Bool) (Γ : ECtx) (e : RawExpr) : Except String RawExpr := do
  let some (p, n) := intTyOf C Γ e | return e
  -- signed inside `unchecked` (`unc`): `-a` is `0 -% a` on the words; `a / b`
  -- at `intN` is the quotient at `int`, read back at `intN` (`-128 / -1` at
  -- `int8` is `-128`), and at `int` the quotient by `1` where `b` is `-1`,
  -- negated on the words (`type(int).min / -1` is `type(int).min`).  None
  -- of these is narrowed again (`narrowPure` does not revisit its output)
  if unc && p == .int then
    let neg (a : RawExpr) : RawExpr := .call (tyName .int n) [.binop .subW (.num 0) (.call "uint" [a])]
    match e with
    | .unop .neg a => if a.isLit then return e else return neg a
    | .binop .div a b =>
      match b.litVal? with
      | some (-1) => return neg a
      | some _ => return e
      | none =>
        if a.hasIncDec || b.hasIncDec then
          throw s!"{e.toStr} inside `unchecked`: a signed quotient of an operand with an effect"
        if n < 256 then
          return .call (tyName .int n) [.binop .div (.call "int" [a]) (.call "int" [b])]
        let m1 : RawExpr := .unop .neg (.num 1)
        let isM1 : RawExpr := .binop .eqB b m1
        let q : RawExpr := .binop .div a (.ternary isM1 (.unop .neg b) b)
        return .call "int" [.binop .mulW (.call "uint" [q])
          (.ternary isM1 (.num (2 ^ 256 - 1)) (.num 1))]
    | _ => pure ()
  -- signed: the operation on the operands' words, the result read back at
  -- `intN` (`int8(uint(x) +% 1)`, `castCapture`), as solc wraps it; `a **% k`
  -- too, its exponent a `uint` (the words' power is the signed one's, modulo `2^256`)
  if let .binop op a b := e then
    if p == .int && op == .powW then
      if let some v := a.litVal? then
        let (lo, hi) := intRange p n
        unless lo ≤ v && v ≤ hi do throw s!"{v} does not fit {tyName p n}"
      let wa : RawExpr := match a.litVal? with
        | some v => .num (v % ((2 ^ 256 : Nat) : Int)).toNat
        | none => .call "uint" [a]
      return .call (tyName .int n) [.binop .powW wa b]
    if p == .int && (op matches .addW | .subW | .mulW) then
      for l in [a, b] do
        if let some v := l.litVal? then
          let (lo, hi) := intRange p n
          unless lo ≤ v && v ≤ hi do throw s!"{v} does not fit {tyName p n}"
      let word (l : RawExpr) : RawExpr := match l.litVal? with
        | some v => .num (v % ((2 ^ 256 : Nat) : Int)).toNat
        | none => .call "uint" [l]
      -- a negative literal added is subtracted: `x + -1` is `uint(x) -% 1`
      let w := match op, b.litVal? with
        | .addW, some v => if v < 0 then .binop .subW (word a) (.num v.natAbs) else .binop op (word a) (word b)
        | .subW, some v => if v < 0 then .binop .addW (word a) (.num v.natAbs) else .binop op (word a) (word b)
        | _, _ => .binop op (word a) (word b)
      return .call (tyName .int n) [w]
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
partial def narrowPure (unc : Bool) (Γ : ECtx) : RawExpr → Except String RawExpr
  | .binop op a b => do narrowWrapNode C unc Γ (.binop op (← narrowPure unc Γ a) (← narrowPure unc Γ b))
  | .unop op a => do narrowWrapNode C unc Γ (.unop op (← narrowPure unc Γ a))
  | .field e f => do pure (.field (← narrowPure unc Γ e) f)
  | .index e k => do
    -- a narrow mapping key: the index converts to it implicitly, so it fits
    -- (`m[300]` at `mapping(uint8 => …)` is solc's compile error)
    if let some (tb, key, .ref (.mapping kp _)) := widthPath? C Γ e then
      if let some n := lookupBy (key ++ "{}") tb then fitCheck C Γ kp n k
    pure (.index (← narrowPure unc Γ e) (← narrowPure unc Γ k))
  | .ternary c a b => do pure (.ternary (← narrowPure unc Γ c) (← narrowPure unc Γ a) (← narrowPure unc Γ b))
  | .incDec op e => do pure (.incDec op (← narrowPure unc Γ e))
  | .newArr T e => do pure (.newArr T (← narrowPure unc Γ e))
  | .call f as => do pure (.call f (← as.mapM (narrowPure unc Γ)))
  | .modular op a b k => do
    pure (.modular op (← narrowPure unc Γ a) (← narrowPure unc Γ b) (← narrowPure unc Γ k))
  | .named f ns as => do pure (.named f ns (← as.mapM (narrowPure unc Γ)))
  | e => pure e

/-- `require(inTy)` of `e` at `p`'s `n` bits, when `n` is narrow. -/
def narrowCheck (p : PrimTy) (n : Nat) (e : RawExpr) : ElabM (SProg C) := do
  if 256 ≤ n then return []
  let Γ ← nctx
  let c ← checkIn C Γ .bool (inTyCond p n e)
  pure [.of Γ (match (← read).overflow with
    | some o => o.guardStmt c
    | none => .require c)]

/-- The slot `b.push()` appended: `b[b.length - 1]`. -/
def pushedSlot (b : RawExpr) : RawExpr :=
  .index b (.binop .sub (.field b "length") (.num 1))

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

/-- The low `n` bits of the word `w`: `w % 2^n`, as solc truncates. -/
def lowBits (n : Nat) (w : RawExpr) : RawExpr :=
  if 256 ≤ n then w else .binop .mod w (.num (2 ^ n))

/-- The word `w`'s low `n` bits read as an `intN`, in two's complement: the
bits moved by `2^(n-1)`, cut to `n`, moved back and read as an `int`
(`int((w +% 128) % 256 -% 128)` at `int8`: `200` is `-56`). -/
def signedAt (n : Nat) (w : RawExpr) : RawExpr :=
  if 256 ≤ n then .unop .toInt w
  else
    let h : RawExpr := .num (2 ^ (n - 1))
    .unop .toInt (.binop .subW (.binop .mod (.binop .addW w h) (.num (2 ^ n))) h)

/-- A cast `T(e)`, `e`'s captures made: a fresh local of type `T` holding `e`.
A cast keeps the low bits of `e`'s word (`uint(i)` is `i`'s two's
complement, `UnOp.toUint`): a `uintN` takes them as they are (`e % 2^N`), an
`intN` reads them signed (`signedAt`); widening within a sign is the
identity.  A literal must fit `T`. -/
def castCapture (f : String) (e : RawExpr) : ElabM (SProg C × RawExpr) := do
  let some (p, n) := castTy? f | throw s!"{f} is not a type"
  let Γ ← ctx
  let word (q : PrimTy) (e : RawExpr) : RawExpr := if q == .int then .unop .toUint e else e
  let r ← match intTyOf C Γ e, e.litVal? with
    | _, some _ => do ElabM.lift (fitCheck C Γ p n e); pure e
    | some (q, m), none =>
      if q == p && m ≤ n then pure e
      else if p == .int then pure (signedAt n (word q e))
      else pure (lowBits n (word q e))
    | none, none =>
      if 256 ≤ n then pure e
      else if p == .int then
        throw s!"{f}({e.toStr}): a cast of arithmetic on literals alone to a narrow int; write the literal"
      else pure (.binop .mod e (.num (2 ^ n)))
  let Γn ← nctx
  let v ← checkIn C Γn p r
  let x ← captureAs C "se" (.val p n)
  pure ([.of Γn (.declLocal p x (some v))], .name (toString x))

/-- A conversion `E(e)` to an enum of `n` members, `e`'s captures made: a
fresh `uint` holding `e`, then `assert` that it names a member (solc panics,
`0x21`, on one that does not). -/
def enumCapture (n : Nat) (e : RawExpr) : ElabM (SProg C × RawExpr) := do
  let Γ ← nctx
  let v ← checkIn C Γ .uint e
  let x ← captureAs C "se" (.val .uint)
  let e' : RawExpr := .name (toString x)
  let Γ' ← nctx
  let c ← checkIn C Γ' .bool (.binop .lt e' (.num n))
  pure ([.of Γ (.declLocal .uint x (some v)), .of Γ' (.assert c)], e')

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
      let sc ← read
      unless (C.rootType x).isSome || sc.mutableFreshNames.contains x ||
          sc.inlined.any (fun (k₀, k₁) => k₀ ≤ i && i < k₁) do return ([], e)
  let ⟨Γ, t⟩ ← synthM C e
  match e, t with
  | .name _, .path (.ref _) _ | .name _, .mpath (.ref _) _ => return ([], e)
  | _, .path (.ref R) sp =>
    let x ← captureRef C "sp" (.alias R) e
    return ([.of Γ (.declStorage R x (some (.path sp)))], .name (toString x))
  | _, .mpath (.ref R) mp =>
    let x ← captureRef C "mv" (.mem R) e
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
and its body. -/
def Stmt.selfCall? {Γ Γ' : Ctx} (ρ : Ctx) : Stmt C Γ Γ' →
    Option ((ps : Ctx) × (Γf : Ctx) × Args C Γ ps × Prog C (ρ ++ ps) Γf)
  | .call (rs := rs) _ as (.rets _) b => if h : rs = ρ then some ⟨_, _, as, h ▸ b⟩ else none
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
bare.  An `address` and an enum are `uint`s to the model, so packed they
take 32 bytes, not solc's 20 and 1. -/

/-- How `abi.encode` sees a value: its static type. -/
inductive AbiKind where
  | uint (n : Nat) | int (n : Nat) | bool | bytesN (n : Nat)
  /-- `bytes` or `string`. -/
  | dyn
  deriving Inhabited, BEq

/-- The width in bytes a packed value takes. -/
def AbiKind.packedWidth : AbiKind → Nat
  | .uint n | .int n => n / 8
  | .bool => 1
  | .bytesN n => n
  | .dyn => 0

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

/-- `d[o]`, a byte of `d`. -/
def abiByte (d : String) (o : Nat) : RawExpr := .index (.name d) (.num o)

/-- The `m` bytes of `d` from `o` read big-endian into the `uint` local `w`:
`w = d[o]; w = w * 256 + d[o + 1]; …`. -/
def abiAssemble (d w : String) (o m : Nat) : List RawStmt :=
  .decl (.named "uint") w (some (abiByte d o)) ::
    (List.range (m - 1)).map fun j =>
      .assign (.name w) (.binop .add (.binop .mul (.name w) (.num 256)) (abiByte d (o + j + 1)))

/-- `require(d[p] == 0)` for each `p` of `ps`. -/
def abiZeros (d : String) (ps : List Nat) : List RawStmt :=
  ps.map fun p => .require (.binop .eqB (abiByte d p) (.num 0))

/-- `abi.decode` of the word at byte `o` of `d` at the type `T`: its checks
(solc's decoder reverts on a word out of the type's range: a high byte not
zero, or not the sign's, a `bool` above `1`), the bytes it reads into the
local `w`, and its value.  `none` for a type it does not decode.  A narrow
type reads only its own bytes into `w`; the others it compares with `0`
one by one. -/
def abiDecodeAt (T : String) (d w : String) (o : Nat) : Option (List RawStmt × RawExpr) :=
  let unsigned (m : Nat) (v : RawExpr) : List RawStmt × RawExpr :=
    (abiZeros d ((List.range (32 - m)).map (o + ·)) ++ abiAssemble d w (o + 32 - m) m, v)
  if T == "bool" then
    some (abiZeros d ((List.range 31).map (o + ·)) ++
      [.require (.binop .lt (abiByte d (o + 31)) (.num 2))], .binop .eqB (abiByte d (o + 31)) (.num 1))
  else if T == "address" then some (unsigned 20 (.name w))
  else if T == "uint" || T == "uint256" then some (abiAssemble d w o 32, .name w)
  else if T == "int" || T == "int256" then some (abiAssemble d w o 32, .call "int256" [.name w])
  else match narrowTy? T, bytesTy? T with
    | some (.uint, n), _ => some (unsigned (n / 8) (.call T [.name w]))
    | some (.int, n), _ =>
      let m := n / 8
      -- the high bytes are the sign's: `0xff` below a byte of `128` or more
      let sign : RawExpr := .ternary (.binop .ge (abiByte d (o + 32 - m)) (.num 128)) (.num 255) (.num 0)
      some ((List.range (32 - m)).map (fun p => .require (.binop .eqB (abiByte d (o + p)) sign)) ++
        abiAssemble d w (o + 32 - m) m, .call T [.name w])
    | _, some n =>
      some (abiZeros d ((List.range (32 - n)).map (o + n + ·)) ++ abiAssemble d w o n,
        .call T [.name w])
    | _, _ => none

/-- The name of the hidden builtin `abi.decode` of one component is lowered
through: `#abiDecode(d, T, i, n)`, the `i`-th of `n` words of `d` read at `T`. -/
def abiDecodeName : String := "#abiDecode"

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
      if b.hasCall || b.hasIncDec || hasNarrow C (← ctx) b then
        -- the right operand's effects, its calls and its checks run only where
        -- solc evaluates it: `bool se = a; if (se) { se = b; }` for `&&`, the
        -- negated test for `||` (solkey's `logicalAndShortCircuitRhs`)
        let x := toString (← freshCapture "se")
        let test := if op == .and then RawExpr.name x else .unop .not (.name x)
        let Q ← elabStmtsP [.decl (.named "bool") x (some a), .ite test [.assign (.name x) b] []]
        return (P ++ Q, .name x)
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
    if a.hasCall || b.hasCall || a.hasIncDec || b.hasIncDec ||
        hasNarrow C (← ctx) a || hasNarrow C (← ctx) b then
      -- a branch's effects, calls and checks run only in the branch solc
      -- evaluates: `T se; if (c) { se = a; } else { se = b; }`, solkey's
      -- `ternaryToIf` on a capture.  `T` is the type of the branch that is
      -- not a literal, read after its effects are hoisted, which is undone
      let typed := if a.isLit then b else a
      let st ← get
      let (_, typed) ← hoist typed
      let ⟨_, t⟩ ← synthM C typed
      let w := widthIn C (← ctx) typed
      set st
      let some ⟨p, _⟩ := t.toVal? | throw "a conditional of references with effects in a branch"
      let x := toString (← freshCapture "se")
      let Q ← elabStmtsP [.decl (.named (tyName p w)) x none,
        .ite c [.assign (.name x) a] [.assign (.name x) b]]
      return (P ++ Q, .name x)
    let Γ ← nctx
    match synth C Γ a, synth C Γ b with
    | .ok (.path (.ref R) pa), .ok (.path (.ref R') pb) =>
      if hR : R' = R then
        let c ← checkIn C Γ .bool c
        let x ← captureRef C "sp" (.alias R) a
        let ⟨Γ', th, ix⟩ ← afterCapture Γ x (.alias R)
        pure (P ++ [.of Γ (.declStorage R x none),
          .of Γ' (.ite (c.wk th) (.cons (.rebind ix (.path (pa.wk th))) .nil)
            (.cons (.rebind ix (.path ((hR ▸ pb).wk th))) .nil))], .name (toString x))
      else throw "a conditional of two reference types"
    | .ok (.mpath (.ref R) pa), .ok (.mpath (.ref R') pb) =>
      if hR : R' = R then
        let pb := hR ▸ pb
        let c ← checkIn C Γ .bool c
        let x ← captureRef C "mv" (.mem R) a
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
    | false => throw s!"++ or −− at {p.toStr}"
  | .named f ns args => do
    -- the members' order; an effect may not move
    let flds := (C.structFields f).map (·.1)
    if flds.isEmpty then throw s!"{f}(\{…}): {f} is not a struct or a function declared before this one"
    unless ns.length == flds.length && flds.all ns.contains do
      throw s!"{f}(\{…}) names each member of {f} once: {flds}"
    if ns != flds && args.any (·.hasIncDec) then
      throw s!"{f}(\{…}): an argument with an effect, out of the members' order"
    hoist (.call f (flds.map fun g => (lookupBy g (ns.zip args)).getD (.num 0)))
  | .modular op a b k => do
    -- Reject a statically zero modulus before captures can hide the literal.
    if let .ok (.simple (.lit n _)) := check C (← nctx) .uint k then
      if n == 0 then throw s!"{op.toStr}: arithmetic modulo zero"
    -- Legacy solc checks the modulus before evaluating the other arguments.
    -- Save it once: an operand's later effects may change its source.
    let (P, k) ← hoist k
    let (Pc, k) ← captureExpr C k
    let Γ ← nctx
    let guard ← checkIn C Γ .bool (.binop .neB k (.num 0))
    let (Q, args) ← hoistArgs [b, a]
    let [b, a] := args | throw "internal: modular argument capture changed arity"
    pure (P ++ Pc ++ [.of Γ (.require guard)] ++ Q, .modular op a b k)
  | .newArr T n => do
    let (P, n) ← hoist n
    let ⟨R, hR⟩ ← elabNewTy C T
    let (Q, ⟨Γ, se⟩) ← elabSize C n
    let x ← captureRef C "mv" (.mem R) (.newArr T n)
    pure (P ++ Q ++ [.of Γ (.declMem R x (some (.newArr se hR)) rfl
      (MRhs.newArr (C := C) se hR).mapFree)], .name (toString x))
  | .call f args => do
    -- a literal of bytes where a `bytes` or a `string` stands: a fresh memory
    -- array of its bytes (`new bytes(n)`, then each byte written)
    if let some bs := (RawExpr.call f args).bytesLit? then
      let x := toString (← freshCapture "mv")
      let Q ← elabStmtsP (.declMemory (.named "bytes") x (some (.newArr (.named "bytes") (.num bs.length))) ::
        bs.zipIdx.map fun (b, i) => .assign (.index (.name x) (.num i)) (.num b))
      return (Q, .name x)
    let builtin := (← read).funs.all (·.1 != f)
    -- `keccak256(b)`: of a memory `bytes` (a storage one copied first), into
    -- a fresh `bytes32` (`Val.keccak`)
    if builtin && f == "keccak256" then
      let [a] := args | throw "keccak256 takes one argument"
      let (P, a) ← hoist a
      let (Q, b) ← abiMemBytes a
      let y := toString (← freshCapture "se")
      let R ← elabStmtsP [.decl (.named "bytes32") y (some (.field (.name b) keccakMember))]
      return (P ++ Q ++ R, .name y)
    if builtin && (f == "abi.encode" || f == "abi.encodePacked" || f == "string.concat" ||
        f == "bytes.concat") then
      -- a `bytesN` marked (`abiBytesMark`); a literal byte string is not
      -- allocated: its bytes are written in place
      let marks := args.map fun | .call g [_] => abiBytesMark? g | _ => none
      let args := args.map fun a => match a with
        | .call g [x] => if (abiBytesMark? g).isSome then x else a
        | _ => a
      let (P, args') ← hoistArgs (args.map fun a => if a.bytesLit?.isSome then .num 0 else a)
      let args := (args.zip args').map fun (a, a') => if a.bytesLit?.isSome then a else a'
      let (Q, e) ← abiEncode (f == "abi.encode") (f == "string.concat") args marks
      return (P ++ Q, e)
    if builtin && f == "abi.decode" then
      let [b, T] := args | throw "abi.decode(b, (T)) takes a byte string and a type"
      let .name T := T | throw "abi.decode: one value type here; a tuple of them is a declaration's `(T a, U b) = abi.decode(…)`"
      return ← hoist (.call abiDecodeName [b, .name T, .num 0, .num 1])
    if builtin && f == abiDecodeName then
      let [b, .name T, .num i, .num n] := args | throw "internal: #abiDecode's arguments"
      let (P, b) ← hoist b
      let (Q, d) ← abiMemBytes b
      let w := toString (← freshCapture "se")
      let x := toString (← freshCapture "se")
      let some (reads, v) := abiDecodeAt T d w (32 * i) |
        throw s!"abi.decode at {T}: only value types are decoded"
      let R ← elabStmtsP ([.require (.binop .ge (.field (.name d) "length") (.num (32 * n)))] ++
        reads ++ [.decl (.named T) x (some v)])
      return (P ++ Q ++ R, .name x)
    if let some ms := lookupBy f C.enums then
      let [a] := args | throw s!"a conversion {f}(…) takes one argument"
      let (P, a) ← hoist a
      let (Q, e) ← enumCapture C ms.length a
      return (P ++ Q, e)
    if (castTy? f).isSome then
      let [a] := args | throw s!"a cast {f}(…) takes one argument"
      let (P, a) ← hoist a
      let (Q, e) ← castCapture C f a
      return (P ++ Q, e)
    -- a struct's constructor (no function of that name): a fresh memory
    -- object, its members written in order, after the arguments are evaluated
    -- left to right (`T memory mv1; mv1.a = x; mv1.b = y;`)
    let flds := C.structFields f
    if (← read).funs.all (·.1 != f) && !flds.isEmpty then
      let (P, args) ← hoistArgs args
      unless flds.length == args.length do
        throw s!"{f} has {flds.length} members, not {args.length}"
      let x := toString (← freshCapture "mv")
      let Q ← elabStmtsP (.declMemory (.named f) x none ::
        (flds.zip args).map fun ((g, _), a) => .assign (.field (.name x) g) a)
      return (P ++ Q, .name x)
    -- a call through a value that is not a name (`callValue`): its callee's
    -- type, from the callee
    if f == callValueName then
      let h :: rest := args | throw "internal: a call through a value with no callee"
      if let .name g := h then
        if (← read).funs.any (·.1 == g) then return ← hoist (.call g rest)
      let some ty := fnTyOfExpr C (← ctx) h | throw s!"{h.toStr}(…): the callee is not a function value"
      let (P, rest) ← hoistArgs rest
      let some (_, [r], _) := fnParts? ty | throw s!"{h.toStr}(…) returns one value where a value stands"
      let some (p, n) := fnCompTy? C r | throw s!"{h.toStr}(…) returns a {r}, not a value type"
      let Γ ← nctx
      let x ← freshCapture "se"
      let Q ← elabCall f (h :: rest) (some (x, p)) n (resNew := true)
      declare C (toString x) (.val p n)
      declareShape (toString x) (← ElabM.lift (bytesRowsOf C (.named r)))
      return (P ++ [.of Γ (.declLocal p x none)] ++ Q, .name (toString x))
    -- a call through a function value, into a fresh local (`fnDispatch`)
    if (← read).funs.all (·.1 != f) then
      if let some ty := fnTyOf? C (← ctx) f then
        let (P, args) ← hoistArgs args
        let some (_, [r], _) := fnParts? ty | throw s!"{f}(…) returns one value where a value stands"
        let some (p, n) := fnCompTy? C r | throw s!"{f}(…) returns a {r}, not a value type"
        let Γ ← nctx
        let x ← freshCapture "se"
        let Q ← elabCall f args (some (x, p)) n (resNew := true)
        declare C (toString x) (.val p n)
        declareShape (toString x) (← ElabM.lift (bytesRowsOf C (.named r)))
        return (P ++ [.of Γ (.declLocal p x none)] ++ Q, .name (toString x))
    -- a call inside an expression runs before the statement, into a fresh local
    let (P, args) ← hoistCallArgs f args
    let some (_, d) := (← read).funs.find? (·.1 == f) | throw s!"{f} is not a function declared before this one"
    match d.ret with
      | some (r, .prim p) =>
        let n := (lookupBy r d.widths).getD 256
        let Γ ← nctx
        let x ← freshCapture "se"
        let Q ← elabCall f args (some (x, p)) n (resNew := true)
        declare C (toString x) (.val p n)
        declareShape (toString x) (shapeUnder d.widths r)
        pure (P ++ [.of Γ (.declLocal p x none)] ++ Q, .name (toString x))
      | some (r, .ref R) =>
        if d.retStorage then
          let x ← freshCapture "sp"
          let Q ← elabStorageCall f args R fun Γ r =>
            pure (.of ((r, .alias R) :: Γ) (.declStorage R x (some (.path (.alias .here)))))
          declare C (toString x) (.alias R)
          declareShape (toString x) (shapeUnder d.widths r)
          return (P ++ Q, .name (toString x))
        -- `Account memory mv1 = makeAccount();`
        let x ← freshCapture "mv"
        let Q ← elabMemCall f args R fun Γ r hm =>
          pure (.of ((r, .mem R) :: Γ) (.declMem R x (some (.alias (.var .here hm))) rfl hm))
        declare C (toString x) (.mem R)
        declareShape (toString x) (shapeUnder d.widths r)
        pure (P ++ Q, .name (toString x))
      | none =>
        if d.rets.isEmpty then throw s!"{f} returns no value"
        else throw s!"{f} returns {d.rets.length} values, which a tuple assignment takes"
  | .tuple _ => throw "a tuple is the right-hand side of a tuple assignment or of a `return`"
  | .assign l r => do
    -- the right-hand side, then the target (`hoistAssign`); the value is the
    -- one written, held first (solkey's `storageCopyAssignmentValue`:
    -- `pv = e; sp = pv; v = pv;`)
    let (P, r) ← hoist r
    let (Pc, r) ← captureExpr C r
    let Q ← elabStmtsP [.assign l r]
    pure (P ++ Pc ++ Q, r)
  | .opAssign op l r => do
    -- the write, then the target read again (solkey's `localAddAssignmentValue`:
    -- `lv += e; v = lv;`): a target with an effect would run it twice
    if l.hasIncDec then
      throw s!"{(RawExpr.opAssign op l r).toStr}: a compound assignment's value, its target with an effect"
    let Q ← elabStmtsP [.opAssign op l r]
    pure (Q, l)
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

/-- A call's arguments, left to right: one read before a later argument's
effect is captured first, as a binary operator's operand is. -/
partial def hoistArgs : List RawExpr → ElabM (SProg C × List RawExpr)
  | [] => pure ([], [])
  | a :: as => do
    let (P, a) ← hoist a
    let (Pc, a) ← if as.any (·.hasIncDec) then captureExpr C a else pure ([], a)
    let (Q, as) ← hoistArgs as
    pure (P ++ Pc ++ Q, a :: as)

/-- A byte string as a memory local: a memory one bound to a fresh name, a
storage one copied into a fresh memory `bytes` (solc's conversion). -/
partial def abiMemBytes (a : RawExpr) : ElabM (SProg C × String) := do
  if let .name x := a then
    if let .ok (.mpath ..) := synth C (← nctx) a then return ([], x)
  let x := toString (← freshCapture "mv")
  pure (← elabStmtsP [.declMemory (.named "bytes") x (some a)], x)

/-- The kind of an argument of `abi.encode` (`AbiKind`), by its static type. -/
partial def abiKind (a : RawExpr) : ElabM AbiKind := do
  if a.bytesLit?.isSome then return .dyn
  let Γ ← ctx
  match synth C (← nctx) a with
  | .ok (.val .bool _) => pure .bool
  | .ok (.val .int _) => pure (.int (widthIn C Γ a))
  | .ok (.val .uint _) =>
    match bytesOf? C Γ a with
    | some n => pure (.bytesN n)
    | none => pure (.uint (widthIn C Γ a))
  | .ok (.mpath (.ref (.array (.prim .uint))) _) | .ok (.path (.ref (.array (.prim .uint))) _) =>
    if lookupBy "[]#bytes" (placeShape C Γ a) == some 1 then pure .dyn
    else throw s!"{a.toStr}: an array other than `bytes`/`string` is not ABI-encoded here"
  | .ok _ => throw s!"{a.toStr}: a value of this type is not ABI-encoded here"
  | .error e => throw e

/-- `abi.encode(…)` (`std`) or `abi.encodePacked(…)`/`bytes.concat(…)`/
`string.concat(…)` (`strs`: byte strings only) of the hoisted arguments: a
fresh memory `bytes` of solc's layout (`AbiKind`). -/
partial def abiEncode (std strs : Bool) (args : List RawExpr) (marks : List (Option Nat)) :
    ElabM (SProg C × RawExpr) := do
  let mut P : SProg C := []
  -- each argument read once: its word in a fresh `uint` (a literal's known),
  -- a byte string in a memory local with its length (a literal's bytes known)
  let mut parts : List (AbiKind × String × String × Option (List Nat)) := []
  for (a, mark) in args.zip marks do
    let k ← match mark with
      | some n => pure (AbiKind.bytesN n)
      | none => abiKind a
    if strs && k != .dyn then throw "string.concat takes `string`s"
    match k, a.bytesLit? with
    | .dyn, some bs => parts := parts ++ [(k, "", "", some bs)]
    | .dyn, none =>
      let (Q, x) ← abiMemBytes a
      let L := toString (← freshCapture "se")
      let R ← elabStmtsP [.decl (.named "uint") L (some (.field (.name x) "length"))]
      P := P ++ Q ++ R
      parts := parts ++ [(k, x, L, none)]
    | _, _ =>
      match k.litWord? a with
      | some v => parts := parts ++ [(k, "#" ++ toString v, "", none)]
      | none =>
        let w := toString (← freshCapture "se")
        P := P ++ (← elabStmtsP [.decl (.named "uint") w (some (k.word a))])
        parts := parts ++ [(k, w, "", none)]
  let r := toString (← freshCapture "mv")
  let tot := toString (← freshCapture "se")
  let n := parts.length
  let len (L : String) (lit : Option (List Nat)) : RawExpr :=
    match lit with
    | some bs => .num bs.length
    | none => .name L
  let pad : RawExpr → RawExpr
    | .num m => .num ((m + 31) / 32 * 32)
    | e => abiPad e
  let total : RawExpr := parts.foldl (fun acc (k, _, L, lit) =>
      if k == .dyn then
        if std then .binop .add acc ((pad (len L lit)).addN 32) else .binop .add acc (len L lit)
      else if std then acc else acc.addN k.packedWidth)
    (.num (if std then 32 * n else 0))
  let mut S : List RawStmt := [.decl (.named "uint") tot (some total),
    .declMemory (.named "bytes") r (some (.newArr (.named "bytes") (.name tot)))]
  -- `o`: where the next tail (`std`) or the next value (packed) starts
  let o := toString (← freshCapture "se")
  S := S ++ [.decl (.named "uint") o (some (.num (if std then 32 * n else 0)))]
  -- a byte string's bytes at `p`: a literal's written, another's copied
  let bytesAt (p : RawExpr) (x L : String) (lit : Option (List Nat)) : ElabM (List RawStmt) := do
    match lit with
    | some bs =>
      pure (bs.zipIdx.filterMap fun (b, j) =>
        if b == 0 then none else some (.assign (.index (.name r) (p.addN j)) (.num b)))
    | none => pure (abiCopy r x (toString (← freshCapture "se")) L p)
  for ((k, x, L, lit), i) in parts.zipIdx do
    if std then
      if k == .dyn then
        let lenW : List RawStmt := match lit with
          | some bs => abiLitBytes r (.name o) bs.length 32
          | none => abiBytes r (.name o) (.name L) 32
        S := S ++ abiBytes r (.num (32 * i)) (.name o) 32 ++ lenW ++
          (← bytesAt ((RawExpr.name o).addN 32) x L lit) ++
          [.assign (.name o) (.binop .add ((RawExpr.name o).addN 32) (pad (len L lit)))]
      else S := S ++ abiStatic r (32 * i) k x
    else
      if k == .dyn then
        S := S ++ (← bytesAt (.name o) x L lit) ++
          [.assign (.name o) (.binop .add (.name o) (len L lit))]
      else
        S := S ++ abiWrite r (.name o) x k.packedWidth ++
          [.assign (.name o) ((RawExpr.name o).addN k.packedWidth)]
  pure (P ++ (← elabStmtsP S), .name r)

/-- Prepare a reference call in argument order. Storage-to-memory conversion
copies at the argument's evaluation point; every reference's identity and
each scalar read are held before a later argument can change them. Calls
with only value parameters retain the ordinary capture policy. -/
partial def hoistCallArgs (f : String) (args : List RawExpr) :
    ElabM (SProg C × List RawExpr) := do
  let funs := (← read).funs
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
    if T matches .ref _ then ElabM.lift (shapeCheck C (← ctx) (shapeUnder d.widths n) a)
    let (Q, a) ← hoist a
    P := P ++ Q
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
        | some .memory =>
          let rhs ← ElabM.lift (elabMRhs C Γ R a)
          if stable && (rhs matches .alias _) then pure ([], a) else do
          let x ← captureRef C "mv" (.mem R) a
          pure ([.of Γ (.declMem R x (some rhs) rfl rhs.mapFree)], .name (toString x))
        | some .calldata => throw s!"{f}: calldata parameter {n} is not supported"
        | none => throw s!"{f}: reference parameter {n} needs a data location"
    P := P ++ Q
    prepared := prepared ++ [a]
  pure (P, prepared)

/-- **A call through a function value** `h(a)`, `h` of the function type
`ty` (`fnTyOf?`): the arguments that are not pure captured, left to right,
then a dispatch over the functions of `ty`, `if (h == 1) { r = g₁(a); } else
if … else { revert(); }` (`fnTag`): calling an unassigned value is solc's
`Panic(0x51)`, which the model reads as a revert, as it reads an index out
of range's `Panic(0x32)` (`Storage.checkIndex`, the solkey reading).  A function
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
  -- (`FunDecl.sigTy?`), so the dispatch would list none
  if let some c := (ps ++ rs).find? fun c => (fnCompTy? C c).isNone then
    throw s!"{h}(…): a function type with a {c} parameter or return is not modelled \
      (docs/semantic-gaps.md, \"Function types\")"
  let scope := (← read).funs
  let taken := fnTaken C
  let mut cands : List (String × Nat) := []
  for ((g, d), i) in C.funs.zipIdx do
    if FunDecl.sigTy? C d == some ty && fnReachable C g then
      if scope.any (·.1 == g) then cands := cands ++ [(g, i + 1)]
      else if taken.contains g then
        throw s!"{h}(…) may call {g}, which is not declared before this function: \
          declare the functions of type {ty} first"
  let mut pre : List RawStmt := []
  let mut as : List RawExpr := []
  for (a, c) in args.zip ps do
    if a.isPure then as := as ++ [a] else
      let y := toString (← freshCapture "se")
      pre := pre ++ [.decl (.named c) y (some a)]
      as := as ++ [.name y]
  let call (g : String) : RawStmt := match res with
    | some (x, _) => .assign (.name (toString x)) (.call g as)
    | none => .call (.name g) as
  let disp := cands.foldr (fun (g, t) els =>
    [RawStmt.ite (.binop .eqB (.name h) (.num t)) [call g] els]) [RawStmt.revert]
  let (Γ0, _) ← get
  if resNew then
    if let some (x, p) := res then declare C (toString x) (.val p resW)
  let P ← elabBranch (pre ++ disp)
  modify fun (_, k) => (Γ0, k)
  pure P

/-- `try r.g(as) returns (T v) { x = v; } catch { revert(); }`: an external
call whose every failure reverts the caller, as a call outside a `try` does,
its one return landing in `res`; the types of `ps → rs`. -/
partial def extCallStmt (r : RawExpr) (g : String) (as : List RawExpr) (rs : List String)
    (res : Option (Var × PrimTy)) : ElabM RawStmt := do
  let mut rets : List (RawTy × String) := []
  for t in rs do rets := rets ++ [(.named t, toString (← freshCapture "se"))]
  let ok : List RawStmt := match res, rets with
    | some (x, _), [(_, v)] => [.assign (.name (toString x)) (.name v)]
    | _, _ => []
  pure (.tryCall r g as rets ok [.revert] none [.revert] [.revert])

/-- **A call through an external function value** `h(a)`, `h` of the
external function type `ty`: `h` is `address * 2^32 + selector` (`fnPure`),
so the call is an external call to `h / 2^32` (`extCallStmt`), dispatched on
the selector `h - h / 2^32 * 2^32` over the functions of `C` of that type, so that one
to `this` runs the function (`Stmt.tryCall`'s `self`, O8); any other
selector is a call the model names `#selector`, its first argument the
selector, whose response the world chooses as for any external call. -/
partial def extDispatch (h ty : String) (ps rs : List String) (args : List RawExpr)
    (res : Option (Var × PrimTy)) (resW : Nat) (resNew : Bool) : ElabM (SProg C) := do
  unless ps.length == args.length do
    throw s!"{h} takes {ps.length} arguments, not {args.length}"
  if 1 < rs.length then throw s!"{h}(…): an external function value of several returns"
  let a := toString (← freshCapture "se")
  let sl := toString (← freshCapture "se")
  let mut pre : List RawStmt := [.decl (.named "address") a (some (.binop .div (.name h) (.num selShift))),
    .decl (.named "uint") sl
      (some (.binop .sub (.name h) (.binop .mul (.name a) (.num selShift))))]
  let mut as : List RawExpr := []
  for (x, c) in args.zip ps do
    if x.isPure then as := as ++ [x] else
      let y := toString (← freshCapture "se")
      pre := pre ++ [.decl (.named c) y (some x)]
      as := as ++ [.name y]
  let mut cands : List (String × Nat) := []
  for (g, d) in C.funs do
    if FunDecl.extTy? C d == some ty then
      if let some sel := fnSelector? C g then cands := cands ++ [(g, sel)]
  let other ← extCallStmt (.name a) "#selector" (.name sl :: as) rs res
  let mut disp : List RawStmt := [other]
  for (g, sel) in cands.reverse do
    disp := [.ite (.binop .eqB (.name sl) (.num sel)) [← extCallStmt (.name a) g as rs res] disp]
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
      let y := toString (← freshCapture "fv")
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
        if let .mpath (.ref _) _ ← ElabM.lift (synth C Γv a) then
          pure (Src.copyMem (← ElabM.lift (checkMPath C Γv (.ref R) a)))
        else ElabM.lift (checkStorageCopy C Γv R a)
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
    ElabM (SProg C × Option (NCtx × RefTy × Var × Bool) × List (PrimTy × Var × Nat)) := do
  let funs := (← read).funs
  -- a call through a value that is not a name (`callValue`)
  if !ctor && f == callValueName then
    let h :: args := args | throw "internal: a call through a value with no callee"
    if targets then throw s!"{h.toStr}(…): a call through a function value in a tuple assignment"
    return (← callValue h args res resW resNew, none, [])
  -- a call through a function value (`fnDispatch`)
  if !ctor && funs.all (·.1 != f) then
    if let some ty := fnTyOf? C (← ctx) f then
      if targets then throw s!"{f}(…): a call through a function value in a tuple assignment"
      return (← fnDispatch f ty args res resW resNew, none, [])
  let selfFrame := selfFrame || (← read).selfFrame
  -- a call of a recursive function whose body is being elaborated: the frame
  -- below, its names the frame's (`ElabScope.recs`)
  let recs := (← read).recs
  let site := if ctor then none else recs.find? (·.name == f)
  let recursive := !ctor && (site.isSome || isRecursiveC C f)
  -- the callee and the functions its body may call: the constructor (`elabCtor`)
  -- may call every function, a function those declared before it, and a
  -- recursive function those it is mutually recursive with too
  let (d, scope) ← if ctor then pure (C.ctor.getD { params := [], body := [] }, C.funs) else
    let some i := funs.findIdx? (·.1 == f) | throw s!"{f} is not a function declared before this one"
    let d := (funs[i]?.map (·.2)).getD default
    if recursive then
      let j := (C.funs.findIdx? (·.1 == f)).getD 0
      let partners := recPartnersC C f
      pure (d, C.funs.take j ++ (C.funs.drop j).filter (partners.contains ·.1))
    else pure (d, funs.take i)
  -- a recursive function's frame is one context, `rs ++ ps`, at every call:
  -- a call of several returns returns to its targets (`CallRet.rets`)
  if recursive && d.rets.length > 1 && !targets then
    throw s!"{f} is recursive and returns several values: call it in a tuple assignment"
  -- a parameter's or return variable's name: fresh, or the recursive frame's
  let pickName (base : String) (frameNames : RecFrame → List Var) (j : Nat) : ElabM Var :=
    match site with
    | some rf => match (frameNames rf)[j]? with
      | some x => pure x
      | none => throw s!"internal: {f}'s recursive frame has no name {j}"
    | none => freshCapture base
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
  let mut pj := 0
  let mut pnames : List Var := []
  for ((n, T), a) in d.params.zip args do
    match T with
    | .prim p =>
      if (lookupBy n d.paramLocs).isSome then
        throw s!"{f}: data location on value parameter {n}"
      let w := (lookupBy n d.widths).getD 256
      ElabM.lift (fitCheck C Γ p w a)
      let e ← checkIn C Γn p a
      let x ← pickName "se" (·.params) pj
      pnames := pnames ++ [x]
      targs := ⟨_, targs.2.snoc p x e⟩
      ρ := (n, toString x) :: ρ
      Γp := shapeEntry (toString x) (shapeUnder d.widths n) ++ (toString x, .val p w) :: Γp
    | .ref R =>
      match lookupBy n d.paramLocs with
      | some .storage =>
        ElabM.lift (shapeCheck C Γ (shapeUnder d.widths n) a)
        let e ← ElabM.lift (checkPath C Γn (.ref R) a)
        let x ← pickName "sp" (·.params) pj
        pnames := pnames ++ [x]
        targs := ⟨_, targs.2.snocStorage R x e⟩
        ρ := (n, toString x) :: ρ
        Γp := shapeEntry (toString x) (shapeUnder d.widths n) ++ (toString x, .alias R) :: Γp
      | some .memory =>
        ElabM.lift (shapeCheck C Γ (shapeUnder d.widths n) a)
        let e ← ElabM.lift (checkMPath C Γn (.ref R) a)
        let x ← pickName "mv" (·.params) pj
        pnames := pnames ++ [x]
        targs := ⟨_, targs.2.snocMemory R x e⟩
        ρ := (n, toString x) :: ρ
        Γp := shapeEntry (toString x) (shapeUnder d.widths n) ++ (toString x, .mem R) :: Γp
      | some .calldata => throw s!"{f}: calldata parameter {n} is not supported"
      | none => throw s!"{f}: reference parameter {n} needs a data location"
    pj := pj + 1
  let mut mret : Option (RefTy × Var × Bool) := none
  let mut mrets : List (PrimTy × Var × Nat) := []
  let mut Γr : ECtx := []
  let kind ← match d.rets, res with
    -- a void call with targets (a void function's obligation, `f(x̄)@C;`)
    -- is a `FunctionBodyStatement` all the same
    | [], none => pure (if targets then RetKind.rets [] else RetKind.none)
    | [], some _ => throw s!"{f} returns no value"
    | [(n, .ref R)], none => do
      if targets then throw s!"{f} returns a {Ty.ref R}, which a tuple assignment does not take"
      if d.retMem && d.retStorage then throw s!"{f}: its return has two data locations"
      if d.retStorage then
        let r ← freshCapture "sp"
        ρ := (n, toString r) :: ρ
        Γr := shapeEntry (toString r) (shapeUnder d.widths n) ++ [(toString r, .alias R)]
        mret := some ⟨R, r, true⟩
        pure (RetKind.storage R r)
      else
        unless d.retMem do throw s!"{f}: its return of reference type {Ty.ref R} needs `memory` or `storage`"
        let r ← freshCapture "mv"
        ρ := (n, toString r) :: ρ
        Γr := shapeEntry (toString r) (shapeUnder d.widths n) ++ [(toString r, .mem R)]
        mret := some ⟨R, r, false⟩
        pure (RetKind.mem R r)
    | [(_, .ref R)], some (_, q) => throw s!"{f} returns a reference {Ty.ref R}, not a {q.toStr}"
    | [(n, .prim p)], res => do
      if d.retMem then throw s!"{f}: `memory` on its return of value type {p.toStr}"
      if d.retStorage then throw s!"{f}: `storage` on its return of value type {p.toStr}"
      if let some (_, q) := res then
        unless q = p do throw s!"{f} returns a {p.toStr}, not a {q.toStr}"
      let w := (lookupBy n d.widths).getD 256
      if resW < w then throw s!"{f} returns a {tyName p w}, where a {tyName p resW} is expected"
      let r ← pickName "se" (·.rets) 0
      ρ := (n, toString r) :: ρ
      Γr := shapeEntry (toString r) (shapeUnder d.widths n) ++ [(toString r, .val p w)]
      if targets then
        mrets := [(p, r, w)]
        pure (RetKind.rets [(p, r)])
      else pure (RetKind.val p r)
    | rs, some _ => throw s!"{f} returns {rs.length} values, which a tuple assignment takes"
    | rs, none => do
      if d.retMem then throw s!"{f}: `memory` on a return of a function of several returns"
      if d.retStorage then throw s!"{f}: `storage` on a return of a function of several returns"
      -- declared in the caller's context too (`CallRet.rets`): fresh at
      -- every call, a recursive one's too
      for (n, T) in rs do
        let .prim p := T | throw s!"{f}: its return {n} has a reference type"
        let w := (lookupBy n d.widths).getD 256
        let r ← freshCapture "se"
        ρ := (n, toString r) :: ρ
        Γr := shapeEntry (toString r) (shapeUnder d.widths n) ++ (toString r, .val p w) :: Γr
        mrets := mrets ++ [(p, r, w)]
      if targets then pure (RetKind.rets (mrets.map fun (p, r, _) => (p, r))) else pure RetKind.none
  let Γf := Γr ++ Γp
  let rnames : List Var := match kind with
    | .val _ r | .mem _ r | .storage _ r => [r]
    | .rets l => l.map (·.2)
    | .none => []
  -- the body: at a recursive function's call in its own body, the frame
  -- below (`ElabScope.recs`); for a recursive function, its body elaborated
  -- per frame, lazily (`recUnroll`, `Stmt.callRec`); otherwise inlined
  let mut P : SProg C := []
  let mut recBody : Option (Nat × ((F : Ctx) → List Var → ElabM (Unit → Prog C F F))) := none
  if let some rf := site then
    recBody := some (rf.depth, fun F _ =>
      if rf.below.frame == F then pure (rf.below.get C F)
      else throw s!"internal: {f}'s recursive frame has another context")
  else
    let body ← renameStmts ρ d.body
    let body ← lowerLoops (some (d.rets.map fun (n, _) => (lookupBy n ρ).getD n)) body
    let body ← ElabM.lift (lowerReturns (d.rets.map fun (n, _) => (lookupBy n ρ).getD n) body)
    let body ← wrapMods body (d.mods.map fun m => { m with args := m.args.map (·.rename ρ) })
    -- a constructor's initializers: after its parameters are bound, before its
    -- modifiers, in declaration order (solkey's `ExpandFunctionBody`)
    let body := (if ctor then C.inits.map fun (x, e) => RawStmt.assign (.name x) e else []) ++ body
    -- an external call of the contract to itself: its frame's environment
    let selfValue := (← read).selfValue
    let body := if selfFrame then body.map (RawStmt.selfFrame selfValue) else body
    -- a block's locals renamed apart (a modifier's `_;` twice repeats the body's)
    let body ← ElabM.lift (freshenBlocks (C.vars.map (·.1)) (Γf.map (·.1)) body)
    let k₁ := (← get).2
    if recursive then
      recBody := some (recDepth, fun F ns => do
        let sc ← read
        let frame (n : Nat) (bt : Unit → Prog C F F) : Except String (Prog C F F × Nat) := do
          let rf : RecFrame :=
            { name := f, params := pnames, rets := rnames, depth := n, below := ⟨C, F, bt⟩ }
          let sc' : ElabScope :=
            { sc with funs := scope, top := false, selfFrame := selfFrame, unchecked := false,
                      inlined := (k₀, k₁) :: sc.inlined, recs := rf :: sc.recs }
          let (Q, (_, kEnd)) ← ((elabStmtsP body).run sc').run (Γf, k₁)
          let ⟨_, b⟩ ← SProg.chain ns F Q
          pure (.cons (.block b) .nil, kEnd)
        -- elaborated once here, for its errors and the names it takes
        let (_, kEnd) ← ElabM.lift (frame (recDepth - 1) fun _ => Prog.recBase)
        modify fun (Γc, _) => (Γc, kEnd)
        pure fun _ => recUnroll Prog.recBase
          (fun n bt => match frame n bt with
            | .ok (Q, _) => Q
            -- unreachable (a frame elaborates as the one checked above);
            -- were it reached, a panic, which no modality accepts
            | .error _ => .cons (.assert (.simple (.bool false))) .nil) recDepth)
    else
      modify fun (_, k) => (Γf, k)
      P ← withReader (fun sc =>
          { sc with funs := scope, top := false, selfFrame := selfFrame, unchecked := false,
                    inlined := (k₀, k₁) :: sc.inlined })
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
      match recBody with
      | some (n, mk) => pure (.of Γs (.callRec f n as .none (← mk ([] ++ ps) as.names)))
      | none =>
        let ⟨_, b⟩ ← ElabM.lift (SProg.chain as.names ([] ++ ps) (decls ++ P))
        pure (.of Γs (.call f as .none b))
    | .val p r =>
      let res' ← match res with
        | some (x, _) => do pure (some (← ElabM.lift (Γs.idx x (.val p))))
        | none => pure none
      match recBody with
      | some (n, mk) =>
        pure (.of Γs (.callRec f n as (.val p r res') (← mk ([.val p] ++ ps) (r :: as.names))))
      | none =>
        let ⟨_, b⟩ ← ElabM.lift (SProg.chain (r :: as.names) ([.val p] ++ ps) P)
        pure (.of Γs (.call f as (.val p r res') b))
    | .rets l =>
      let ⟨ρs, bs⟩ := Binders.ofList l
      match recBody with
      | some (n, mk) =>
        pure (.of Γs (.callRec f n as (.rets bs) (← mk (ρs ++ ps) (bs.names ++ as.names))))
      | none =>
        let ⟨_, b⟩ ← ElabM.lift (SProg.chain (bs.names ++ as.names) (ρs ++ ps) P)
        pure (.of Γs (.call f as (.rets bs) b))
    | .mem R r =>
      -- a memory return variable: declared on entry, a fresh default object
      let ⟨hm⟩ ← ElabM.lift (memOk R)
      match hd : (Ty.ref R).defaultOkS with
      | true =>
        match recBody with
        | some (n, mk) =>
          pure (.of Γs (.callRec f n as (.mem R r hd hm) (← mk ([.mem R] ++ ps) (r :: as.names))))
        | none =>
          let ⟨_, b⟩ ← ElabM.lift (SProg.chain (r :: as.names) ([.mem R] ++ ps) P)
          pure (.of Γs (.call f as (.mem R r hd hm) b))
      | false => throw s!"{f} returns a {Ty.ref R}, whose default is not well-formed"
    | .storage R r =>
      match recBody with
      | some (n, mk) =>
        pure (.of Γs (.callRec f n as (.storage R r) (← mk ([.alias R] ++ ps) (r :: as.names))))
      | none =>
        let ⟨_, b⟩ ← ElabM.lift (SProg.chain (r :: as.names) ([.alias R] ++ ps) P)
        pure (.of Γs (.call f as (.storage R r) b))
  unless as.separated Γs.names do throw s!"{f}: an argument reads a parameter"
  pure ([call], mret.map fun (R, r, storage) => (Γs, R, r, storage), mrets)

/-- **The body a `try` runs when its receiver is the contract itself**
(`Stmt.tryCall`'s `self`, `docs/options.md` O8): the callee `g` inlined as a
call with targets (`elabCallRet`), its environment the frame's
(`RawStmt.selfFrame`), when `g` is a function declared before this one whose
parameters take the arguments' types and whose return variables are the
`try`'s `ρ`; `none` otherwise (another contract's function, or one this
function may not call: the restriction that keeps the run structural). -/
partial def trySelfBody (g : String) {Γ : NCtx} (args : List (ExtArg C Γ.ctx)) (ρ : Ctx) :
    ElabM (Option ((ps : Ctx) × (Γf : Ctx) × Args C Γ.ctx ps × Prog C (ρ ++ ps) Γf)) := do
  let some (_, d) := (← read).funs.find? (·.1 == g) | pure none
  unless d.params.map (·.2) == args.map (fun a => Ty.prim a.1) do return none
  unless d.rets.all (fun (_, T) => T matches .prim _) do return none
  let raw := args.map fun a => Simple.toRaw C Γ.names a.2
  let r ← tryCatch (do
      let (P, _, _) ← elabCallRet g raw none (targets := true) (selfFrame := true)
      pure (some P)) fun _ => pure none
  let some [st] := r | pure none
  if h : st.Γ.ctx = Γ.ctx then
    pure (Stmt.selfCall? C ρ (h ▸ st.s))
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
partial def hoistStmt : RawStmt → ElabM (SProg C × RawStmt)
  | .pushOpAssign op b r => do
    let (P, r) ← hoist r
    let (Pc, r) ← if b.hasIncDec then captureExpr C r else pure ([], r)
    let (Q, b) ← hoist b
    pure (P ++ Pc ++ Q, .pushOpAssign op b r)
  | .pushIncDec op b => do
    let (P, b) ← hoist b
    pure (P, .pushIncDec op b)
  | .assign l r => do
    -- `m = f(a);` to a reference local: its arguments only (`elabStmt1`)
    if let .call f args := r then
      let isRefLocal := match synth C (← nctx) l with
        | .ok (.mpath (.ref _) (.var ..)) | .ok (.path (.ref _) (.alias ..)) => true
        | _ => false
      if (← read).funs.any (·.1 == f) && isRefLocal then
        let (P, args) ← hoistCallArgs f args
        return (P, .assign l (.call f args))
    match r, synth C (← nctx) l with
    | .incDec op e, .ok (.val _ (.simple (.local _))) =>
      let (P, e) ← hoist e
      pure (P, .assignIncDec l op e)
    | .newArr T n, _ =>
      let (P, n) ← hoist n
      let (Pc, n) ← if l.hasIncDec then captureExpr C n else pure ([], n)
      let (Q, l) ← hoist l
      pure (P ++ Pc ++ Q, .assign l (.newArr T n))
    | .call f args, .ok (.val _ (.simple (.local _))) =>
      if (castTy? f).isSome || (lookupBy f C.enums).isSome ||
          (byteBuiltin f && (← read).funs.all (·.1 != f)) then hoistAssign l r
      else
        let (P, args) ← hoistCallArgs f args
        pure (P, .assign l (.call f args))
    | _, _ => hoistAssign l r
  | .decl T x (some (.call f args)) => do
    if (castTy? f).isSome || (lookupBy f C.enums).isSome ||
        (byteBuiltin f && (← read).funs.all (·.1 != f)) then
      let (P, r) ← hoist (.call f args)
      return (P, .decl T x (some r))
    let (P, args) ← hoistCallArgs f args
    pure (P, .decl T x (some (.call f args)))
  | .decl T x (some r) => do
    let (P, r) ← hoistTop r
    pure (P, .decl T x (some r))
  | .declMemory T x (some (.newArr T' n)) => do
    let (P, n) ← hoist n
    pure (P, .declMemory T x (some (.newArr T' n)))
  -- a statement of one expression: its captures, then the statement
  | s@(.decl ..) | s@(.declStorage ..) | s@(.declMemory ..) | s@(.declStoragePush ..)
  | s@(.declPush ..) | s@(.delete _) | s@(.incDec ..) | s@(.ite ..) | s@(.require _)
  | s@(.assert _) | s@(.tryCall ..) => do
    -- `T memory x = f(a);`: its arguments only (`elabStmt1`)
    if let .declMemory T x (some (.call f args)) := s then
      if (← read).funs.any (·.1 == f) then
        let (P, args) ← hoistCallArgs f args
        return (P, .declMemory T x (some (.call f args)))
    if let .declStorage T x (some (.call f args)) := s then
      if (← read).funs.any (·.1 == f) then
        let (P, args) ← hoistCallArgs f args
        return (P, .declStorage T x (some (.call f args)))
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
    if let .call f getterArgs := e then
      if m == "push" || m == "pop" then
        let (P, getterArgs) ← hoistCallArgs f getterArgs
        return (P, .call (.field (.call f getterArgs) m) args)
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
    if (← read).funs.all (·.1 != f) then
      if let some op := ModOp.ofName? f then
        let [a, b, k] := args | throw s!"{f} takes three uint arguments"
        let (P, e) ← hoist (.modular op a b k)
        let (Q, _) ← captureExpr C e
        return (P ++ Q, .eval [])
    let (P, args) ← hoistCallArgs f args
    pure (P, .call (.name f) args)
  | .assignPush l b => do
    let (P, b) ← hoist b
    let (Q, l) ← hoist l
    pure (P ++ Q, .assignPush l b)
  | .send T x r a g => do
    -- the receiver first, then the amount, as `transfer`'s
    let (P, r) ← hoist r
    let (Pc, r) ← if a.hasIncDec && !(r matches .name _) then captureExpr C r
      else pure ([], r)
    let (Q, a) ← hoist a
    pure (P ++ Pc ++ Q, .send T x r a g)
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
  -- a call statement through a value that is not a name, `s.f(x);`
  -- (`callValueName`); `push`, `pop` and `transfer` are the receivers' own
  let s := match s with
    | .call (.name _) _ => s
    | .call e@(.field _ m) args =>
      if ["push", "pop", "transfer"].contains m then s else .call (.name callValueName) (e :: args)
    | .call e args => .call (.name callValueName) (e :: args)
    | s => s
  -- external function values and their members (`fnPure`)
  let s ← match s with
    | .call (.name f) as =>
      if f == callValueName then do
        let as' ← match ← ElabM.lift (fnPure C (← ctx) (.call f as)) with
          | .call _ as' => pure as'
          | _ => pure as
        pure (.call (.name f) as')
      else ElabM.lift (s.mapExprsM (fnPure C (← ctx)))
    | s => ElabM.lift (s.mapExprsM (fnPure C (← ctx)))
  -- `(T a, U b) = abi.decode(d, (T, U));`: each component decoded from its
  -- word (`#abiDecode`), `d` read once
  let decode? : Option (RawExpr × List RawExpr) := match s with
    | .tupleDecl _ (.call "abi.decode" [d, .tuple ts]) | .tupleAssign _ (.call "abi.decode" [d, .tuple ts]) =>
      some (d, ts)
    | _ => none
  if let some (d, ts) := decode? then
    if (← read).funs.all (·.1 != "abi.decode") then
      let x := toString (← freshCapture "mv")
      let n := ts.length
      let one (i : Nat) : RawExpr := .call abiDecodeName [.name x, ts[i]!, .num i, .num n]
      let rest : List RawStmt ← match s with
        | .tupleDecl vs _ => do
          unless vs.length == n do throw s!"abi.decode gives {n} values, not {vs.length}"
          pure (vs.zipIdx.filterMap fun (v, i) => v.map fun (T, y) => .decl T y (some (one i)))
        | .tupleAssign ls _ => do
          unless ls.length == n do throw s!"abi.decode gives {n} values, not {ls.length}"
          pure (ls.zipIdx.filterMap fun (l, i) => l.map fun l => .assign l (one i))
        | _ => pure []
      return ← elabStmtsP (.declMemory (.named "bytes") x (some d) :: rest)
  -- solc's operations on byte types, as the `uint` ones (`bytesPure`)
  let s ← ElabM.lift (bytesStmt C (← ctx) s)
  -- push arithmetic inside `unchecked`: the appended slot starts at `0`, so
  -- `b.push() op= r` pushes `0 op r`, wrapping at the element's width as
  -- `narrowWrapNode` wraps (`small.push() -= 1` at `uint8[]` pushes `255`):
  -- `r` itself for `+=`, `0` for `*=`, `r`'s negation for `-=` (`0` at `0`,
  -- `2^N - r` above it; a signed `r` at the minimum is itself), a literal
  -- folded; `r` is evaluated once, before the push, as the checked
  -- statement reads it
  if (← read).unchecked then
    let push? : Option (BinOp × RawExpr × RawExpr) := match s with
      | .pushOpAssign op b r => some (op, b, r)
      | .pushIncDec op b => some (if op.isIncrement then .add else .sub, b, .num 1)
      | _ => none
    if let some (op, b, r) := push? then
      let ⟨_, t⟩ ← synthM C b
      let .path (.ref (.array (.prim p))) _ := t
        | throw "push arithmetic needs a storage array of primitive numeric elements"
      unless p.isNumeric do throw s!"push arithmetic at {p.toStr}"
      let n := widthIn C (← ctx) (.index b (.num 0))
      let T := tyName p n
      let m : Int := 2 ^ n
      let lit (v : Int) : RawExpr :=
        let w := if p == .int then ((v + m / 2) % m + m) % m - m / 2 else (v % m + m) % m
        if w < 0 then .unop .neg (.num w.natAbs) else .num w.toNat
      let push (pre : List RawStmt) (v : RawExpr) : ElabM (SProg C) :=
        elabStmtsP (pre ++ [.call (.field b "push") [v]])
      match op, r.litVal? with
      | .add, some v => return ← push [] (lit v)
      | .sub, some v => return ← push [] (lit (-v))
      | .mul, some _ => return ← push [] (.num 0)
      | .add, none | .sub, none | .mul, none =>
        -- `r` at the element's type, captured where it is not a name
        let (pre, R) ← if r.isPure then pure ([], RawExpr.call T [r]) else do
          let y := toString (← freshCapture "pa")
          pure ([RawStmt.decl (.named T) y (some r)], RawExpr.name y)
        let v : RawExpr := match op with
          | .add => R
          | .mul => .binop .mul R (.num 0)
          | _ =>
            if p == .int then
              .ternary (.binop .eqB R (.unop .neg (.num (2 ^ (n - 1))))) R (.binop .sub (.num 0) R)
            else
              .ternary (.binop .eqB R (.num 0)) (.num 0)
                (.binop .add (.binop .sub (.num (2 ^ n - 1)) R) (.num 1))
        return ← push pre v
      | _, _ => return ← push [] (.binop op (.num 0) r)
  -- a loop outside a function's body, lowered here (`lowerLoops`)
  if s matches .whileLoop .. | .forLoop .. | .doWhile .. then
    return ← elabStmtsP (← lowerLoops none [s])
  -- a place with a narrow position below it is used through its indices and
  -- members, or whole where its narrow positions are checked against the
  -- target's (`shapeCheck`): a reference local's initializer, a reference
  -- assignment, a push bound to an alias, an argument (`elabCallRet`)
  let Γ ← ctx
  let isRef (l : RawExpr) : Bool := (widthPath? C Γ l).any fun (_, _, t) => t matches .ref _
  let whole ← match s with
    | .declStorage T _ (some e) | .declMemory T _ (some e) => do
      ElabM.lift (shapeCheck C Γ (← ElabM.lift (elabTyW C T)).2 e); pure true
    | .declStoragePush T _ b => do
      ElabM.lift (shapeCheck C Γ (← ElabM.lift (elabTyW C T)).2 (.index b (.num 0))); pure true
    | .assignPush l b =>
      if isRef l then do
        ElabM.lift (shapeCheck C Γ (placeShape C Γ l) (.index b (.num 0))); pure true
      else pure true
    | .assign l r =>
      if isRef l then do ElabM.lift (shapeCheck C Γ (placeShape C Γ l) r); pure true
      else pure false
    | .declPush .. => pure true
    | _ => pure false
  -- a call statement's arguments, as a call expression's (`narrowWholeUse?`)
  -- a push's receiver, as a `.push` member's base
  let es : List (RawExpr × Bool) := match s with
    | .call (.name f) as => [(RawExpr.call f as, whole)]
    | .pushOpAssign _ b r => [(b, true), (r, whole)]
    | .pushIncDec _ b => [(b, true)]
    | s => s.exprs.map (·, whole)
  unless s matches .delete _ do
    for (e, base) in es do
      let w := if base then narrowWholeAt? C Γ e else narrowWholeUse? C Γ e
      if let some w := w then
        throw s!"{w.toStr} has a narrow element, key or value: it is used through an index, \
          `.length`, `.push`, `.pop` or `delete`, or whole where the same narrow positions are \
          expected, not whole"
  let s ← ElabM.lift (s.mapExprsM (narrowPure C (← read).unchecked (← ctx)))
  let (P, s) ← hoistStmt s
  let P ← pure (P ++ (← elabStmt1 s))
  -- a reference local's narrow positions (`LocalTy.shape`)
  match s with
  | .declStorage T x _ | .declMemory T x _ | .declStoragePush T x _ =>
    declareShape x (← ElabM.lift (elabTyW C T)).2
  | _ => pure ()
  pure P

/-- A statement whose expressions have no effect left. -/
partial def elabStmt1 : RawStmt → ElabM (SProg C)
  | .pushOpAssign op b r => do
    let ⟨Γ, t⟩ ← synthM C b
    let .path (.ref (.array (.prim p))) path := t
      | throw "push arithmetic needs a storage array of primitive numeric elements"
    -- at a narrow element (`uint8[]`), `r` fits it and the appended slot is
    -- checked after the write, as `narrowPost` checks a variable's
    let n := widthIn C (← ctx) (.index b (.num 0))
    ElabM.lift (fitCheck C (← ctx) p n r)
    match hop : op.hasCompoundAssign, hp : p.isNumeric with
    | true, true => pure (.of Γ (.pushOpAssign op hop hp path (← checkIn C Γ p r)) ::
        (← narrowCheck C p n (pushedSlot b)))
    | false, _ => throw s!"no push compound assignment for {BinOp.sym op}"
    | _, false => throw s!"push arithmetic at {p.toStr}"
  | .pushIncDec op b => do
    let ⟨Γ, t⟩ ← synthM C b
    let .path (.ref (.array (.prim p))) path := t
      | throw "push arithmetic needs a storage array of primitive numeric elements"
    let n := widthIn C (← ctx) (.index b (.num 0))
    match hp : p.isNumeric with
    | true => pure (.of Γ (.pushIncDec op hp path) :: (← narrowCheck C p n (pushedSlot b)))
    | false => throw s!"push increment/decrement at {p.toStr}"
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
    | .path (.ref R) (.alias x) =>
      let xn := x.name Γ.names
      elabStorageCall f args R fun Γ' r => do
        let Γr : NCtx := (r, .alias R) :: Γ'
        pure (.of Γr (.rebind (← Γr.idx xn (.alias R)) (.path (.alias .here))))
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
        | _ => do pure [.of Γ (.assign l (← ElabM.lift (checkStorageCopy C Γ R r)))]
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
    declareShape x (← ElabM.lift (bytesRowsOf C T))
    pure (.of Γ (.declLocal p (Var.ofName x) none) :: P)
  | .decl T x init => do
    let (.prim p, n) ← ElabM.lift (elabDeclTy C T) | throw s!"{x}: a reference type needs a data location"
    let Γ ← nctx
    let v ← init.mapM (checkIn C Γ p)
    declare C x (.val p n)
    declareShape x (← ElabM.lift (bytesRowsOf C T))
    let post ← match init with
      | some r => narrowPost C (.name x) r
      | none => pure []
    pure (.of Γ (.declLocal p (Var.ofName x) v) :: post)
  | .declStorage T x (some (.call f args)) => do
    let .ref R ← ElabM.lift ((·.1) <$> elabTyW C T) | throw s!"{x}: `storage` on a value type"
    let P ← elabStorageCall f args R fun Γ r =>
      pure (.of ((r, .alias R) :: Γ) (.declStorage R (Var.ofName x) (some (.path (.alias .here)))))
    declare C x (.alias R)
    pure P
  | .declStorage T x init => do
    let .ref R ← ElabM.lift ((·.1) <$> elabTyW C T) | throw s!"{x}: `storage` on a value type"
    let Γ ← nctx
    let init ← ElabM.lift (init.mapM fun e => ARhs.path <$> checkPath C Γ (.ref R) e)
    declare C x (.alias R)
    pure [.of Γ (.declStorage R (Var.ofName x) init)]
  | .declStoragePush T x b => do
    let .ref R ← ElabM.lift ((·.1) <$> elabTyW C T) | throw s!"{x}: `storage` on a value type"
    let Γ ← nctx
    let r ← ElabM.lift (elabPush C Γ R b)
    declare C x (.alias R)
    pure [.of Γ (.declStorage R (Var.ofName x) (some r))]
  | .declPush T x b => do
    let (.prim p, n) ← ElabM.lift (elabDeclTy C T) | throw s!"{x}: a reference type needs a data location"
    let Γ ← nctx
    let b ← ElabM.lift (elabPrimPush C Γ p b)
    declare C x (.val p n)
    let ⟨Γ', th, ix⟩ ← afterCapture Γ (Var.ofName x) (.val p)
    pure [.of Γ (.declLocal p (Var.ofName x) none),
      .of Γ' (.assignLocalPush ix (b.wk th))]
  | .assignPush l b => do
    let ⟨Γ, t⟩ ← synthM C l
    match t with
    | .path (.ref R) (.alias x) => pure [.of Γ (.rebind x (← ElabM.lift (elabPush C Γ R b)))]
    | .val _ (.simple (.local _)) => do
      let ⟨Γ, .val p (.simple (.local i))⟩ ← synthM C l
        | throw "a pushed primitive's target must remain a value local"
      let b ← ElabM.lift (elabPrimPush C Γ p b)
      pure [.of Γ (.assignLocalPush i b)]
    | _ => throw "`= b.push()` binds a storage pointer or a value local"
  | .declMemory T x (some (.newArr T' n)) => do
    let .ref R ← ElabM.lift ((·.1) <$> elabTyW C T) | throw s!"{x}: `memory` on a value type"
    let ⟨R', hR⟩ ← elabNewTy C T'
    unless R' = R do throw s!"{x}: `new` of another type"
    let (P, ⟨Γ, se⟩) ← elabSize C n
    declare C x (.mem R')
    pure (P ++ [.of Γ (.declMem R' (Var.ofName x) (some (.newArr se hR)) rfl
      (MRhs.newArr (C := C) se hR).mapFree)])
  | .declMemory T x (some (.call f args)) => do
    let .ref R ← ElabM.lift ((·.1) <$> elabTyW C T) | throw s!"{x}: `memory` on a value type"
    let P ← elabMemCall f args R fun Γ r hm =>
      pure (.of ((r, .mem R) :: Γ) (.declMem R (Var.ofName x) (some (.alias (.var .here hm))) rfl hm))
    declare C x (.mem R)
    pure P
  | .declMemory T x init => do
    let .ref R ← ElabM.lift ((·.1) <$> elabTyW C T) | throw s!"{x}: `memory` on a value type"
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
      let e ← ElabM.lift (narrowWrapNode C (← read).unchecked (← ctx) (.binop op l r))
      -- a signed wrap is a cast, captured (`narrowWrapNode`)
      if e matches .call .. then return ← elabStmtP (.assign l e)
      return ← elabStmt1 (.assign l e)
    let (pre, ⟨Γ, p, t⟩) ← elabOpTarget C l
    -- at a narrow target, what `l ⊕ r` may leave the type by is checked after
    let n := widthIn C (← ctx) l
    ElabM.lift (fitCheck C (← ctx) p n r)
    let post ← if (op matches .add | .sub | .mul) || (op == .div && p == .int) then
      narrowCheck C p n l else pure []
    match hop : op.hasCompoundAssign, hp : p.isNumeric with
    | true, true => pure (pre ++ [.of Γ (.opAssign op hop hp t (← checkIn C Γ p r))] ++ post)
    | false, _ => throw s!"no compound assignment for {BinOp.sym op}"
    | _, false => throw s!"a compound assignment at {p.toStr}"
  | .incDec op l => do
    let (pre, ⟨Γ, p, t⟩) ← elabOpTarget C l
    match hp : p.isNumeric with
    | true => pure (pre ++ [.of Γ (.incDec op hp t)] ++ (← narrowCheck C p (widthIn C (← ctx) l) l))
    | false => throw s!"++ or −− at {p.toStr}"
  | .assignIncDec x op l => do
    let (pre, ⟨Γ, p, t, hs⟩) ← elabIncTarget C l
    match ← ElabM.lift (synth C Γ x) with
    | .val q (.simple (.local y)) =>
      ElabM.lift (fitCheck C (← ctx) q (widthIn C (← ctx) x) l)
      match hp : p.isNumeric with
      | true => if h : q = p then
                  pure (pre ++ [.of Γ (.assignIncDec (h ▸ y) op hp t hs)] ++
                    (← narrowCheck C p (widthIn C (← ctx) l) l))
                else throw s!"a {p.toStr} assigned to a {q.toStr}"
      | false => throw s!"++ or −− at {p.toStr}"
    | _ => throw "the result of ++ or −− goes to a stack local"
  | .call (.field (.call f args) "push") values => do
    match values with
    | [] =>
      elabCallReceiver f args fun _ E => do
        match hd : E.defaultOkS with
        | true => pure (.push none (by simp only [Option.isSome_none, hd, Bool.or_true]))
        | false => throw "push() of an element whose default is not well-formed"
    | [a] => elabCallReceiverPush f args a
    | _ => throw "push takes at most one argument"
  | .call (.field (.call f args) "pop") [] =>
    elabCallReceiver f args fun _ _ => pure .pop
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
      | .prim p =>
        -- a narrow element: the value converts to it implicitly, so it fits
        ElabM.lift (fitCheck C (← ctx) p (widthIn C (← ctx) (.index e (.num 0))) a)
        pure [.of Γ (.push b (some (.val (← checkIn C Γ p a))) rfl)]
      | .ref R =>
        if let .mpath (.ref _) _ ← ElabM.lift (synth C Γ a) then
          let mp ← ElabM.lift (checkMPath C Γ (.ref R) a)
          return [.of Γ (.push b (some (.copyMem mp)) rfl)]
        pure [.of Γ (.push b (some (← ElabM.lift (checkStorageCopy C Γ R a))) rfl)]
    | _ => throw "push takes at most one argument"
  | .call (.field e "pop") [] => do
    let ⟨Γ, t⟩ ← synthM C e
    let .path (.ref (.array _)) b := t | throw "pop on something that is not an array"
    pure [.of Γ (.pop b)]
  | .call (.field e "transfer") [a] => do
    let Γ ← nctx
    pure [.of Γ (.transfer (← checkIn C Γ .uint e) (← checkIn C Γ .uint a))]
  | .send T x e a g => do
    let Γ ← nctx
    let r ← checkIn C Γ .uint e
    let v ← checkIn C Γ .uint a
    match T, x with
    | some T, .name n =>
      let (.prim .bool, w) ← ElabM.lift (elabDeclTy C T)
        | throw s!"{n}: `send` returns a bool"
      declare C n (.val .bool w)
      let ⟨Γ', th, ix⟩ ← afterCapture Γ (Var.ofName n) (.val .bool)
      if g then
        return [.of Γ (.declLocal .bool (Var.ofName n) none)] ++
          (← elabValueCall Γ' ix (.name n) e a)
      pure [.of Γ (.declLocal .bool (Var.ofName n) none), .of Γ' (.send ix (r.wk th) (v.wk th) g)]
    | some _, _ => throw "`T x = r.send(a);` declares a name"
    | none, x =>
      match ← ElabM.lift (synth C Γ x) with
      | .val .bool (.simple (.local y)) =>
        if g then elabValueCall Γ y x e a else pure [.of Γ (.send y r v g)]
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
    -- quantified clauses alone: the plain invariant is `true`
    let a := if a.inv.isEmpty && !a.qinv.isEmpty then { a with inv := [.bool true] } else a
    let a : LoopAnn C Γ.ctx ← match a.inv, a.unwind with
      | [], u => do
        if a.dec.isSome then throw "a loop's `decreases` clause without an `invariant`"
        pure (u.map LoopAnn.unwind |>.getD LoopAnn.auto)
      | i :: is, none => do
        let I ← loopExpr Γ .bool (RawExpr.andAll (i :: is).dropLast ((i :: is).getLast?.getD i))
          "invariant"
        pure (.inv I (← a.dec.mapM fun d => loopExpr Γ .uint d "variant") a.brk
          (← a.qinv.mapM (loopQ Γ)))
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
  | .assumeFalse => do pure [.of (← nctx) .assumeFalse]
  | .eval _ => pure []
  | .unchecked ss => do
    withReader (fun sc => { sc with unchecked := true }) (elabBranch (← ElabM.lift (uncheckStmts ss)))
  | .checked o ss => do
    -- the guards made once, by the outermost block (`Prog.withOF`)
    match (← read).overflow with
    | some o' =>
      if o' == o then elabBranch ss
      else throw "`checked { … }` and `ignoringOverflow { … }` do not nest in each other"
    | none =>
      let P ← withReader (fun sc => { sc with overflow := some o }) (elabBranch ss)
      pure (P.flatMap (SStmt.withOF o))
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
    let sb ← trySelfBody g args' ρ
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
    match sb with
    | some ⟨_, _, sargs, sbody⟩ =>
      pure (Q ++ [.of Γ (.tryCall ⟨addr', g, args'⟩ bs ok.2 err.2 cb pnc.2 other.2 sargs sbody true)])
    | none =>
      pure (Q ++ [.of Γ (.tryCall ⟨addr', g, args'⟩ bs ok.2 err.2 cb pnc.2 other.2 .nil .nil false)])

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
    let (P, args) ← hoistCallArgs f args
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

end Elab

end Solidity
