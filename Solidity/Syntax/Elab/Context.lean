import Solidity.Syntax.Scoped
import Solidity.Syntax.Join
import Solidity.Syntax.Checked
import Solidity.Keccak
import Solidity.RevertBytes

/-!
# The elaborator's contexts and the passes on the raw syntax

Named contexts (`NCtx`) and the passes on the raw syntax that the typing
leaves untouched: traversals, `calldata` parameters, block locals renamed
apart, calldata slices, the recursion thunk, and the locals a part reads.

A piece of `Syntax/Elab.lean`, whose docstring describes the whole.
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
      -- a `calldata` one a memory one the body does not write (`calldataCheck`)
      | some .memory | some .calldata =>
        if (Ty.ref R).mapFree then .ok (shapeEntry n (shapeUnder d.widths n) ++ [(n, .mem R)])
        else .error s!"memory parameter {n} holds a mapping"
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
  | .call "#array" as => s!"[{", ".intercalate (as.map (·.toStr))}]"
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

/-- Exact rational arithmetic for a whole literal expression. Intermediate
negative or fractional values are not checked at the target word type. -/
def RawExpr.constRat? : RawExpr → Option (Int × Int)
  | .num n => some (n, 1)
  | .unop .neg a => do
    let (n, d) ← a.constRat?
    pure (-n, d)
  | .binop op a b => do
    let (an, ad) ← a.constRat?
    let (bn, bd) ← b.constRat?
    match op with
    | .add => pure (an * bd + bn * ad, ad * bd)
    | .sub => pure (an * bd - bn * ad, ad * bd)
    | .mul => pure (an * bn, ad * bd)
    | .div => if bn == 0 then none else pure (an * bd, ad * bn)
    | _ => none
  | _ => none

/-- Fold an integral constant once, before capturing or typing its operands. -/
def RawExpr.foldConst (e : RawExpr) : Except String RawExpr :=
  match e.constRat? with
  | none => pure e
  | some (n, d) =>
    if d == 0 || n % d != 0 then throw "a non-integral rational constant"
    else let v := n / d
         pure (if v < 0 then .unop .neg (.num v.natAbs) else .num v.toNat)

/-- An expression inside `unchecked { … }`: `+ - * **` wrap (`+%` …).  An
`++`/`−−` inside it is an error: its capture (`hoist`) is checked. -/
def RawExpr.uncheck : RawExpr → Except String RawExpr :=
  RawExpr.mapM fun e => do
    let e ← e.foldConst
    match e with
    | .binop op a b =>
      let op' : BinOp := match op with
        | .add => .addW | .sub => .subW | .mul => .mulW | .pow => .powW | op => op
      pure (.binop op' a b)
    | .opAssign op l r =>
      let op' : BinOp := match op with
        | .add => .addW | .sub => .subW | .mul => .mulW | .pow => .powW | op => op
      pure (.opAssign op' l r)
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
  | .ite b _ _ | .requireMsg b _ => [b]
  | .revertErr _ as => as
  | .requireErr c _ as => c :: as
  | .revertReason m | .revertRaw m => [m]
  | .requireReason c m => [c, m]
  | .call f as => f :: as
  | .eval as => as
  | .tryCall r _ as .. => r :: as
  | .send none x r a _ => [x, r, a]
  | .send (some _) _ r a _ => [r, a]
  | .tupleDecl _ r => [r]
  | .tupleAssign ts r => ts.filterMap id ++ [r]
  | .revert | .revertMsg _ | .assumeFalse | .unchecked _ | .checked .. | .block _ | .brk | .cont
  | .hole => []
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
  | .revertMsg m => pure (.revertMsg m)
  | .requireMsg b m => return .requireMsg (← f b) m
  | .revertReason m => return .revertReason (← f m)
  | .requireReason c m => return .requireReason (← f c) (← f m)
  | .revertRaw d => return .revertRaw (← f d)
  | .revertErr e as => return .revertErr e (← as.mapM f)
  | .requireErr c e as => return .requireErr (← f c) e (← as.mapM f)
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

/-! ### `calldata` parameters

A `calldata` parameter is a memory parameter the body does not write
(`docs/semantic-gaps.md`, "Bytes and strings"): solc refuses a write to
calldata, and a copy of it to memory (`T memory m = xs;`, an argument to a
`memory` parameter, a `memory` return) is a copy there, where the model's
memory binding shares the object.  So the elaborator reads it as a memory
local and refuses, before the body is elaborated (`calldataCheck`), a write
through it and through every memory name bound to it, a binding of it
returned, and an argument of it to a callee's `memory` parameter the callee
writes: what is left only reads the object, where sharing and copying agree. -/

/-- The names of a function's reference returns. -/
def FunDecl.refRets (d : FunDecl) : List String :=
  d.rets.filterMap fun (x, T) => if T matches .ref _ then some x else none

/-- Its `calldata` parameters. -/
def FunDecl.calldataParams (d : FunDecl) : List String :=
  d.paramLocs.filterMap fun (x, l) => if l == .calldata then some x else none

/-- Why a write through calldata is refused. -/
def roMsg : String :=
  "a write through calldata or a memory binding of it: solc refuses the first and copies \
    calldata to memory for the second, where the model would share the object"

/-- The name a write target is rooted at: `x` of `x[i].f`. -/
def RawExpr.root? : RawExpr → Option String
  | .name x => some x
  | .index e _ | .field e _ => e.root?
  | _ => none

/-- A write through one of the names `ro` (not a binding of the name itself). -/
def roWrite (ro : List String) (l : RawExpr) : Bool :=
  !(l matches .name _) && (l.root?.any ro.contains)

/-- The writes inside an expression (`(x[0] = 1)`, `x[0]++`) through `ro`. -/
def RawExpr.roWrites (ro : List String) (e : RawExpr) : Bool :=
  e.any fun
    | .assign l _ | .opAssign _ l _ | .incDec _ l => roWrite ro l
    | _ => false

/-- Whether an expression may retain the read-only object named `x`.
A slice materialization allocates and copies primitive elements; its result
retains no alias of its source. Effects inside its descriptor are still
visited by `roWrites` and the nested-assignment scan in `roStmt`. -/
def RawExpr.roMentions (x : String) (e : RawExpr) (memoryReturns : List String := []) : Bool :=
  (Id.run <| e.mapM fun
    | .call "#sliceCopy" _ => pure (.num 0)
    | .call f args => pure (if memoryReturns.contains f then .num 0 else .call f args)
    | e => pure e).mentions x

/-- What `calldataCheck` refuses in one statement (not its blocks), and the
names it binds to the read-only object. -/
def roStmt (ro : List String) (s : RawStmt) (memoryReturns : List String := []) : Except String (List String) := do
  -- Effects nested in a tuple or an array literal can rebind another
  -- local before the outer assignment. Retain those aliases too.
  let binds := s.exprs.flatMap fun e => e.names.filter fun x =>
    e.any fun | .assign l r => l.root? == some x && ro.any (fun x => r.roMentions x) | _ => false
  let ro := (binds ++ ro).eraseDups
  let mention (e : RawExpr) : Bool := ro.any (fun x => e.roMentions x memoryReturns)
  if s.exprs.any (RawExpr.roWrites ro) then
    throw roMsg
  match s with
  | .assign l r =>
    if roWrite ro l then throw s!"{l.toStr}: {roMsg}"
    pure (if mention r then l.root?.toList ++ ro else ro)
  | .opAssign _ l _ | .incDec _ l | .assignIncDec _ _ l | .delete l =>
    if roWrite ro l then throw s!"{l.toStr}: {roMsg}" else pure ro
  | .tupleAssign ts rhs =>
    if ts.any (·.any (roWrite ro)) then throw roMsg
    -- Capturing references preserves calldata's read-only origin. A
    -- conservative join also covers a tuple returned by a call.
    pure (if mention rhs then (ts.filterMap fun t => t.bind RawExpr.root?) ++ ro else ro)
  | .call (.field b m) _ =>
    if (m == "push" || m == "pop") && b.root?.any ro.contains then
      throw s!"{b.toStr}.{m}: {roMsg}"
    else pure ro
  | .declMemory _ x (some e) => pure (if mention e then x :: ro else ro)
  | _ => pure ro

/-- The name of a slice's refusal (`RawStmt.sliceViews`), its reason the
argument's name; `calldataCheck` reports it. -/
def sliceRefusedName : String := "#sliceRefused"

/-- The reason of the first slice refused in the body (`RawStmt.sliceViews`). -/
def sliceRefusal? (body : List RawStmt) : Option String :=
  (body.flatMap (RawStmt.flatMapDeep fun s => s.exprs)).findSome? fun e =>
    let found := e.any fun | .call f _ => f == sliceRefusedName | _ => false
    if !found then none else
      some <| Id.run do
        let mut r := "a calldata slice"
        for x in (e.names) do
          if x.startsWith "a calldata slice" then r := x
        return r

/-- **What a body does with its `calldata` parameters `ro`** (above): a
write through one, or through a memory name bound to one, is refused; so is
returning one where the function returns a memory reference (`rets`, its
reference returns), and passing one to a callee's `memory` parameter the
callee writes.  `fuel` bounds the callees followed. -/
partial def calldataCheck (funs : List (String × FunDecl)) (fuel : Nat) (ro rets : List String)
    (body : List RawStmt) : Except String Unit := do
  if let some r := sliceRefusal? body then throw r
  if ro.isEmpty then return
  -- Callee memory-argument checks below retain conservative mentions: a
  -- memory return that aliases a calldata argument must still be refused.
  let memoryReturns := funs.filterMap fun (name, declaration) =>
    if declaration.retMem && !declaration.retStorage && declaration.refRets.length == 1 then some name else none
  let ss := body.flatMap (RawStmt.flatMapDeep fun s => [s])
  -- the names bound to the object, to a fixed point (a loop may bind late)
  let mut ro := ro.eraseDups
  -- Every added root occurs in this finite body. Iterate to a fixed point
  -- rather than assuming that three passes cover a loop's alias chain.
  let roots := (ss.flatMap fun s => s.exprs.flatMap RawExpr.names ++ s.binds).eraseDups
  for _ in [0:roots.length + 1] do
    let before := ro.length
    for s in ss do
      ro := (← roStmt ro s memoryReturns).eraseDups
    if ro.length == before then break
  let mention (e : RawExpr) : Bool := ro.any (fun x => e.roMentions x memoryReturns)
  if let some r := rets.find? ro.contains then
    throw s!"the memory return {r} bound to calldata: solc copies it, the model would share it"
  for s in ss do
    if let .ret (some e) := s then
      if !rets.isEmpty && mention e then
        throw "calldata returned as memory: solc copies it, the model would share it"
    -- a call statement's callee, as the expression it would be
    let es := match s with
      | .call (.name g) as => RawExpr.call g as :: s.exprs
      | _ => s.exprs
    for e in es do
      for (g, d) in funs do
        let offends := e.any fun
          | .call g' as => g' == g && (d.params.zip as).any fun ((p, _), a) =>
              lookupBy p d.paramLocs == some .memory && ro.any (fun x => a.roMentions x) &&
                (fuel == 0 || (calldataCheck funs (fuel - 1) [p] (d.refRets) d.body).isOk == false)
          | _ => false
        if offends then
          throw s!"{g}: calldata passed to a `memory` parameter it writes: solc copies it, \
            the model would share it"

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

/-- `mapBlocks` in a monad, the blocks in order. -/
def RawStmt.mapBlocksM {m : Type → Type} [Monad m] (f : List RawStmt → m (List RawStmt)) :
    RawStmt → m RawStmt
  | .ite c t e => return .ite c (← f t) (← f e)
  | .unchecked b => return .unchecked (← f b)
  | .checked o b => return .checked o (← f b)
  | .block b => return .block (← f b)
  | .tryCall r g as rets ok err code pnc other =>
    return .tryCall r g as rets (← f ok) (← f err) code (← f pnc) (← f other)
  | .whileLoop a c b => return .whileLoop a c (← f b)
  | .doWhile a b c => return .doWhile a (← f b) c
  | .loop a c b => return .loop a c (← f b)
  | .forLoop a i c u b => return .forLoop a (← f i) c (← f u) (← f b)
  | s => pure s

/-! ### Calldata slices

`b[i:j]` of a calldata array is a view of it, as solc reads it: no copy.
`RawStmt.sliceViews` rewrites a body before it is elaborated (the
`contract!` and `sol_raw!` macros apply it to a body that has a slice).  A
view is its base and where it starts and ends in it, `o` and `f`, after
solc's checks `i <= j` and `j` within the sliced array (a revert
otherwise; `j` is the array's length where it is left out, `i` is `0`).
The base is captured before either endpoint, and nonconstant endpoints
are captured once. Relative bounds are checked before offsets are added.
A named view retains that captured identity even if its source is rebound.
Inline views open at their expression's evaluation position through private
markers. An index is captured there too: only `k < f - o` evaluates `o + k`;
otherwise the base's out-of-range index supplies its bounds panic. Short
circuiting keeps these effects in the branch that reads the slice.
`t.length` is `f - o`, and `abi.decode(t, …)` reads the view without a copy.
A `calldata` local retains a view; a `memory` initializer and other whole
uses materialize a fresh flat array (`#sliceCopy`, `hoistWith`). This is also
how a view crosses an internal call boundary. Reference-element copies and
rebinding a view local remain refused. -/

/-- A slice's view: its base array, and where it starts and ends in it
(each a literal, the base's length, or a local assigned once). -/
structure SliceView where
  base : String
  off : RawExpr
  fin : RawExpr
  deriving Inhabited

/-- The hidden builtin a view is decoded through: `#sliceV(b, o, n)`. -/
def sliceViewName : String := "#sliceV"

/-- Inside `unchecked`, and evaluated only on a condition (a conditional's
branch, the right operand of `&&`/`||`, a loop's condition); the views
open, a counter for the names of inline slices, and the statements the
current statement's slices open before it. Ordinary aliases retain their
known calldata origins separately from virtual slice descriptors. Both lists
are restored when a nested lexical scope ends. -/
abbrev SliceSt := List (String × SliceView) × List String × Nat × Array RawStmt

@[inherit_doc SliceSt]
abbrev SliceM := StateT (Bool × Bool) (StateM SliceSt)

instance : Inhabited (SliceM RawExpr) := ⟨pure default⟩

/-- A refusal in place of an expression, its reason the argument. -/
def sliceRefuse (why : String) : RawExpr :=
  .call sliceRefusedName [.name s!"a calldata slice {why}: refused (docs/semantic-gaps.md, \
    \"Bytes and strings\")"]

/-- Whether an expression is a slice or names a view. -/
def sliceViewish (views : List (String × SliceView)) : RawExpr → Bool
  | .name x => (lookupBy x views).isSome
  | .call f _ => f == "#slice"
  | _ => false

/-- An ordinary calldata alias must come from a stable place rooted in an
actual calldata parameter or another admitted ordinary alias. Calls, effects
and conditional references are deliberately outside this admission path. -/
def RawExpr.calldataPlace (origins : List String) : RawExpr → Bool
  | .name x => origins.contains x
  | .field b _ => b.calldataPlace origins
  | .index b i => b.calldataPlace origins && i.isPure
  | _ => false

/-- A write target rooted in a virtual view or an inline slice. Only the
base of indexing/member access is a target; slices read inside its index
are ordinary expressions, so `a[xs[:].length] = v` remains legal. -/
def RawExpr.sliceTarget (views : List String) : RawExpr → Bool
  | .name x => views.contains x
  | .index b _ | .field b _ => b.sliceTarget views
  | .assign _ rhs => rhs.sliceTarget views
  | .ternary _ yes no => yes.sliceTarget views || no.sliceTarget views
  | .call "#slice" _ => true
  | _ => false

/-- `o + k`, folded where a side is a literal. -/
def sliceAdd (o k : RawExpr) : RawExpr :=
  match o, k with
  | .num 0, k => k
  | o, .num 0 => o
  | .num a, .num b => .num (a + b)
  | o, k => .binop .add o k

/-- `e - o`, folded where `o` is `0` or both are literals. -/
def sliceSub (e o : RawExpr) : RawExpr :=
  match e, o with
  | e, .num 0 => e
  | .num a, .num b => .num (a - b)
  | e, o => .binop .sub e o

/-- Its length. -/
def SliceView.len (v : SliceView) : RawExpr := sliceSub v.fin v.off

/-- `x` evaluated only on a condition (above). -/
def sliceCond {α : Type} (x : SliceM α) : SliceM α := do
  let u ← getThe (Bool × Bool)
  set (σ := Bool × Bool) (u.1, true)
  let r ← x
  set (σ := Bool × Bool) u
  return r

/-- Hide an inline slice until its containing expression is evaluated,
while replacing an already opened view by its stable descriptor. -/
partial def slicePack (views : List (String × SliceView)) : RawExpr → RawExpr
  | .name x => match lookupBy x views with
    | some sv => .call "#sliceDesc" [.name sv.base, sv.off, sv.fin]
    | none => .name x
  | .call "#slice" [b, i, j] => .call "#sliceRaw" [slicePack views b, i, j]
  | e => e

mutual

/-- The view `t` of `b[i:j]`: its checks and locals pushed before the
statement. The base and bounds retain their source evaluation order. -/
partial def sliceOpen (t : String) (b i j : RawExpr) : SliceM (Option SliceView) := do
  let t := "#slice$" ++ t
  -- Capture the base before either bound. A view must survive later
  -- rebinding or shadowing of the source name.
  let outer ← match b with
    | .name x =>
      match lookupBy x (← getThe SliceSt).1 with
      | some v => pure v
      | none =>
        let base := t ++ "$view$base"
        modifyThe SliceSt fun (vs, origins, k, pre) =>
          (vs, origins, k, pre.push (.declMemory (.named "#sliceBase") base (some b)))
        pure { base, off := .num 0, fin := .field (.name base) "length" }
    | .call "#sliceDesc" [.name base, off, fin] => pure { base, off, fin }
    | .call "#slice" [b, i, j] | .call "#sliceRaw" [b, i, j] =>
      let some v ← sliceOpen (t ++ "$outer") b i j | return none
      pure v
    | b =>
      let base := t ++ "$view$base"
      modifyThe SliceSt fun (vs, origins, k, pre) =>
        (vs, origins, k, pre.push (.declMemory (.named "#sliceBase") base (some b)))
      pure { base, off := .num 0, fin := .field (.name base) "length" }
  let i ← i.mapM sliceNode
  let j ← (if j matches .call "#sliceEnd" [] then pure outer.len else j.mapM sliceNode)
  let fixed : RawExpr → Bool
    | .num _ => true
    | .field (.name x) "length" => x == outer.base
    | .name x => x.startsWith "#slice$"
    | _ => false
  let bind (sfx : String) (x : RawExpr) (ss : Array RawStmt) : RawExpr × Array RawStmt :=
    if fixed x then (x, ss)
    else (.name (t ++ "$view$" ++ sfx), ss.push (.decl (.named "uint") (t ++ "$view$" ++ sfx) (some x)))
  let (st, ss) := bind "s" i #[]
  let (e, ss) := bind "e" j ss
  let ss := match st, e with
    | .num a, .num c => if a > c then ss.push (.require (.bool false)) else ss
    | .num 0, _ => ss
    | _, _ => ss.push (.require (.binop .le st e))
  -- Check relative bounds before adding an offset. An invalid large bound
  -- must revert as a slice, rather than overflowing offset + bound.
  let ss := ss.push (.require (.binop .le e outer.len))
  let (off, ss) := bind "o" (sliceAdd outer.off st) ss
  let (fin, ss) := bind "f" (sliceAdd outer.off e) ss
  modifyThe SliceSt fun (vs, origins, k, pre) => (vs, origins, k, pre ++ ss)
  return some { base := outer.base, off, fin }

/-- The view an expression is: a view's name, or a slice opened here. -/
partial def sliceViewOf? : RawExpr → SliceM (Option SliceView)
  | .name x => return lookupBy x (← getThe SliceSt).1
  | .call "#slice" [b, i, j] => do
    let (_, _, k, _) ← getThe SliceSt
    modifyThe SliceSt fun (vs, origins, _, pre) => (vs, origins, k + 1, pre)
    sliceOpen s!"slice{k}" b i j
  | _ => pure none

/-- One node (`RawExpr.mapM`): index, length and decoding read the view;
other value uses copy it at their expression's evaluation position. -/
partial def sliceNode (e : RawExpr) : SliceM RawExpr := do
  let views := (← getThe SliceSt).1
  match e with
  | .assign l r =>
    let descriptors := views.map (·.1)
    let origins := (← getThe SliceSt).2.1
    let readonly := descriptors ++ origins
    let forbidden := match l with
      | .name x => descriptors.contains x ||
          (origins.contains x && !r.calldataPlace origins)
      | _ => l.sliceTarget readonly
    if forbidden then return sliceRefuse "written or rebound through a calldata local"
    return e
  | .opAssign _ l _ | .incDec _ l =>
    if l.sliceTarget ((views.map (·.1)) ++ (← getThe SliceSt).2.1) then
      return sliceRefuse "written or rebound through a calldata local"
    return e
  | .index v k =>
    if !sliceViewish views v then return e
    if v matches .call "#slice" _ then
      return .call "#sliceAt" [slicePack views v, k]
    let some sv ← sliceViewOf? v | return sliceRefuse "whose base or bounds are not read here"
    return .index (.name sv.base) (.call "#sliceIndex" [sv.off, sv.len, k, .field (.name sv.base) "length"])
  | .ternary c a b => do
    let c ← c.mapM sliceNode
    let (a, b) ← sliceCond do pure (← a.mapM sliceNode, ← b.mapM sliceNode)
    return .ternary c a b
  | .binop op a b =>
    if !(op matches .and | .or) then return e
    let a ← a.mapM sliceNode
    let b ← sliceCond (b.mapM sliceNode)
    return .binop op a b
  | .field v "length" =>
    if !sliceViewish views v then return e
    if v matches .call "#slice" _ then return .call "#sliceLength" [slicePack views v]
    let some sv ← sliceViewOf? v | return sliceRefuse "whose base or bounds are not read here"
    return sv.len
  | .call "abi.decode" (v :: rest) =>
    if !sliceViewish views v then return e
    if v matches .call "#slice" _ then return .call "#sliceDecode" (slicePack views v :: rest)
    let some sv ← sliceViewOf? v | return sliceRefuse "whose base or bounds are not read here"
    return .call "abi.decode" (.call sliceViewName [.name sv.base, sv.off, sv.len] :: rest)
  | .call "#slice" _ => return .call "#sliceCopy" [slicePack views e]
  | .name x =>
    if (lookupBy x views).isSome then return .call "#sliceCopy" [slicePack views e]
    return e
  | e => pure e

end

mutual

/-- `RawStmt.sliceViews` on a block (above). -/
partial def sliceStmts (ss : List RawStmt) : SliceM (List RawStmt) := do
  let out ← ss.mapM fun s => do
    modifyThe SliceSt fun (vs, origins, k, _) => (vs, origins, k, #[])
    match s with
    | .declMemory T t (some (.call "#sliceBind" [e])) =>
      -- Ordinary aliases retain their typed memory path, but only a
      -- genuine calldata origin may introduce a new calldata name. A
      -- standalone memory place is not made calldata by this marker.
      if !sliceViewish (← getThe SliceSt).1 e then
        unless e.calldataPlace (← getThe SliceSt).2.1 do
          return [RawStmt.eval [sliceRefuse "ordinary alias without a known calldata origin"]]
        modifyThe SliceSt fun (vs, origins, k, pre) =>
          (vs.filter (·.1 != t), t :: origins.filter (· != t), k, pre)
        return [.declMemory T t (some e)]
      let opened ← match e with
        | .call "#slice" [b, i, j] => sliceOpen t b i j
        | e => sliceOpen t e (.num 0) (.call "#sliceEnd" [])
      match opened with
      | some v =>
        let (vs, origins, k, pre) ← getThe SliceSt
        set (σ := SliceSt) ((t, v) :: vs, origins.filter (· != t), k, (#[] : Array RawStmt))
        -- A private typed alias checks T (including widths) against the
        -- captured base. Do not bind the source name t to the whole base:
        -- a formula outside this source pass must not observe a false
        -- length/offset for a virtual view. All source reads use v instead.
        return pre.toList ++ [.declMemory T ("#slice$type$" ++ t) (some (.name v.base))]
      | none => return [RawStmt.eval [sliceRefuse "whose base or bounds are not read here"]]
    | s =>
      let out ← sliceOther s
      let names := s.declared?.toList ++ (match s with | .tupleDecl .. => s.binds | _ => [])
      modifyThe SliceSt fun (vs, origins, k, pre) =>
        (vs.filter (fun v => !names.contains v.1), origins.filter (!names.contains ·), k, pre)
      return out
  return out.flatten

/-- `sliceStmts` on a statement that opens no named view. -/
partial def sliceOther (s : RawStmt) : SliceM (List RawStmt) := do
  let state ← getThe SliceSt
  let descriptors := state.1.map (·.1)
  let readonly := descriptors ++ state.2.1
  let target (e : RawExpr) := match e with
    | .name x => descriptors.contains x
    | _ => e.sliceTarget readonly
  let through (e : RawExpr) := e.sliceTarget readonly
  let rebinding (l r : RawExpr) := match l with
    | .name x => descriptors.contains x ||
        (state.2.1.contains x && !r.calldataPlace state.2.1)
    | _ => through l
  -- Never turn a write target into a temporary materialization. A view
  -- descriptor is read only, including rebinding (not yet implemented).
  -- An ordinary calldata parameter can be rebound; its captured views keep
  -- their original base. Writes through either kind remain forbidden.
  let writes := s.exprs.any fun e => e.any fun
    | .assign l r => rebinding l r
    | .opAssign _ l _ | .incDec _ l => through l
    | _ => false
  let writes := writes || match s with
    | .assign l r => rebinding l r
    | .opAssign _ l _ | .incDec _ l | .delete l => through l
    | .assignIncDec x _ l | .assignPush x l => target x || through l
    | .pushOpAssign _ b _ | .pushIncDec _ b | .declStoragePush _ _ b
    | .declPush _ _ b => through b
    | .tupleAssign ts _ => ts.any (·.any through)
    | .call (.field b m) _ => (m == "push" || m == "pop") && through b
    | _ => false
  if writes then return [RawStmt.eval [sliceRefuse "written or rebound through a calldata local"]]
  -- a loop's condition is read on each iteration: a view read there
  -- checked in place
  let loop := s matches .whileLoop .. | .doWhile .. | .loop .. | .forLoop ..
  let s ← if loop then sliceCond (s.mapExprsM (·.mapM sliceNode))
    else s.mapExprsM (·.mapM sliceNode)
  let pre := (← getThe SliceSt).2.2.2
  -- a loop's condition is read again on each iteration: no slice opened in it
  if !pre.isEmpty && loop then
    return [RawStmt.eval [sliceRefuse "opened in a loop's condition"]]
  let u ← getThe (Bool × Bool)
  let s ← s.mapBlocksM fun b => do
    let (vs, origins, k, pre) ← getThe SliceSt
    if s matches .unchecked _ then set (σ := Bool × Bool) (true, u.2)
    let b ← sliceStmts b
    set (σ := Bool × Bool) u
    let (_, _, k', _) ← getThe SliceSt
    set (σ := SliceSt) (vs, origins, max k k', pre)
    pure b
  return pre.toList ++ [s]

end

/-- **A body's calldata slices read as views** (above). Ordinary alias
origins are supplied only by the declaring function's calldata parameters;
standalone raw programs have none. Explicit slice descriptors keep their
existing native behavior, including memory-backed interpreter examples. -/
def RawStmt.sliceViews (ss : List RawStmt) (calldataRoots : List String := []) : List RawStmt :=
  ((sliceStmts ss).run' (false, false)).run' ([], calldataRoots.eraseDups, 0, #[])

/-- Open an inline view at the expression's evaluation position. -/
def inlineSliceOpen (t : String) (e : RawExpr) : Except String (SliceView × List RawStmt) := do
  if let .call "#sliceDesc" [.name base, off, fin] := e then
    return ({ base, off, fin }, [])
  let .call "#sliceRaw" [b, i, j] := e | throw "internal: a slice descriptor"
  let (v, (_, _, _, pre)) := ((sliceOpen t b i j).run' (false, false)).run ([], [], 0, #[])
  let some v := v | throw "an inline calldata slice cannot be opened"
  pure (v, pre.toList)

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
    -- each function once a round: a function called twice is not explored twice
    let next := (todo.filter (fun g => !seen.contains g && (lookupBy g funs).isSome)).eraseDups
    if next.isEmpty then break
    seen := seen ++ next
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

/-- A `catch` clause whose first statement binds the call's data (the marker
`expandTry` writes for `catch Error(string memory r)` and `catch (bytes
memory d)`): its kind, the declaration it is elaborated from, the rest. -/
partial def RawStmt.catchBinder? : List RawStmt → Option CatchKind × List RawStmt
  | .declMemory T x (some (.name n)) :: rest =>
    if n == "catch$reason" || n == "catch$data" then
      -- a name the clause does not read binds nothing: the clause as written
      if rest.any (·.anyDeep fun s => s.exprs.any (·.mentions x)) then
        (some (if n == "catch$reason" then .reason else .raw), .declMemory T x none :: rest)
      else (none, rest)
    else (none, .declMemory T x (some (.name n)) :: rest)
  | ss => (none, ss)

/-- A `catch` clause elaborated with its binder declared first, as
`Stmt.catchData` (`docs/semantic-gaps.md`, "Revert data"): the declaration's
local bound to the call's data, the rest of the clause its body. -/
def Blk.toCatchData {Γ ρ ps Γf : Ctx} (call : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf) (self : Bool) (kind : CatchKind) :
    Blk C Γ → Except String (Blk C Γ)
  | ⟨_, .cons (.declMem R x none _ _) rest⟩ =>
    if h : R = bytesR then
      pure ⟨Γ, .cons (.catchData call rets sargs sbody self kind x (h ▸ rest)) .nil⟩
    else throw s!"a `catch` clause binds `bytes memory` or `string memory`, not {Ty.toStr (.ref R)}"
  | _ => throw "internal: a `catch` binder elaborated to no declaration"

/-- A statement inside `checked { … }` or `ignoringOverflow { … }`: its
guard's statement first, the programs it holds guarded (`Stmt.guard`,
`Stmt.withOF`). -/
def SStmt.withOF (o : OFMode) (sf : Bool) (s : SStmt C) : SProg C :=
  match s.s.guard with
  | none => [⟨s.Γ, s.Γ', s.s.withOF o sf⟩]
  | some g => [.of s.Γ (o.guardStmt g sf), ⟨s.Γ, s.Γ', s.s.withOF o sf⟩]

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
  | _, .hash _ b _ => b.vars ns
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

end Solidity
