import Solidity.Calculus.RuleSyntax.Schemas

/-!
# The rule syntax, printed

The delaborators that print the notation back: programs, terms, updates
and formulas.

A piece of `Calculus/RuleSyntax.lean`, whose docstring describes the whole.
-/

namespace Solidity

/-! ## Printing the notation (delaborators)

Each `pp…` function walks a Lean `Expr` and builds syntax of the grammar
above; Lean's formatter prints it.  The walk first computes (`whnf`), so a
lowered schema variable, `P ++ ω` and the like print as what they compute
to.  A subterm the walk does not recognise prints as `‹…›`. -/

section Print
open Lean Meta PrettyPrinter Delaborator SubExpr
set_option hygiene false

@[category_parenthesizer dl_fml] def dl_fml.parenthesizer : CategoryParenthesizer
  | prec => Parenthesizer.maybeParenthesize `dl_fml false
      (fun stx => Unhygienic.run `(dl_fml| ($(⟨stx⟩)))) prec
      (Parenthesizer.parenthesizeCategoryCore `dl_fml prec)

@[category_parenthesizer dl_term] def dl_term.parenthesizer : CategoryParenthesizer
  | prec => Parenthesizer.maybeParenthesize `dl_term false
      (fun stx => Unhygienic.run `(dl_term| ($(⟨stx⟩)))) prec
      (Parenthesizer.parenthesizeCategoryCore `dl_term prec)

@[category_parenthesizer sol_expr] def sol_expr.parenthesizer : CategoryParenthesizer
  | prec => Parenthesizer.maybeParenthesize `sol_expr false
      (fun stx => Unhygienic.run `(sol_expr| ($(⟨stx⟩)))) prec
      (Parenthesizer.parenthesizeCategoryCore `sol_expr prec)

register_option pp.sol.dl : Bool := {
  defValue := true
  descr := "print statements, formulas, taclets and sequents in the calculus's \
            notation, rather than as constructor applications"
}

def ppOn : MetaM Bool := return pp.sol.dl.get (← getOptions)

register_option pp.sol.key : Bool := {
  defValue := false
  descr := "print terms in KeY's long forms: `consr(p, f)` for `p.f`, `consr(p, at(i))` for \
            `p[i]`, `find(storage, consr(p, size))` for `p.length`, `read(m, i, f)`, \
            `write(m, i, f, v)`, `storeSt`/`selectSt`/`self` in the ledger (`#taclet` sets it)"
}

/-- Whether terms print in KeY's long forms (`pp.sol.key`). -/
def keyOn : MetaM Bool := return pp.sol.key.get (← getOptions)

register_option pp.sol.reduce : Bool := {
  defValue := true
  descr := "the notation's printers compute (`whnf`) each term before they print it; \
            `tm{ … }` prints a term as it is written, with this off"
}

def nameIdent (s : String) : Ident := mkIdent (Name.mkSimple s)

/-- Lean's own printing of `e`, with this notation off. -/
def escapeTerm (e : Lean.Expr) : MetaM Lean.Term :=
  withOptions (fun o => pp.sol.dl.set o false) (PrettyPrinter.delab e)

partial def listElems? (es : Lean.Expr) : MetaM (Option (Array Lean.Expr)) := do
  let mut out := #[]
  let mut cur ← whnf es
  repeat
    if cur.isAppOfArity ``List.nil 1 then return some out
    unless cur.isAppOfArity ``List.cons 3 do return none
    let args := cur.getAppArgs
    out := out.push args[1]!
    cur ← whnf args[2]!
  return some out

/-- The name of a free variable. -/
def fvarName? (e : Lean.Expr) : MetaM (Option String) := do
  let .fvar fv := (← instantiateMVars e).consumeMData | return none
  return some (← fv.getUserName).eraseMacroScopes.toString

/-- A string, or the name of a string variable. -/
def nameOf? (e : Lean.Expr) : MetaM (Option String) := do
  if let some n ← fvarName? e then return some n
  match (← whnf (← instantiateMVars e)).consumeMData with
  | .lit (.strVal s) => return some s
  | _ => return none

/-- A closed natural number. -/
def natOf? (e : Lean.Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  if let some n ← (evalNat e).run then return some n
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return none
  try return some (← unsafe evalExpr Nat (mkConst ``Nat) e) catch _ => return none

/-- A closed integer. -/
def intOf? (e : Lean.Expr) : MetaM (Option Int) := do
  let e ← instantiateMVars e
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return none
  try return some (← unsafe evalExpr Int (mkConst ``Int) e) catch _ => return none

/-- The spelling of `.fresh b k` by the `FreshNames` in scope. -/
def freshName (b : String) (k : Nat) : MetaM String := do
  let fn ← synthInstance (mkConst ``Solidity.FreshNames)
  unsafe evalExpr String (mkConst ``String)
    (mkApp3 (mkConst ``Solidity.FreshNames.name) fn (toExpr b) (toExpr k))

/-- A variable: `x`, `se1` (as `FreshNames` spells it), or `se` for a taclet's
fresh `.fresh "se" k`. -/
def ppVar? (e : Lean.Expr) : MetaM (Option Ident) := do
  if let some n ← fvarName? e then return some (nameIdent n)
  match_expr (← whnf (← instantiateMVars e)) with
  | Solidity.Var.user s => return (← nameOf? s).map nameIdent
  | Solidity.Var.fresh b k =>
    let some b ← nameOf? b | return none
    match ← natOf? k with
    | some n => return some (nameIdent (← freshName b n))
    | none =>
      -- a taclet's fresh `sp` beside a schema variable `sp` it reads: `sp'`
      let lctx ← getLCtx
      let mut x := b
      while (lctx.findFromUserName? (Name.mkSimple x)).isSome do x := x ++ "'"
      return some (nameIdent x)
  | _ => return none

/-! ### Programs

The builders `Calculus/PrintStmt.lean`'s printers of the scoped syntax use. -/

def binopSym? (op : Lean.Expr) : MetaM (Option String) := do
  if (← fvarName? op).isSome then return some "⊕"
  let op ← whnf op
  return (BinOp.all.find? (toExpr · == op)).map BinOp.sym

/-- `a ⊕ b` in the program grammar: the node the parser makes of `a ⊕ b` for
an operator of the table (`BinOp.ofSym?`), else the schema operator `⊕`. -/
def mkBinExpr (sym : String) (a b : TSyntax `sol_expr) : MetaM (TSyntax `sol_expr) := do
  if (BinOp.ofSym? sym).isSome then
    if let .ok t := Lean.Parser.runParserCategory (← getEnv) `sol_expr s!"a {sym} b" then
      if t.getNumArgs == 3 then
        return ⟨Syntax.node .none t.getKind #[a, mkAtom sym, b]⟩
  `(sol_expr| $a ⊕ $b)

/-- `b.f`: one dotted name when `b` is a name, as the parser reads it. -/
def dotExpr (b : TSyntax `sol_expr) (f : String) : MetaM (TSyntax `sol_expr) :=
  match b with
  | `(sol_expr| $x:ident) => `(sol_expr| $(mkIdent (x.getId.str f)):ident)
  | _ => `(sol_expr| $b . $(nameIdent f):ident)

/-- A Solidity type, as written: `uint`, `Person`, `uint[]`, `mapping(uint => Person)`. -/
partial def ppTy (e : Lean.Expr) : MetaM (TSyntax `sol_ty) := do
  if let some n ← fvarName? e then return ← `(sol_ty| $(nameIdent n):ident)
  let T := nameIdent "T"
  match_expr (← whnf e) with
  | Ty.prim p => ppPrim p
  | Ty.ref R => ppRef R
  | _ => `(sol_ty| $T:ident)
where
  ppPrim (p : Lean.Expr) : MetaM (TSyntax `sol_ty) := do
    if (← fvarName? p).isSome then return ← `(sol_ty| T)
    match_expr (← whnf p) with
    | PrimTy.uint => `(sol_ty| uint)
    | PrimTy.int => `(sol_ty| int)
    | PrimTy.bool => `(sol_ty| bool)
    | _ => `(sol_ty| T)
  ppRef (R : Lean.Expr) : MetaM (TSyntax `sol_ty) := do
    if (← instantiateMVars R).hasFVar then return ← `(sol_ty| T)
    match_expr (← whnf R) with
    | RefTy.struct s =>
      if (← fvarName? s).isSome then return ← `(sol_ty| T)
      let some s ← nameOf? s | `(sol_ty| T)
      `(sol_ty| $(nameIdent s):ident)
    | RefTy.array E => `(sol_ty| $(← ppTy E):sol_ty[])
    | RefTy.fixed E n =>
      let some n ← natOf? n | `(sol_ty| T)
      `(sol_ty| $(← ppTy E):sol_ty[$(Syntax.mkNumLit (toString n)):num])
    | RefTy.mapping K V => `(sol_ty| mapping($(← ppPrim K) => $(← ppTy V)))
    | _ => `(sol_ty| T)

/-- `l++`, `−−l` and the rest; `l⊕⊕` for a schema operator. -/
def ppIncDec (op : Lean.Expr) (l : TSyntax `sol_expr) : MetaM (Option (TSyntax `sol_stmt)) := do
  if (← fvarName? op).isSome then return some (← `(sol_stmt| $l:sol_expr ⊕⊕))
  match_expr (← whnf op) with
  | IncDec.postInc => return some (← `(sol_stmt| $l:sol_expr ++))
  | IncDec.preInc => return some (← `(sol_stmt| ++ $l:sol_expr))
  | IncDec.postDec => return some (← `(sol_stmt| $l:sol_expr −−))
  | IncDec.preDec => return some (← `(sol_stmt| −− $l:sol_expr))
  | _ => return none

/-- `l += r`, `l -= r` and the rest; `l ⊕= r` for a schema operator. -/
def ppCompound (op : Lean.Expr) (l r : TSyntax `sol_expr) : MetaM (Option (TSyntax `sol_stmt)) := do
  if (← fvarName? op).isSome then return some (← `(sol_stmt| $l:sol_expr ⊕= $r:sol_expr))
  match_expr (← whnf op) with
  | BinOp.add => return some (← `(sol_stmt| $l:sol_expr += $r:sol_expr))
  | BinOp.sub => return some (← `(sol_stmt| $l:sol_expr -= $r:sol_expr))
  | BinOp.mul => return some (← `(sol_stmt| $l:sol_expr *= $r:sol_expr))
  | BinOp.div => return some (← `(sol_stmt| $l:sol_expr /= $r:sol_expr))
  | BinOp.mod => return some (← `(sol_stmt| $l:sol_expr %= $r:sol_expr))
  | _ => return none

/-! ### Terms -/

def escapeDl (e : Lean.Expr) : MetaM (TSyntax `dl_term) := do `(dl_term| ‹$(← escapeTerm e):term›)

/-- `p` where a member or an index follows it: `p[i]@S` in parentheses, since
its storage `S` would take the `.f` or `[j]` after it. -/
def recvTerm (b : TSyntax `dl_term) : MetaM (TSyntax `dl_term) :=
  match b with
  | `(dl_term| $_:dl_term[$_:dl_term]@$_:dl_term) => `(dl_term| ($b))
  | _ => pure b

/-- `p.f`, dotted when `p` is a name. -/
def dotTerm (b : TSyntax `dl_term) (f : String) : MetaM (TSyntax `dl_term) := do
  match b with
  | `(dl_term| $x:ident) => `(dl_term| $(mkIdent (x.getId.str f)):ident)
  | _ => `(dl_term| $(← recvTerm b) . $(nameIdent f):ident)

/-- The type a concrete allocation carries, which `dl!{ … }` needs to read
`addM(m, T)` and `newArr(T, n)` back: `Person`, `uint[]`, `Token[3]`.  A rule's
`R` gives none: the rule table writes `addM(m)`, the type being the
statement's. -/
partial def allocTy? (R : Lean.Expr) : MetaM (Option (TSyntax `dl_term)) := do
  let R ← instantiateMVars R
  if R.hasFVar then return none
  let elem (E : Lean.Expr) : MetaM (Option (TSyntax `dl_term)) := do
    match_expr (← whnf E) with
    | Ty.prim p =>
      let T? : Option String ← match_expr (← whnf p) with
        | PrimTy.uint => pure (some "uint")
        | PrimTy.int => pure (some "int")
        | PrimTy.bool => pure (some "bool")
        | _ => pure none
      let some T := T? | return none
      return some (← `(dl_term| $(nameIdent T):ident))
    | Ty.ref R' => allocTy? R'
    | _ => return none
  match_expr (← whnf R) with
  | RefTy.struct s =>
    let .lit (.strVal s) := (← whnf s).consumeMData | return none
    return some (← `(dl_term| $(nameIdent s):ident))
  | RefTy.array E =>
    let some E ← elem E | return none
    return some (← `(dl_term| $E:dl_term[]))
  | RefTy.fixed E n =>
    let some E ← elem E | return none
    let some n ← natOf? n | return none
    return some (← `(dl_term| $E:dl_term[$(Syntax.mkNumLit (toString n)):num]))
  | _ => return none

def mkBinTerm (sym : String) (a b : TSyntax `dl_term) : MetaM (TSyntax `dl_term) :=
  match sym with
  | "+" => `(dl_term| $a + $b) | "-" => `(dl_term| $a - $b) | "/" => `(dl_term| $a / $b)
  | "*" => `(dl_term| $a * $b) | "%" => `(dl_term| $a % $b)
  | "&&" => `(dl_term| $a && $b) | "||" => `(dl_term| $a || $b)
  | "==" => `(dl_term| ($a == $b))
  | "±" => `(dl_term| $a ± $b)
  | _ => `(dl_term| $a ⊕ $b)

/-- The term of `t ⊕ u` with a concrete operator: `+`, `-`, `*`, `/` have
term syntax at `uint`, `&&`, `||` at `bool` and `==` at any type (the types
they read back at: `ppTermS` escapes the others); the other operators escape
(`‹…›`). -/
def termOpSym? (op : Lean.Expr) : MetaM (Option String) := do
  if (← fvarName? op).isSome then return some "⊕"
  if op.isAppOfArity ``IncDec.binOp 1 then
    if (← fvarName? op.appArg!).isSome then return some "±"
  match_expr (← whnf op) with
  | BinOp.add => return "+"
  | BinOp.sub => return "-"
  | BinOp.div => return "/"
  | BinOp.mul => return "*"
  | BinOp.mod => return "%"
  | BinOp.and => return "&&"
  | BinOp.or => return "||"
  | BinOp.eqB => return "=="
  | _ => return none

/-- A variable of a term sort, by its name, where a term prints as it is
written (`tm{ … }`, `pp.sol.reduce false`, whose names are such variables). -/
def tmVar? (e : Lean.Expr) : MetaM (Option (TSyntax `dl_term)) := do
  if pp.sol.reduce.get (← getOptions) then return none
  let some n ← fvarName? e | return none
  return some (← `(dl_term| $(nameIdent n):ident))

/-- `p[i]`, KeY's `consr(p, at(i))`. -/
def elemTerm (p i : TSyntax `dl_term) : MetaM (TSyntax `dl_term) := do
  if ← keyOn then `(dl_term| consr($p, at($i))) else `(dl_term| $(← recvTerm p):dl_term[$i:dl_term])

/-- The push positions of the array `p`: its length as a path, as the value
read in `storage`, and the slot past the end — `p.length`, `p.length` and
`p[p.length]`, KeY's `consr(p, size)`, `find(storage, consr(p, size))` and
`consr(p, at(find(storage, consr(p, size))))`. -/
def lenTerms (p : TSyntax `dl_term) :
    MetaM (TSyntax `dl_term × TSyntax `dl_term × TSyntax `dl_term) := do
  if ← keyOn then
    let path ← `(dl_term| consr($p, size))
    let val ← `(dl_term| find(storage, $path))
    return (path, val, ← `(dl_term| consr($p, at($val))))
  let p ← recvTerm p
  let len ← match p with
    | `(dl_term| $x:ident) => `(dl_term| $(mkIdent (x.getId.str "length")):ident)
    | _ => `(dl_term| $p . $(nameIdent "length"):ident)
  return (len, len, ← `(dl_term| $p[$len]))

/-! ### Updates and formulas -/

/-- A quantifier's type, as the specification writes it. -/
def primName? (p : Lean.Expr) : MetaM (Option String) := do
  match_expr (← whnf p) with
  | PrimTy.uint => return "uint"
  | PrimTy.int => return "int"
  | PrimTy.bool => return "bool"
  | _ => return none

/-- A formula that is a Lean variable, or the coercion of one (`↑φ` for
`φ : Post C`, `Chains.lean`): its name, which reads back as `‹φ›` does.  Not
an inaccessible one (`φ✝`): its bare name would read back as another variable,
so it stays `‹φ✝›`. -/
def fmlVar? (e : Lean.Expr) : MetaM (Option Ident) := do
  let e := (← instantiateMVars e).consumeMData
  let x ← match e.getAppFn with
    | .const f _ => match ← getCoeFnInfo? f with
      | some i => pure (if e.getAppNumArgs == i.numArgs then e.getArg! i.coercee else e)
      | none => pure e
    | _ => pure e
  let .fvar fv := x.consumeMData | return none
  let n : Lean.Name ← fv.getUserName
  if n.hasMacroScopes || n.isInaccessibleUserName then return none
  return (← fvarName? x).map nameIdent

/-! ### The delaborators

Each stands aside (`failure`, and Lean prints the term its own way) when all
it would print is one `‹…›`, and `⊨ᶠ`, `⊧` when it is a name: `⊨ᶠ φ`. -/

/-- Printed as `‹…›` as a whole. -/
def isEscape (s : Syntax) : Bool := s[0].isToken "‹"

/-- Only a full application: `Fml.modal m P` alone is a function. -/
def fullApp : DelabM Unit := do
  let e ← getExpr
  let some c := e.getAppFn.constName? | failure
  let info ← getConstInfoCtor c
  guard (e.getAppNumArgs == info.numParams + info.numFields)

/-- Whether `e` has at most `n` nodes (shared ones counted each time). -/
partial def sizeAtMost (n : Nat) (e : Lean.Expr) : Bool :=
  (go e n).isSome
where
  /-- The fuel left once `e` is counted, if any is. -/
  go (e : Lean.Expr) (fuel : Nat) : Option Nat := do
    if fuel == 0 then none
    match e with
    | .app f a => go a (← go f (fuel - 1))
    | .mdata _ b => go b fuel
    | .lam _ t b _ | .forallE _ t b _ => go b (← go t (fuel - 1))
    | .letE _ t v b _ => go b (← go v (← go t (fuel - 1)))
    | .proj _ _ b => go b (fuel - 1)
    | _ => some (fuel - 1)

/-- The largest term `tm{ … }` prints; a larger one prints as Lean prints it. -/
def tmCutoff : Nat := 2000

end Print

end Solidity
