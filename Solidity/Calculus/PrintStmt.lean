import Solidity.Calculus.DelabErase

/-!
# Printing scoped statements, blocks, premises and formulas

The printer of the scoped syntax (`Syntax/Scoped.lean`, `Calculus/Fml.lean`)
read from its `Expr`, schema variables and all: `ppStmtS`, `ppProgS`,
`ppBlockS`, `ppExprS`, `ppPremiseS`, `ppFmlS`.  It builds the syntax
`RuleSyntax.lean`'s `ppStmt`/`ppExpr`/`ppProg?`/`ppFml` and `RuleKit`'s
`ppPremise?` build from the erasure, with their builders (`ppVar?`, `ppTy`,
`mkBinExpr`, `dotExpr`, `ppIncDec`, `ppUpd`, `ppTerm`), so the KeY text is the
same: no statement, block or premise is erased to `Surface` on the way.
Terms and updates still go through `Delab.tr` to `Surface.Tm`/`Surface.Upd`,
the closer's IR (`Calculus/DelabErase.lean`).

**The name-stack walker** (the API a reader of the scoped syntax uses, the
SolKey reader's port among them): the names of the context a part is read
in are a stack `ns` (innermost first) of `Var` terms, the ones the binders
carry.
* A position (`idxName`) is its `Idx.here`/`.there` chain into the stack; a
  free variable of a scoped type (a schema variable) is itself, under any
  number of `.there`, `up` and weakenings, and prints as its user name.
* `declLocal`, `declStorage`, `declMem` and a call's return variables push
  their name (`Delab.stmtOutNames`); `Args`, `Binders`, `CodeBinder`,
  `Upd.decl`, `Fml.all`, `Fml.bind` and `Premise.bind` push theirs where
  they bind.
* A block is a list of pieces (`SPiece`, `progPiecesS`): a statement with
  the stack it is read at, a program variable spliced in, a block end, or a
  part that does not compute.  A block `{ … }` is its statements; a scope's
  end (`pop .capture`, an update's pops, a hidden binder) prints as nothing,
  a block's end in a formula's frames as `}` (`blockEndName`, which
  `Calculus/Delab.lean`'s `fixBlockEnds` turns into the token).

The option `pp.sol.twinCheck` makes the delaborators print both ways (this
printer and the erasure's) and fail with an error where they differ
(`twinCompare`), until the erasure goes (W8.4 of `docs/intrinsic.md`).
-/

namespace Solidity

open Lean Meta

register_option pp.sol.twinCheck : Bool := {
  defValue := false
  descr := "the scoped printers also print through the erasure (`Delab.tr`) and fail with an \
            error where the two differ"
}

namespace Delab

section Print
set_option hygiene false

/-! ## The name stack -/

/-- The name of the position `e` from the names `ns` (innermost first): the
`Var` its binder gave it; a schema variable itself (its user name prints);
`unknownVar` (`_`) for a position past the stack or that does not
compute. -/
partial def idxName (ns : List Expr) (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData
  if e.isFVar then return e
  let e ← whnf e
  if e.isAppOf ``Idx.here then return ns.headD unknownVar
  if e.isAppOf ``Idx.there then return ← idxName ns.tail e.appArg!
  if e.isFVar then return e
  return unknownVar

/-- An option of a scoped part, as its erasure has it: `some x`, or nothing
(a variable or a stuck option prints as `none`, as `Delab.trArg` erases
it). -/
def optSome? (o : Expr) : MetaM (Option Expr) := do
  let o ← whnf o
  if o.isAppOfArity ``Option.some 2 then return some o.appArg!
  return none

/-- Binders as `(type, name)` pairs in the order they are bound, and their
names innermost first, when they compute. -/
partial def bindersS? (bs : Expr) : MetaM (Option (Array (Expr × Expr) × List Expr)) := do
  let bs ← whnf bs
  if bs.isAppOf ``Binders.nil then return some (#[], [])
  unless bs.isAppOfArity ``Binders.snoc 4 do return none
  let some (xs, names) ← bindersS? (bs.getArg! 1) | return none
  let x := bs.getArg! 3
  return some (xs.push (bs.getArg! 2, x), x :: names)

/-- The printer's state: the erasure's twins (what `Delab.tr` reads, for
terms and updates), and whether a block's end in a formula's frames
prints (`}`). -/
structure PEnv where
  tr : Env := {}
  blockEnds : Bool := false

abbrev PrM := ReaderT PEnv MetaM

/-- `Delab.tr`'s monad, run on the printer's twins. -/
def runTr {α : Type} (x : TrM α) : PrM α := do x.run (← read).tr

/-! ## Blocks as pieces -/

/-- A piece of a block. -/
inductive SPiece where
  /-- A statement, read at the names `ns`. -/
  | stmt (ns : List Expr) (s : Expr)
  /-- A program variable spliced in: `P;`, or the rest `..ω`. -/
  | var (P : Expr)
  /-- A block's end in a formula's frames: `}`. -/
  | blockEnd
  /-- A part that does not compute. -/
  | stuck (P : Expr)

instance : Inhabited SPiece := ⟨.blockEnd⟩

def SPiece.isStmt : SPiece → Bool
  | .stmt .. | .blockEnd => true
  | _ => false

mutual

/-- The pieces of a block read at `ns`, and the names it leaves. -/
partial def progPiecesS (ns : List Expr) (P : Expr) : MetaM (Array SPiece × List Expr) := do
  let P := (← instantiateMVars P).consumeMData
  if P.isFVar then return (#[.var P], ns)
  -- a block read under one local more (`Prog.up`): itself
  if let some n := P.getAppFn.constName? then
    if isUp n && P.getAppNumArgs > 0 && P.appArg!.isFVar then return ← progPiecesS ns P.appArg!
  if let some P' := wkUp? P then return ((← progPiecesS ns.tail P').1, ns)
  let P ← whnf P
  if let some P' := wkUp? P then return ((← progPiecesS ns.tail P').1, ns)
  if P.isAppOf ``Prog.cons then
    let args := P.getAppArgs
    let (ss, ms) ← stmtPiecesS ns args[4]!
    let (rest, ms) ← progPiecesS ms args[5]!
    return (ss ++ rest, ms)
  if P.isAppOf ``Prog.nil then return (#[], ns)
  return (#[.stuck P], ns)

/-- A statement's pieces (a block's statements, spliced) and the names it
leaves. -/
partial def stmtPiecesS (ns : List Expr) (s : Expr) : MetaM (Array SPiece × List Expr) := do
  let s := (← instantiateMVars s).consumeMData
  if s.isFVar then return (#[.stmt ns s], ns)
  -- a hole filled declares nothing; read before `whnf` unfolds its `fill`
  if holeFills.any (s.isAppOf ·.1) then return (#[.stmt ns s], ns)
  let s ← whnf s
  if s.isAppOf ``Stmt.block then
    let (ps, _) ← progPiecesS ns s.appArg!
    return (ps, ns)
  return (#[.stmt ns s], ← stmtOutNames ns s)

end

/-- The pieces of a block that is an argument (a branch, a premise's
block), read at `ns`: a variable, a block read with one local more (`up`),
or the block's statements. -/
partial def progExprPieces (ns : List Expr) (P : Expr) : MetaM (Array SPiece) := do
  let P := (← instantiateMVars P).consumeMData
  if P.isFVar then return #[.var P]
  if let some P' := wkUp? P then return ← progExprPieces ns.tail P'
  if let some n := P.getAppFn.constName? then
    if isUp n && P.getAppNumArgs > 0 then return ← progExprPieces ns.tail P.appArg!
    if n == ``Prog.nil || n == ``Prog.cons then return (← progPiecesS ns P).1
  let P' ← whnf P
  if P' == P then return #[.stuck P]
  progExprPieces ns P'

/-- The statements frames hold, a block's end where one ends (when block ends
print), and the names of the postcondition's context. -/
partial def framePiecesS (ns : List Expr) (κ : Expr) : PrM (Array SPiece × List Expr) := do
  let κ := (← instantiateMVars κ).consumeMData
  if κ.isFVar then return (#[.var κ], ns)
  let κ ← whnf κ
  let args := κ.getAppArgs
  if κ.isAppOf ``Frames.seq then
    let (ps, ms) ← progPiecesS ns args[4]!
    let (qs, ms) ← framePiecesS ms args[5]!
    return (ps ++ qs, ms)
  if κ.isAppOf ``Frames.pop then
    let b ← whnf args[4]!
    let d ← extDepth args[5]!
    let (qs, ms) ← framePiecesS (ns.drop d) args[6]!
    if (← read).blockEnds && b.isConstOf ``BlockKind.block then return (#[.blockEnd] ++ qs, ms)
    return (qs, ms)
  if κ.isAppOf ``Frames.drop then
    return ← framePiecesS (← thinNames ns args[4]!) args[5]!
  if κ.isAppOf ``Frames.nil then return (#[], ns)
  return (#[.stuck κ], ns)

/-! ## Expressions -/

/-- A program expression of any sort read at `ns` (`ppExpr` of its
erasure); indices and proofs are not shown. -/
partial def ppExprS (ns : List Expr) (e : Expr) : MetaM (TSyntax `sol_expr) := do
  let e := (← instantiateMVars e).consumeMData
  if let some n ← fvarName? e then return ← `(sol_expr| $(nameIdent n):ident)
  if let some n := e.getAppFn.constName? then
    if isUp n && e.getAppNumArgs > 0 then return ← ppExprS ns.tail e.appArg!
  let escape := do `(sol_expr| ‹$(← escapeTerm e):term›)
  let var (i : Expr) := do
    let some x ← ppVar? (← idxName ns i) | escape
    `(sol_expr| $x:ident)
  let name (r : Expr) := do
    let some r ← nameOf? r | escape
    `(sol_expr| $(nameIdent r):ident)
  let field (b f : Expr) := do
    let some f ← nameOf? f | escape
    dotExpr (← ppExprS ns b) f
  let index (b k : Expr) := do
    `(sol_expr| $(← ppExprS ns b):sol_expr[$(← ppExprS ns k):sol_expr])
  match_expr (← whnf e) with
  | Simple.lit _ _ _ n _ =>
    let some n ← intOf? n | escape
    if n < 0 then `(sol_expr| -$(Syntax.mkNumLit (toString n.natAbs)):num)
    else `(sol_expr| $(Syntax.mkNumLit (toString n)):num)
  | Simple.bool _ _ b =>
    match_expr (← whnf b) with
    | Bool.true => `(sol_expr| true)
    | Bool.false => `(sol_expr| false)
    | _ => escape
  | Simple.local _ _ _ i => var i
  | Simple.env _ _ _ k _ =>
    match_expr (← whnf k) with
    | EnvKey.msgSender => `(sol_expr| msg.sender)
    | EnvKey.msgValue => `(sol_expr| msg.value)
    | EnvKey.timestamp => `(sol_expr| block.timestamp)
    | EnvKey.selfBalance => `(sol_expr| address(this).balance)
    | EnvKey.selfAddress => `(sol_expr| address(this))
    | _ => escape
  | SPath.alias _ _ _ i => var i
  | SPath.loc _ _ _ l => ppExprS ns l
  | Loc.root _ _ _ r _ => name r
  | Loc.field _ _ _ _ b f _ => field b f
  | Loc.index _ _ _ _ _ _ b i => index b i
  | MPath.var _ _ _ i _ => var i
  | MPath.loc _ _ _ l => ppExprS ns l
  | MLoc.field _ _ _ _ b f _ => field b f
  | MLoc.index _ _ _ _ _ b i => index b i
  | Val.simple _ _ _ s => ppExprS ns s
  | Val.read _ _ _ l => ppExprS ns l
  | Val.readMem _ _ _ l => ppExprS ns l
  | Val.binop _ _ _ _ op _ _ a b =>
    let some sym ← binopSym? op | escape
    mkBinExpr sym (← ppExprS ns a) (← ppExprS ns b)
  | Val.unop _ _ _ _ op _ _ a =>
    if (← fvarName? op).isSome then return ← `(sol_expr| ⊖$(← ppExprS ns a))
    match_expr (← whnf op) with
    | UnOp.neg => `(sol_expr| -$(← ppExprS ns a))
    | UnOp.not => `(sol_expr| !$(← ppExprS ns a))
    | UnOp.bnot => `(sol_expr| ~$(← ppExprS ns a))
    | _ => escape
  | Val.ternary _ _ _ c a b =>
    `(sol_expr| $(← ppExprS ns c) ? $(← ppExprS ns a) : $(← ppExprS ns b))
  | Val.len _ _ _ _ b _ => dotExpr (← ppExprS ns b) "length"
  | Val.mlen _ _ _ _ b _ => dotExpr (← ppExprS ns b) "length"
  | MRhs.newArr _ _ R n _ => `(sol_expr| new $(← ppTy.ppRef R):sol_ty ( $(← ppExprS ns n) ))
  | NewLhs.store _ _ _ l => ppExprS ns l
  | NewLhs.mem _ _ _ l => ppExprS ns l
  | Src.val _ _ _ v => ppExprS ns v
  | Src.copy _ _ _ p _ => ppExprS ns p
  | ARhs.path _ _ _ p => ppExprS ns p
  | MRhs.alias _ _ _ p => ppExprS ns p
  | MRhs.copy _ _ _ p _ => ppExprS ns p
  | MSrc.val _ _ _ v => ppExprS ns v
  | MSrc.ref _ _ _ p => ppExprS ns p
  | OpLoc.local _ _ _ i => var i
  | OpLoc.root _ _ _ r _ => name r
  | OpLoc.field _ _ _ _ b f _ => field b f
  | OpLoc.index _ _ _ _ _ _ b i => index b i
  | OpLoc.mfield _ _ _ _ b f _ => field b f
  | OpLoc.mindex _ _ _ _ _ b i => index b i
  | _ => escape

/-- A call's callee and its arguments (`Args`, in the order they are bound,
each read at the caller's `ns`), printed. -/
partial def ppCallPartsS (ns : List Expr) (f args : Expr) :
    MetaM (Option (TSyntax `sol_expr × Array (TSyntax `sol_expr))) := do
  let some f ← nameOf? f | return none
  let fe ← `(sol_expr| $(mkIdent (Lean.Name.mkSimple f)):ident)
  let rec go (as : Expr) : MetaM (Option (Array (TSyntax `sol_expr))) := do
    let as ← whnf as
    if as.isAppOf ``Args.nil then return some #[]
    unless as.isAppOfArity ``Args.snoc 7 do return none
    let some xs ← go (as.getArg! 3) | return none
    return some (xs.push (← ppExprS ns (as.getArg! 6)))
  let some xs ← go args | return none
  return some (fe, xs)

/-! ## Statements and blocks -/

/-- The name of an erased statement's head, the scoped one's: what
`Taclet.labelledBy` reads (`Stmt.ite` is `Surface.Stmt.ite` there). -/
def labelHead (s : Expr) : Lean.Name :=
  match s.getAppFn.constName? with
  | some n => if (`Solidity.Stmt).isPrefixOf n then
      n.replacePrefix `Solidity.Stmt `Solidity.Surface.Stmt else n
  | none => .anonymous

/-- Whether the syntax `stx` has the identifier `x`. -/
partial def hasIdent (x : Lean.Name) (stx : Syntax) : Bool :=
  (stx.isIdent && stx.getId == x) || stx.getArgs.any (hasIdent x)

mutual

partial def ppStmtS (ns : List Expr) (e : Expr) : PrM (TSyntax `sol_stmt) := do
  let e := (← instantiateMVars e).consumeMData
  let escape := do `(sol_stmt| ‹$(← escapeTerm e):term›)
  -- a hole that is a schema variable, filled: `lhs = e`, as the rule line writes it
  if holeFills.any (e.isAppOfArity ·.1 5) then
    if let some h ← fvarName? (← stripUps (e.getArg! 3)) then
      return ← `(sol_stmt| $(nameIdent h):ident = $(← ppExprS ns (e.getArg! 4)))
  -- a statement schema variable `s`
  if let some n ← fvarName? e then return ← `(sol_stmt| $(nameIdent n):ident)
  if let some n := e.getAppFn.constName? then
    if isUp n && e.getAppNumArgs > 0 then return ← ppStmtS ns.tail e.appArg!
  let var? (i : Expr) : MetaM (Option Ident) := do ppVar? (← idxName ns i)
  match_expr (← whnf e) with
  | Stmt.assign _ _ _ l r => `(sol_stmt| $(← ppExprS ns l):sol_expr = $(← ppExprS ns r):sol_expr)
  | Stmt.rebind _ _ _ i r =>
    let some x ← var? i | escape
    let r := (← instantiateMVars r).consumeMData
    if let some n ← fvarName? r then return ← `(sol_stmt| $x:ident = $(nameIdent n):ident)
    match_expr (← whnf r) with
    | ARhs.push _ _ _ b _ => `(sol_stmt| $x:ident = $(← ppExprS ns b):sol_expr .push())
    | _ => `(sol_stmt| $x:ident = $(← ppExprS ns r):sol_expr)
  | Stmt.assignLocal _ _ _ i r =>
    let some x ← var? i | escape
    `(sol_stmt| $x:ident = $(← ppExprS ns r):sol_expr)
  | Stmt.declLocal _ _ p x init =>
    let some x ← ppVar? x | escape
    let T ← ppTy.ppPrim p
    match ← optSome? init with
    | none => `(sol_stmt| $T:sol_ty $x:ident)
    | some v => `(sol_stmt| $T:sol_ty $x:ident = $(← ppExprS ns v):sol_expr)
  | Stmt.declStorage _ _ R x init =>
    let some x ← ppVar? x | escape
    let T ← ppTy.ppRef R
    match ← optSome? init with
    | none => `(sol_stmt| $T:sol_ty storage $x:ident)
    | some r =>
      let r := (← instantiateMVars r).consumeMData
      if r.isFVar then return ← `(sol_stmt| $T:sol_ty storage $x:ident = $(← ppExprS ns r):sol_expr)
      match_expr (← whnf r) with
      | ARhs.push _ _ _ b _ =>
        `(sol_stmt| $T:sol_ty storage $x:ident = $(← ppExprS ns b):sol_expr .push())
      | _ => `(sol_stmt| $T:sol_ty storage $x:ident = $(← ppExprS ns r):sol_expr)
  | Stmt.declMem _ _ R x init _ _ =>
    let some x ← ppVar? x | escape
    let T ← ppTy.ppRef R
    match ← optSome? init with
    | none => `(sol_stmt| $T:sol_ty memory $x:ident)
    | some r => `(sol_stmt| $T:sol_ty memory $x:ident = $(← ppExprS ns r):sol_expr)
  | Stmt.rebindMem _ _ _ i r =>
    let some x ← var? i | escape
    `(sol_stmt| $x:ident = $(← ppExprS ns r):sol_expr)
  | Stmt.assignFromMem _ _ _ l p =>
    `(sol_stmt| $(← ppExprS ns l):sol_expr = $(← ppExprS ns p):sol_expr)
  | Stmt.assignMem _ _ _ l r =>
    `(sol_stmt| $(← ppExprS ns l):sol_expr = $(← ppExprS ns r):sol_expr)
  | Stmt.opAssign _ _ _ op _ _ l r =>
    let l ← ppExprS ns l
    let r ← ppExprS ns r
    if (← fvarName? op).isSome then return ← `(sol_stmt| $l:sol_expr ⊕= $r:sol_expr)
    match_expr (← whnf op) with
    | BinOp.add => `(sol_stmt| $l:sol_expr += $r:sol_expr)
    | BinOp.sub => `(sol_stmt| $l:sol_expr -= $r:sol_expr)
    | BinOp.mul => `(sol_stmt| $l:sol_expr *= $r:sol_expr)
    | BinOp.div => `(sol_stmt| $l:sol_expr /= $r:sol_expr)
    | BinOp.mod => `(sol_stmt| $l:sol_expr %= $r:sol_expr)
    | _ => escape
  | Stmt.incDec _ _ _ op _ l =>
    let some s ← ppIncDec op (← ppExprS ns l) | escape
    pure s
  | Stmt.assignIncDec _ _ _ i op _ l _ =>
    let some x ← var? i | escape
    let l ← ppExprS ns l
    if (← fvarName? op).isSome then return ← `(sol_stmt| $x:ident = $l:sol_expr ⊕⊕)
    match_expr (← whnf op) with
    | IncDec.postInc => `(sol_stmt| $x:ident = $l:sol_expr ++)
    | IncDec.preInc => `(sol_stmt| $x:ident = ++ $l:sol_expr)
    | IncDec.postDec => `(sol_stmt| $x:ident = $l:sol_expr −−)
    | IncDec.preDec => `(sol_stmt| $x:ident = −− $l:sol_expr)
    | _ => escape
  | Stmt.push _ _ _ b v _ =>
    match ← optSome? v with
    | none => `(sol_stmt| $(← ppExprS ns b):sol_expr .push())
    | some a => `(sol_stmt| $(← ppExprS ns b):sol_expr .push( $(← ppExprS ns a) ))
  | Stmt.pop _ _ _ b => `(sol_stmt| $(← ppExprS ns b):sol_expr .pop())
  | Stmt.transfer _ _ r a => `(sol_stmt| $(← ppExprS ns r):sol_expr .transfer( $(← ppExprS ns a) ))
  | Stmt.send _ _ i r a =>
    let some x ← var? i | escape
    `(sol_stmt| $x:ident = $(← ppExprS ns r):sol_expr .send( $(← ppExprS ns a) ))
  | Stmt.delete _ _ _ l => `(sol_stmt| delete $(← ppExprS ns l):sol_expr)
  | Stmt.deleteMem _ _ _ p _ => `(sol_stmt| delete $(← ppExprS ns p):sol_expr)
  | Stmt.assignNew _ _ R l n _ =>
    `(sol_stmt| $(← ppExprS ns l):sol_expr = new $(← ppTy.ppRef R):sol_ty ( $(← ppExprS ns n) ))
  | Stmt.ite _ _ _ _ c thn els =>
    if (← progExprPieces ns els).isEmpty then
      `(sol_stmt| if ($(← ppExprS ns c)) $(← ppBlockS ns thn):sol_block)
    else
      `(sol_stmt| if ($(← ppExprS ns c)) $(← ppBlockS ns thn):sol_block
        else $(← ppBlockS ns els):sol_block)
  | Stmt.require _ _ c => `(sol_stmt| require($(← ppExprS ns c)))
  | Stmt.assert _ _ c => `(sol_stmt| assert($(← ppExprS ns c)))
  | Stmt.revert _ _ => `(sol_stmt| revert())
  | Stmt.call _ _ _ _ _ _ f args ret body =>
    -- KeY's `fbs` (`ic` under `pp.sol.ic`): a call whose parts are all schema variables
    if ← [f, args, ret, body].allM fun x => return (← instantiateMVars x).consumeMData.isFVar then
      return ← if (← getOptions).getBool `pp.sol.ic then `(sol_stmt| ic) else `(sol_stmt| fbs)
    let some (fe, xs) ← ppCallPartsS ns f args | escape
    let ret ← whnf ret
    let mut res : Option Ident := none
    if ret.isAppOfArity ``CallRet.val 4 then
      if let some y ← optSome? (ret.getArg! 3) then res ← var? y
    else if ret.isAppOfArity ``CallRet.rets 3 then
      if (← bindersS? (ret.getArg! 2)).isNone then return ← escape
    else unless ret.isAppOfArity ``CallRet.none 1 || ret.isAppOfArity ``CallRet.mem 5 do
      return ← escape
    match res, xs.toList with
    | none, [] => `(sol_stmt| $fe:sol_expr ( ))
    | none, [a] => `(sol_stmt| $fe:sol_expr ( $a:sol_expr ))
    | none, a :: bs => `(sol_stmt| $fe:sol_expr ( $a:sol_expr, $(bs.toArray),* ))
    | some y, [] => `(sol_stmt| $y:ident = $fe:sol_expr ( ))
    | some y, bs => `(sol_stmt| $y:ident = $fe:sol_expr ( $(bs.toArray),* ))
  | Stmt.tryCall _ _ _ _ _ _ _ _ c rets ok err code pnc other =>
    let c := (← instantiateMVars c).consumeMData
    let rets := (← instantiateMVars rets).consumeMData
    let code := (← instantiateMVars code).consumeMData
    -- the names `ok` and `panic` read: the returned values, the code
    let mut rNames : List Expr := []
    unless rets.isFVar do
      let some (_, names) ← bindersS? rets | return ← escape
      rNames := names
    let mut cNames : List Expr := []
    unless code.isFVar do
      let code' ← whnf code
      if code'.isAppOfArity ``CodeBinder.some 1 then cNames := [code'.appArg!]
      else unless code'.isAppOf ``CodeBinder.none do return ← escape
    if let some cn ← fvarName? c then
      -- KeY's schema: `try call returns (rets) body catch Error errorBody …`
      let some code ← fvarName? code | return ← escape
      let catches : Array (TSyntax `sol_catch) := #[
        ← `(sol_catch| catch Error $(← ppBlockS ns err):sol_block),
        ← `(sol_catch| catch Panic($(nameIdent code):ident) $(← ppBlockS (cNames ++ ns) pnc):sol_block),
        ← `(sol_catch| catch $(← ppBlockS ns other):sol_block)]
      let call ← `(sol_expr| $(nameIdent cn):ident)
      let okB ← ppBlockS (rNames ++ ns) ok
      let some r ← fvarName? rets |
        return ← `(sol_stmt| try $call:sol_expr $okB:sol_block $catches:sol_catch*)
      let r ← `(sol_tparam| $(nameIdent r):ident)
      return ← `(sol_stmt| try $call:sol_expr returns ($r) $okB:sol_block $catches:sol_catch*)
    if c.isFVar then return ← escape
    let some call ← ppExtCallS ns c | escape
    if rets.isFVar then return ← escape
    let some (rs, _) ← bindersS? rets | escape
    let mut ps : Array (TSyntax `sol_tparam) := #[]
    for (p, x) in rs do
      let some x ← ppVar? x | return ← escape
      ps := ps.push (← `(sol_tparam| $(← ppTy.ppPrim p):sol_ty $x:ident))
    let code ← match cNames with
      | [x] => do
        let some x ← ppVar? x | return ← escape
        `(sol_tparam| uint $x:ident)
      | _ => `(sol_tparam| uint)
    let catches : Array (TSyntax `sol_catch) := #[
      ← `(sol_catch| catch Error(string memory) $(← ppBlockS ns err):sol_block),
      ← `(sol_catch| catch Panic($code) $(← ppBlockS (cNames ++ ns) pnc):sol_block),
      ← `(sol_catch| catch $(← ppBlockS ns other):sol_block)]
    let okB ← ppBlockS (rNames ++ ns) ok
    if ps.isEmpty then
      `(sol_stmt| try $call:sol_expr $okB:sol_block $catches:sol_catch*)
    else
      `(sol_stmt| try $call:sol_expr returns ($ps,*) $okB:sol_block $catches:sol_catch*)
  | Stmt.loop _ _ _ a c body =>
    let w ← `(sol_stmt| while ($(← ppExprS ns c)) $(← ppBlockS ns body):sol_block)
    -- the annotation: none for a schema variable (`ann`) and for `.unwind 0`
    if (← instantiateMVars a).consumeMData.isFVar then return w
    let clause (k : String) (e : TSyntax `sol_expr) (s : TSyntax `sol_stmt) :
        MetaM (TSyntax `sol_stmt) := do
      `(sol_stmt| /// @custom:key $(Lean.mkIdent (Lean.Name.mkSimple k)):ident $e:sol_expr $s:sol_stmt)
    let name? (e : Expr) : MetaM (Option Ident) := do
      return (← fvarName? e).map fun x => Lean.mkIdent (Lean.Name.mkSimple x)
    let succName? (e : Expr) : MetaM (Option Ident) := do
      let_expr HAdd.hAdd _ _ _ _ x o := e | return none
      unless (← (evalNat o).run) == some 1 do return none
      name? x
    match_expr (← whnf a) with
    | LoopAnn.unwind _ _ k =>
      -- a taclet's bound: `n`, `n + 1`
      if let some x ← name? k then return ← clause "unwind" (← `(sol_expr| $x:ident)) w
      if let some x ← succName? k then
        return ← clause "unwind" (← `(sol_expr| $x:ident + 1)) w
      let some n ← (evalNat k).run | escape
      if n == 0 then return w
      clause "unwind" (← `(sol_expr| $(Lean.Syntax.mkNumLit (toString n)):num)) w
    | LoopAnn.inv _ _ I dec =>
      let w ← match ← optSome? dec with
        | some d => clause "decreases" (← ppExprS ns d) w
        | none => pure w
      clause "invariant" (← ppExprS ns I) w
    | _ => escape
  | _ => escape

/-- `address(a).f(e₁, …)`: an external call. -/
partial def ppExtCallS (ns : List Expr) (c : Expr) : PrM (Option (TSyntax `sol_expr)) := do
  let c ← whnf c
  unless c.isAppOfArity ``ExtCall.mk 5 do return none
  let a := c.getAppArgs
  let some f ← nameOf? a[3]! | return none
  let some args ← listElems? a[4]! | return none
  let mut es : Array (TSyntax `sol_expr) := #[]
  for x in args do
    let x ← whnf x
    unless x.isAppOfArity ``Sigma.mk 4 do return none
    es := es.push (← ppExprS ns x.getAppArgs[3]!)
  let recv ← `(sol_expr| address($(← ppExprS ns a[2]!)))
  return some (← `(sol_expr| $recv:sol_expr . $(nameIdent f):ident ( $es,* )))

/-- A piece printed alone. -/
partial def ppPieceS : SPiece → PrM (TSyntax `sol_stmt)
  | .stmt ns s => ppStmtS ns s
  | .blockEnd => `(sol_stmt| $(mkIdent blockEndName):ident)
  | .var P => do `(sol_stmt| ‹$(← escapeTerm P):term›)
  | .stuck P => do `(sol_stmt| ‹$(← escapeTerm P):term›)

/-- A statement after a call of several returns that assigns one of them
(`lo = se2;`): its target and the name of the return variable it reads. -/
partial def ppRetTargetS (t : SPiece) : PrM (Option (TSyntax `sol_expr × Expr)) := do
  let .stmt ns t := t | return none
  let local? (v : Expr) : MetaM (Option Expr) := do
    let_expr Val.simple _ _ _ s := (← whnf v) | return none
    let_expr Simple.local _ _ _ r := (← whnf s) | return none
    return some (← idxName ns r)
  let t := (← instantiateMVars t).consumeMData
  if t.isFVar then return none
  match_expr (← whnf t) with
  | Stmt.assignLocal _ _ _ i v =>
    let some x ← ppVar? (← idxName ns i) | return none
    let some r ← local? v | return none
    return some (← `(sol_expr| $x:ident), r)
  | Stmt.assign _ _ _ l src =>
    let_expr Src.val _ _ _ v := (← whnf src) | return none
    let some r ← local? v | return none
    return some (← ppExprS ns l, r)
  | Stmt.assignMem _ _ _ l src =>
    let_expr MSrc.val _ _ _ v := (← whnf src) | return none
    let some r ← local? v | return none
    return some (← ppExprS ns l, r)
  | _ => return none

/-- A call that returns to targets (`CallRet.rets`) and the statements after
it assigning them, as the one statement they are elaborated from (as
`ppTupleCall?` prints its erasure), with the number of pieces after the call
it covers. -/
partial def ppTupleCallS (s : SPiece) (rest : List SPiece) :
    PrM (Option (TSyntax `sol_stmt × Nat)) := do
  let .stmt ns s := s | return none
  let s := (← instantiateMVars s).consumeMData
  if s.isFVar then return none
  let_expr Stmt.call _ _ _ _ _ _ f args ret _ := (← whnf s) | return none
  let_expr CallRet.rets _ _ bs := (← whnf ret) | return none
  let some (rs, _) ← bindersS? bs | return none
  let rvs := rs.map (·.2)
  let rps := rs.map (·.1)
  let some (fe, xs) ← ppCallPartsS ns f args | return none
  let mut slots : Array (Option (TSyntax `sol_expr)) := Array.replicate rvs.size none
  let mut start := 0
  let mut n := 0
  for t in rest do
    let some (tgt, r) ← ppRetTargetS t | break
    let mut hit : Option Nat := none
    for i in [start:rvs.size] do
      if ← isDefEq rvs[i]! r then
        hit := some i
        break
    let some i := hit | break
    slots := slots.set! i (some tgt)
    start := i + 1
    n := n + 1
  -- every value discarded, `(, ) = f(x);`: a call with targets still
  if n == 0 && rvs.size < 2 then return none
  let call ← `(sol_expr| $fe:sol_expr ( $xs,* ))
  -- none assigned but read after the call: the declarations they are,
  -- `(uint a, uint b) = f(x);`
  if n == 0 then
    let mut reads := false
    let mut names : Array Lean.Name := #[]
    for r in rvs do
      if let some x ← ppVar? r then names := names.push x.getId
    for t in rest do
      if reads then break
      let stx ← ppPieceS t
      if names.any (hasIdent · stx) then reads := true
    if reads then
      let mut decls : Array Syntax := #[]
      for i in [0:rvs.size] do
        let some x ← ppVar? rvs[i]! | return none
        decls := decls.push (mkNullNode #[(← ppTy.ppPrim rps[i]!).raw, x.raw])
      let groups := (decls.extract 1 decls.size).map fun d => mkNode groupKind #[mkAtom ",", d]
      return some (⟨mkNode ``Solidity.solTupleDecl
        #[mkAtom "(", decls[0]!, mkNullNode groups, mkAtom ")", mkAtom "=", call.raw]⟩, 0)
  if let #[some y] := slots then
    return some (← `(sol_stmt| $y:sol_expr = $call:sol_expr), n)
  let opt (x : Option (TSyntax `sol_expr)) : Syntax := mkNullNode ((x.map fun x => #[x.raw]).getD #[])
  let groups := (slots.extract 1 slots.size).map fun x => mkNode groupKind #[mkAtom ",", opt x]
  return some (⟨mkNode ``Solidity.solTupleAssign
    #[mkAtom "(", opt slots[0]!, mkNullNode groups, mkAtom ")", mkAtom "=", call.raw]⟩, n)

/-- A call returning a memory reference (`CallRet.mem`) and the statement
after it binding the return variable, as the one statement they are
elaborated from: `Person memory mv1 = choosePersonMem();`,
`m = choosePersonMem();` (as `ppMemCall?` prints their erasure). -/
partial def ppMemCallS (s t : SPiece) : PrM (Option (TSyntax `sol_stmt)) := do
  let .stmt ns s := s | return none
  let .stmt ns' t := t | return none
  let s := (← instantiateMVars s).consumeMData
  let t := (← instantiateMVars t).consumeMData
  if s.isFVar || t.isFVar then return none
  let_expr Stmt.call _ _ _ _ _ _ f args ret _ := (← whnf s) | return none
  let_expr CallRet.mem _ _ r _ _ := (← whnf ret) | return none
  -- the local `t` binds to `r`
  let bound (rhs : Expr) : MetaM Bool := do
    let_expr MRhs.alias _ _ _ p := (← whnf rhs) | return false
    let_expr MPath.var _ _ _ i _ := (← whnf p) | return false
    isDefEq r (← idxName ns' i)
  let some (fe, xs) ← ppCallPartsS ns f args | return none
  let call ← `(sol_expr| $fe:sol_expr ( $xs,* ))
  match_expr (← whnf t) with
  | Stmt.declMem _ _ R x init _ _ =>
    let some rhs ← optSome? init | return none
    unless ← bound rhs do return none
    let some x ← ppVar? x | return none
    return some (← `(sol_stmt| $(← ppTy.ppRef R):sol_ty memory $x:ident = $call:sol_expr))
  | Stmt.rebindMem _ _ _ i rhs =>
    unless ← bound rhs do return none
    let some x ← ppVar? (← idxName ns' i) | return none
    return some (← `(sol_stmt| $x:ident = $call:sol_expr))
  | _ => return none

/-- The statements of a block of pieces with no variable in it, a tuple
call and a memory call each as the one statement it is elaborated from (as
`ppProg?` prints the erasure); none if a variable or a stuck part is in
it. -/
partial def ppItemsS (ps : Array SPiece) : PrM (Option (Array (TSyntax `sol_stmt))) := do
  unless ps.all SPiece.isStmt do return none
  let mut out : Array (TSyntax `sol_stmt) := #[]
  let mut i := 0
  while i < ps.size do
    if let some (st, n) ← ppTupleCallS ps[i]! (ps.extract (i + 1) ps.size).toList then
      out := out.push st
      i := i + 1 + n
      continue
    if let (some s, some t) := (ps[i]?, ps[i + 1]?) then
      if let some st ← ppMemCallS s t then
        out := out.push st
        i := i + 2
        continue
    out := out.push (← ppPieceS ps[i]!)
    i := i + 1
  return some out

/-- A block with variables in it, `s :: P ++ ω`: its statements one by one
(a program variable as a statement, `P;`) and the rest `ω` when the block
ends in a variable (as `ppProgParts?` prints the erasure). -/
partial def ppPartsS (ps : Array SPiece) :
    PrM (Option (Array (TSyntax `sol_stmt) × Option Ident)) := do
  let mut out : Array (TSyntax `sol_stmt) := #[]
  for h : i in [0:ps.size] do
    match ps[i] with
    | .var P =>
      let some n ← fvarName? P | return none
      if i + 1 == ps.size then return some (out, some (nameIdent n))
      out := out.push (← `(sol_stmt| $(nameIdent n):ident))
    | .stuck _ => return none
    | p => out := out.push (← ppPieceS p)
  return some (out, none)

/-- A branch: `{ s₁; …; sₙ; }`, or the name of a schema variable, or a block
with one spliced in (`{ body; s; }`), from its pieces. -/
partial def ppBlockOf (ps : Array SPiece) : PrM (TSyntax `sol_block) := do
  if let #[.var P] := ps then
    if let some n ← fvarName? P then return ← `(sol_block| $(nameIdent n):ident)
  if let some ss ← ppItemsS ps then return ← `(sol_block| { $[$ss;]* })
  match ← ppPartsS ps with
  | some (ss, none) => `(sol_block| { $[$ss;]* })
  | _ =>
    let e := match ps.find? (· matches .stuck _ | .var _) with
      | some (.stuck P) | some (.var P) => P
      | _ => mkConst ``Unit.unit
    `(sol_block| ‹$(← escapeTerm e):term›)

/-- A block argument (a branch of an `if`, a loop's body) read at `ns`. -/
partial def ppBlockS (ns : List Expr) (P : Expr) : PrM (TSyntax `sol_block) := do
  ppBlockOf (← progExprPieces ns P)

end

/-- A block read at `ns`, its statements (`ppProg?` of its erasure). -/
def ppProgS (ns : List Expr) (P : Expr) : PrM (Option (Array (TSyntax `sol_stmt))) := do
  ppItemsS (← progExprPieces ns P)

/-- The statements of pieces with schema variables in them, a program
variable as a statement (`body;`), the rest `ω` too. -/
def progItemsS (ps : Array SPiece) : PrM (Option (Array (TSyntax `sol_stmt))) := do
  let some (ss, t) ← ppPartsS ps | return none
  match t with
  | some x => return some (ss.push (← `(sol_stmt| $x:ident)))
  | none => return some ss

/-! ## Formulas -/

/-- Whether an update read at `ns` prints (has an element: `Delab.updParts`'s
pieces, nothing erased), and the names of the context it leaves. -/
partial def updShape (ns : List Expr) (U : Expr) : MetaM (Bool × List Expr) := do
  let U ← whnf (← instantiateMVars U)
  let args := U.getAppArgs
  if U.isAppOf ``Upd.snoc then return (true, (← updShape ns args[3]!).2)
  if U.isAppOf ``Upd.decl then return (true, args[5]! :: (← updShape ns args[4]!).2)
  if U.isAppOf ``Upd.pop then
    let (b, ms) ← updShape ns args[4]!
    return (b, ms.drop (← extDepth args[5]!))
  if U.isAppOf ``Upd.drop then
    let (b, ms) ← updShape ns args[4]!
    return (b, ← thinNames ms args[5]!)
  if U.isAppOf ``Upd.nil then return (false, ns)
  return (true, ns)

/-- A formula as its erasure shows it, read at `ns`: the hidden binders and
the updates that print as nothing gone through, the rest computed.  A
postcondition variable (`↑φ`) and a schema variable stay. -/
partial def viewF (ns : List Expr) (e : Expr) : PrM (List Expr × Expr) := do
  let e := (← instantiateMVars e).consumeMData
  if e.isFVar then return (ns, e)
  if e.isAppOfArity `Solidity.Post.fml 3 then
    if (← instantiateMVars (e.getArg! 2)).consumeMData.getAppFn.isFVar then return (ns, e)
  if let some n := e.getAppFn.constName? then
    if isUp n && e.getAppNumArgs > 0 then return ← viewF ns.tail e.appArg!
  let e ← whnf e
  if e.isAppOfArity ``Fml.bind 6 then return ← viewF (e.getArg! 3 :: ns) (e.getArg! 5)
  if e.isAppOfArity ``Fml.upd 6 then
    let (shown, ms) ← updShape ns (e.getArg! 4)
    if !shown then return ← viewF ms (e.getArg! 5)
  return (ns, e)

/-- The erased term of a term read at `ns`. -/
def termS (ns : List Expr) (t : Expr) : PrM Expr := do
  instantiateMVars (← runTr (tr ns t))

/-- `defined(a) ∧ defined(b) ∧ a ≐ b`, which `Fml.eqD a b` unfolds to and
`a = b` prints: `a` and `b`, each with its names.  The two reads of a term
are the same when their erasures are (the same term at the same names, else
the erasures compared). -/
def eqDPartsS (ns : List Expr) (e : Expr) :
    PrM (Option ((List Expr × Expr) × (List Expr × Expr))) := do
  let (ns, e) ← viewF ns e
  let_expr Fml.and _ _ l r := e | return none
  let (nl, l) ← viewF ns l
  let_expr Fml.defined _ _ a := l | return none
  let (nr, r) ← viewF ns r
  let_expr Fml.and _ _ l' r' := r | return none
  let (nl', l') ← viewF nr l'
  let_expr Fml.defined _ _ b := l' | return none
  let (nr', r') ← viewF nr r'
  let_expr Fml.eq _ _ a' b' := r' | return none
  let same (n₁ : List Expr) (x : Expr) (n₂ : List Expr) (y : Expr) : PrM Bool := do
    let (x, y) := (← instantiateMVars x, ← instantiateMVars y)
    if x == y && n₁ == n₂ then return true
    return (← termS n₁ x) == (← termS n₂ y)
  unless ← same nl a nr' a' do return none
  unless ← same nl' b nr' b' do return none
  return some ((nl, a), (nl', b))

/-- A connective, which the operand of `¬`, `{U}` and `⟨P⟩` parenthesises. -/
def isConnectiveS (ns : List Expr) (e : Expr) : PrM Bool := do
  let (_, e') ← viewF ns e
  if e'.isAppOfArity ``Fml.imp 4 || e'.isAppOfArity ``Fml.all 5 then return true
  unless e'.isAppOfArity ``Fml.and 4 do return false
  return (← eqDPartsS ns e).isNone

/-- `¬(¬φ ∧ ¬ψ)`, which `φ ∨ ψ` spells: `φ` and `ψ`, with their names. -/
def orPartsS (ns : List Expr) (e : Expr) :
    PrM (Option ((List Expr × Expr) × (List Expr × Expr))) := do
  let (ns, e) ← viewF ns e
  let_expr Fml.not _ _ a := e | return none
  let (ns, a) ← viewF ns a
  let_expr Fml.and _ _ l r := a | return none
  let (nl, l) ← viewF ns l
  let_expr Fml.not _ _ φ := l | return none
  let (nr, r) ← viewF ns r
  let_expr Fml.not _ _ ψ := r | return none
  return some ((nl, φ), (nr, ψ))

/-- `¬(∀ T x; ¬φ)`, which `∃ T x; φ` spells: `x`, `T` and `φ` with its
names. -/
def exPartsS (ns : List Expr) (e : Expr) :
    PrM (Option (Expr × Expr × List Expr × Expr)) := do
  let (ns, e) ← viewF ns e
  let_expr Fml.not _ _ a := e | return none
  let (ns, a) ← viewF ns a
  let_expr Fml.all _ _ x p b := a | return none
  let x := x.consumeMData
  let (nb, b) ← viewF (x :: ns) b
  let_expr Fml.not _ _ φ := b | return none
  return some (x, p, nb, φ)

/-- `(φ → ψ) ∧ (ψ → φ)`, which `φ ↔ ψ` spells: `φ` and `ψ` with their names. -/
def iffPartsS (ns : List Expr) (e : Expr) :
    PrM (Option ((List Expr × Expr) × (List Expr × Expr))) := do
  let (ns, e) ← viewF ns e
  let_expr Fml.and _ _ l r := e | return none
  let (nl, l) ← viewF ns l
  let_expr Fml.imp _ _ φ ψ := l | return none
  let (nr, r) ← viewF ns r
  let_expr Fml.imp _ _ ψ' φ' := r | return none
  let (φ, ψ, φ', ψ') := (← instantiateMVars φ, ← instantiateMVars ψ, ← instantiateMVars φ',
    ← instantiateMVars ψ')
  return if φ == φ' && ψ == ψ' && nl == nr then some ((nl, φ), (nl, ψ)) else none

/-- The update of an `{U}` read at `ns`, erased (`Delab.updParts`), and the
names of the context it leaves. -/
def updS (ns : List Expr) (U : Expr) : PrM (TSyntax `dl_upd × List Expr) := do
  let (es, ms) ← runTr (updParts ns U)
  let c ← contractOf U
  return (← ppUpd (← runTr (updList c U es)), ms)

/-- A scoped formula read at `ns`, as `ppFml` prints its erasure. -/
partial def ppFmlS (ns : List Expr) (e : Expr) : PrM (TSyntax `dl_fml) := do
  let (ns, e) ← viewF ns e
  if let some x ← fmlVar? e then return ← `(dl_fml| $x:ident)
  let escape := do `(dl_fml| ‹$(← escapeTerm e):term›)
  let arg (ms : List Expr) (φ : Expr) : PrM (TSyntax `dl_fml) := do
    let s ← ppFmlS ms φ
    if ← isConnectiveS ms φ then `(dl_fml| ($s)) else pure s
  match_expr e with
  | Fml.tt _ _ => `(dl_fml| true)
  | Fml.not _ _ φ =>
    if (← viewF ns φ).2.isAppOfArity ``Fml.tt 2 then return ← `(dl_fml| false)
    if let some ((na, a), (nb, b)) ← orPartsS ns e then
      return ← `(dl_fml| $(← ppFmlS na a):dl_fml ∨ $(← ppFmlS nb b):dl_fml)
    if let some (x, p, na, a) ← exPartsS ns e then
      if let (some x, some T) := (← ppVar? x, ← primName? p) then
        return ← `(dl_fml| ∃ $(mkIdent (Name.mkSimple T)):ident $x:ident; $(← ppFmlS na a):dl_fml)
    `(dl_fml| ¬$(← arg ns φ):dl_fml)
  | Fml.eq _ _ a b =>
    `(dl_fml| $(← ppTerm (← termS ns a)):dl_term ≐ $(← ppTerm (← termS ns b)):dl_term)
  | Fml.defined _ _ t => `(dl_fml| defined($(← ppTerm (← termS ns t)):dl_term))
  | Fml.all _ _ x p φ =>
    let x := x.consumeMData
    let some xi ← ppVar? x | escape
    let some T ← primName? p | escape
    `(dl_fml| ∀ $(mkIdent (Name.mkSimple T)):ident $xi:ident; $(← ppFmlS (x :: ns) φ):dl_fml)
  | Fml.and _ _ φ ψ =>
    if let some ((na, a), (nb, b)) ← eqDPartsS ns e then
      let a ← termS na a
      let b ← termS nb b
      if let some (sym, l, r) ← Surface.cmpParts? a b then
        let l ← ppTerm l
        let r ← ppTerm r
        return ← match sym with
          | "<" => `(dl_fml| $l:dl_term < $r:dl_term)
          | "<=" => `(dl_fml| $l:dl_term <= $r:dl_term)
          | ">" => `(dl_fml| $l:dl_term > $r:dl_term)
          | _ => `(dl_fml| $l:dl_term >= $r:dl_term)
      return ← `(dl_fml| $(← ppTerm a):dl_term = $(← ppTerm b):dl_term)
    if let some ((na, a), (nb, b)) ← iffPartsS ns e then
      return ← `(dl_fml| $(← ppFmlS na a):dl_fml ↔ $(← ppFmlS nb b):dl_fml)
    let ψ' ← ppFmlS ns ψ
    let ψ' ← if (← viewF ns ψ).2.isAppOfArity ``Fml.imp 4 then `(dl_fml| ($ψ')) else pure ψ'
    `(dl_fml| $(← arg ns φ):dl_fml ∧ $ψ')
  | Fml.imp _ _ φ ψ => `(dl_fml| $(← arg ns φ):dl_fml → $(← ppFmlS ns ψ):dl_fml)
  | Fml.upd _ _ _ _ U φ =>
    let (u, ms) ← updS ns U
    `(dl_fml| $u:dl_upd $(← arg ms φ):dl_fml)
  | Fml.havoc _ _ φ => `(dl_fml| { havoc } $(← arg ns φ):dl_fml)
  | Fml.anon _ _ xs φ =>
    let some xs ← listElems? xs | escape
    let ids ← xs.mapM fun x => do ppVar? (← idxName ns (← whnf x).appArg!)
    if ids.any Option.isNone then return ← escape
    let ids : Array Ident := ids.filterMap id
    `(dl_fml| { anon($ids,*) } $(← arg ns φ):dl_fml)
  | Fml.modal _ _ _ _ m P κ φ =>
    let (ps, ms) ← progPiecesS ns P
    let (qs, ms) ← framePiecesS ms κ
    let items := ps ++ qs
    let body ← arg ms φ
    let m' ← whnf m
    let some ss ← ppItemsS items |
      if let #[.var P] := items then
        if let some n ← fvarName? P then
          let b ← `(sol_block| $(nameIdent n):ident)
          return ← match_expr m' with
            | Modality.diamond => `(dl_fml| ⟨ $b:sol_block ⟩ $body:dl_fml)
            | Modality.box => `(dl_fml| [ $b:sol_block ] $body:dl_fml)
            | _ => `(dl_fml| ⟨[ $b:sol_block ]⟩ $body:dl_fml)
      -- `⟨[ s; ..ω ]⟩ φ`: statements in front of the rest of the program
      let some (ss, t) ← ppPartsS items | escape
      match t with
      | some ω =>
        if (← fvarName? m).isSome then
          return ← `(dl_fml| ⟨[ $[$ss;]* .. $ω:ident ]⟩ $body:dl_fml)
        match_expr m' with
        | Modality.diamond => `(dl_fml| ⟨ $[$ss;]* .. $ω:ident ⟩ $body:dl_fml)
        | Modality.box => `(dl_fml| [ $[$ss;]* .. $ω:ident ] $body:dl_fml)
        | _ => escape
      | none =>
        match_expr m' with
        | Modality.diamond => `(dl_fml| ⟨ $[$ss;]* ⟩ $body:dl_fml)
        | Modality.box => `(dl_fml| [ $[$ss;]* ] $body:dl_fml)
        | _ => `(dl_fml| ⟨[ $[$ss;]* ]⟩ $body:dl_fml)
    match_expr m' with
    | Modality.diamond => `(dl_fml| ⟨ $[$ss;]* ⟩ $body:dl_fml)
    | Modality.box => `(dl_fml| [ $[$ss;]* ] $body:dl_fml)
    | _ => `(dl_fml| ⟨[ $[$ss;]* ]⟩ $body:dl_fml)
  | _ => escape

/-! ## Premises -/

/-- A scoped premise read at `ns`, as `ppPremise?` prints its erasure: its
goals labelled by `labels` (solkey's, `Taclet.branchLabels`), the blocks of
`branches` in the box's brackets when `box`. -/
partial def ppPremiseS (ns : List Expr) (e : Expr) (labels : List String := [])
    (box : Bool := false) : PrM (Option (TSyntax `dl_premise)) := do
  let lbl (i : Nat) : Option (TSyntax `str) := labels[i]?.map Syntax.mkStrLit
  let l0 := lbl 0
  let l1 := lbl 1
  let e := (← instantiateMVars e).consumeMData
  -- `expand_function_body(fbs)`: the statements a call of schema variables runs
  if e.isAppOf ``Premise.expandCall && e.getAppNumArgs ≥ 3 then
    let a := e.getAppArgs
    if [a[a.size - 3]!, a[a.size - 2]!, a.back!].all (·.consumeMData.isFVar) then
      let s ← if (← getOptions).getBool `pp.sol.ic then `(sol_stmt| expand_function_body(ic))
        else `(sol_stmt| expand_function_body(fbs))
      return some (← `(dl_premise| ⟨[ $s:sol_stmt; ]⟩))
  let unfold (ns : List Expr) (P : Expr) : PrM (Option (TSyntax `dl_premise)) := do
    let some ss ← ppProgS ns P | return none
    return some (← `(dl_premise| ⟨[ $[$ss;]* ]⟩))
  match_expr (← whnf e) with
  | Premise.update _ _ _ U =>
    let (u, _) ← updS ns U
    return some (← `(dl_premise| $u:dl_upd ⟨[ ]⟩))
  | Premise.unfold _ _ _ _ P _ => unfold ns P
  | Premise.inline _ _ _ _ P _ => unfold ns P
  | Premise.bind _ _ _ x _ P => unfold (x :: ns) P
  | Premise.split _ _ _ _ _ c c' P Q =>
    let c ← ppFmlS ns c
    let c' ← ppFmlS ns c'
    let P ← progExprPieces ns P
    let Q ← progExprPieces ns Q
    match ← ppItemsS P, ← ppItemsS Q with
    | some ts, some fs =>
      return some (← `(dl_premise| $[$l0:str :]? $c:dl_fml ⟹ ⟨[ $[$ts;]* ]⟩ ;
        $[$l1:str :]? $c':dl_fml ⟹ ⟨[ $[$fs;]* ]⟩))
    | _, _ =>
      return some (← `(dl_premise| $[$l0:str :]? $c:dl_fml ⟹ ⟨[ $(← ppBlockOf P) ]⟩ ;
        $[$l1:str :]? $c':dl_fml ⟹ ⟨[ $(← ppBlockOf Q) ]⟩))
  | Premise.check _ _ c =>
    let c ← ppFmlS ns c
    return some (← `(dl_premise| $[$l0:str :]? $c:dl_fml ⟹ ⟨[ ]⟩ ; $[$l1:str :]? $c:dl_fml))
  | Premise.done _ _ _ b =>
    match_expr (← whnf b) with
    | Bool.true => return some (← `(dl_premise| true))
    | Bool.false => return some (← `(dl_premise| false))
    | _ => return none
  | Premise.branches _ _ bs =>
    -- a goal per block, `"label": ∀ xs. ⟨[ P ]⟩` (`[ P ]` for a box-only taclet)
    let some bs ← listElems? bs | return none
    let mut out : Array (TSyntax `dl_branch) := #[]
    for h : i in [0:bs.size] do
      let l := lbl i
      let b ← whnf bs[i]
      unless b.isAppOfArity ``Branch.mk 6 do return none
      let xs := (← instantiateMVars (b.getArg! 4)).consumeMData
      -- the binders: a schema variable (`rets`), the `Panic` code's
      -- (`code.binders`), or none
      let (x?, names) ← do
        if let some n ← fvarName? xs then pure (some n, [])
        else if xs.isAppOf ``CodeBinder.binders && xs.getAppNumArgs > 0 &&
            xs.appArg!.consumeMData.isFVar then
          pure (← fvarName? xs.appArg!, [])
        else
          let some (pairs, names) ← bindersS? xs | return none
          unless pairs.isEmpty do return none
          pure (none, names)
      let blk ← ppBlockOf (← progPiecesS (names ++ ns) (b.getArg! 5)).1
      let x? := x?.map fun x => nameIdent x
      out := out.push (← if box then `(dl_branch| $[$l:str :]? $[∀ $x?:ident .]? [ $blk ])
        else `(dl_branch| $[$l:str :]? $[∀ $x?:ident .]? ⟨[ $blk ]⟩))
    let some b := out[0]? | return none
    if out.size < 2 then return none
    return some (← `(dl_premise| $b:dl_branch ; $[$(out.extract 1 out.size)];*))
  | Premise.cases _ _ fs us =>
    -- `"label": φ` for each formula, then `"label": {U} ⟨[ ]⟩` for each update
    let some fs ← listElems? fs | return none
    let some us ← listElems? us | return none
    let mut out : Array (TSyntax `dl_case) := #[]
    for h : i in [0:fs.size] do
      let l := lbl i
      out := out.push (← `(dl_case| $[$l:str :]? $(← ppFmlS ns fs[i]):dl_fml))
    for h : j in [0:us.size] do
      let l := lbl (fs.size + j)
      let (u, _) ← updS ns us[j]
      out := out.push (← `(dl_case| $[$l:str :]? $u:dl_upd ⟨[ ]⟩))
    let some c := out[0]? | return none
    if out.size < 2 then return none
    return some (← `(dl_premise| $c:dl_case ; $[$(out.extract 1 out.size)];*))
  | Premise.inv _ _ _ _ _ I _ _ U c c' _ hb P post =>
    let (es, ms) ← runTr (updParts ns U)
    let ks := ms.drop (← extDepth hb)
    let I ← ppFmlS ns I
    let c ← ppFmlS ms c
    let c' ← ppFmlS ms c'
    let post ← ppFmlS ks post
    let b ← ppBlockOf (← progPiecesS ks P).1
    let cE ← contractOf U
    let U' ← runTr (updList cE U es)
    if let some #[] ← listElems? U' then
      return some (← `(dl_premise| $[$l0:str :]? $I:dl_fml ; $[$l1:str :]? { anon($b) } ($I →
        $c:dl_fml ⟹ ⟨[ $b ]⟩ $post:dl_fml ; $c':dl_fml ⟹ ⟨[ ]⟩)))
    return some (← `(dl_premise| $[$l0:str :]? $I:dl_fml ; $[$l1:str :]? { anon($b) } ($I →
      $(← ppUpd U'):dl_upd ($c:dl_fml ⟹ ⟨[ $b ]⟩ $post:dl_fml ; $c':dl_fml ⟹ ⟨[ ]⟩))))
  | _ => return none

end Print

/-! ## Running it -/

/-- `k` with the printer's state for `e`: the twins of its schema variables
(`withTwins`, for the terms and updates `Delab.tr` erases), block ends
printed when `frames` (and `e` has a contract). -/
def withPrinter {α : Type} (e : Expr) (frames : Bool) (k : PrM α)
    (contract? : Option Expr := none) (schema : Bool := false) : MetaM α := do
  let ends ← if !frames then pure false else
    match contract? with
    | some _ => pure true
    | none => try (do let _ ← contractOf (← instantiateMVars e); pure true) catch _ => pure false
  withTwins e false (schema := schema) fun env => k.run { tr := env, blockEnds := ends }

/-- Whether the twin check is on (`pp.sol.twinCheck`). -/
def twinCheckOn : MetaM Bool := return pp.sol.twinCheck.get (← getOptions)

/-- Under `pp.sol.twinCheck`: an error where `new` (this printer's) and
`old` (the erasure's) print differently.  It is thrown, not only logged, so a
delaborator's difference shows in the printed text even where its messages
are dropped (a message's expressions are printed lazily). -/
def twinCompare (what : String) (new old : Option Syntax) (cat : Lean.Name := `term) :
    MetaM Unit := do
  let fmt (s : Option Syntax) : MetaM String := do
    match s with
    | some s =>
      try return toString ((← PrettyPrinter.ppCategory cat s).pretty 100000)
      catch _ => return "‹does not format›"
    | none => return "‹none›"
  let a ← fmt new
  let b ← fmt old
  unless a == b do
    let msg := m!"twin check ({what}): the scoped printer prints\n{a}\nthe erasure's\n{b}"
    logError msg
    throwError msg

end Delab

end Solidity
