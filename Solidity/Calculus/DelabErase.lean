import Solidity.Calculus.Rules
import Solidity.Calculus.RuleKit

/-!
# The printers' name stack

What the printers of the scoped terms and programs (`Calculus/PrintTerm.lean`,
`Calculus/PrintStmt.lean`, `Calculus/Delab.lean`) read off an `Expr` with
its schema variables free: the names a statement, a call or a frame end
leaves (`stmtOutNames`, `thinNames`, `extDepth`), a part read under `up`s
(`isUp`, `stripUps`, `wkUp?`), the lowering functions, and the scoped
families an escape must not name (`isScopedFamily`).

It imports the scoped rule table and `RuleKit` only, below the
delaborators, the sequent and the strategy (decision 53).  Until W9.7.1 it
also held `Delab.tr`, the erasure the SolKey reader read; that is deleted.
-/

namespace Solidity

open Lean Meta

namespace Delab

/-- Whether `n` names a scoped family: a term, a memory address term
(`MAddr.field`, `MAddr.at`), an update or its element, a formula, or a
position.  These are the families the erased twins named until W9.7.1.
`MAddr` is a namespace here, not a constant (the run's `MAddr` is not
imported), so it is quoted with one backtick. -/
def isScopedFamily (n : Lean.Name) : Bool :=
  [``Tm, `Solidity.MAddr, ``Upd, ``UpdElem, ``Fml, ``Idx].contains n

/-- A position that is no local the term declared. -/
def unknownVar : Expr := mkApp (mkConst ``Solidity.Var.user) (toExpr "_")

/-- The names of what a frame end by `h : Thin Γ Δ` keeps, from the names
`ns` of `Δ`; as many as it can read when `h` does not compute. -/
partial def thinNames (ns : List Expr) (h : Expr) : MetaM (List Expr) := do
  let h ← whnf h
  if h.isAppOf ``Thin.keep then return ns.headD unknownVar :: (← thinNames ns.tail h.appArg!)
  if h.isAppOf ``Thin.drop then return ← thinNames ns.tail h.appArg!
  return ns

/-- How many locals a scope end pops, when it computes. -/
partial def extDepth (e : Expr) : MetaM Nat := do
  let e ← whnf e
  if e.isAppOf ``Ext.push then return (← extDepth e.appArg!) + 1
  return 0

/-- The lowering functions (`Calculus/Lower.lean`). -/
def lowerFns : List Lean.Name :=
  [``Simple.lower, ``SPath.lower, ``Loc.lower, ``MPath.lower, ``MLoc.lower, ``Val.lower,
    ``Src.lower, ``MSrc.lower]

/-- A part of the program or a term, read with one local more on top:
`Val.up` and its kin (the one other `Solidity` name ending in `up` is a
theorem, `Wrote.up`, which no term heads). -/
def isUp (n : Lean.Name) : Bool := (`Solidity).isPrefixOf n && n.getString! == "up"

/-- A part under any number of `up`s: the part itself. -/
partial def stripUps (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData
  match e.getAppFn.constName? with
  | some n => if isUp n && e.getAppNumArgs > 0 then stripUps e.appArg! else return e
  | none => return e

/-- The contract of a scoped term, its type's first argument. -/
def contractOf (e : Expr) : MetaM Expr := do
  let ty ← whnfR (← inferType e)
  return ty.getArg! 0

/-- The names of binders, innermost first (`Binders.names`), when they
compute. -/
partial def bindersNames? (bs : Expr) : MetaM (Option (List Expr)) := do
  let bs ← whnf bs
  if bs.isAppOf ``Binders.nil then return some []
  if bs.isAppOfArity ``Binders.snoc 4 then
    let some xs ← bindersNames? (bs.getArg! 1) | return none
    return some (bs.getArg! 3 :: xs)
  return none

/-- The length of a context, when it computes. -/
partial def ctxLength? (Γ : Expr) : MetaM (Option Nat) := do
  let Γ ← whnf Γ
  if Γ.isAppOf ``List.nil then return some 0
  if Γ.isAppOfArity ``List.cons 3 then return (· + 1) <$> (← ctxLength? Γ.appArg!)
  return none

/-- The names of the context a call leaves its caller in
(`CallRet.outNames`). -/
def callOutNames (ns : List Expr) (ret : Expr) : MetaM (List Expr) := do
  let ret ← whnf ret
  match ret.getAppFn.constName? with
  | some ``CallRet.mem => return ret.getArg! 2 :: ns
  | some ``CallRet.rets => do
    if let some xs ← bindersNames? (ret.getArg! 2) then return xs ++ ns
    match ← ctxLength? (ret.getArg! 1) with
    | some n => return List.replicate n unknownVar ++ ns
    | none => return ns
  | _ => return ns

/-- The names a statement leaves: its declaration's on top. -/
def stmtOutNames (ns : List Expr) (s : Expr) : MetaM (List Expr) := do
  let s ← whnf s
  match s.getAppFn.constName? with
  | some ``Stmt.declLocal | some ``Stmt.declStorage => return s.getArg! 3 :: ns
  | some ``Stmt.declMem => return s.getArg! 3 :: ns
  | some ``Stmt.call => callOutNames ns (s.getArg! 8)
  | _ => return ns

/-- `(Prog.wk up P).2.2`, the unfolding of `Prog.up P` (a block read with
one local more on top), as a projection or an application: `P`. -/
def wkUp? (e : Expr) : Option Expr :=
  let snd? (e : Expr) (s : Lean.Name) (f : Lean.Name) : Option Expr :=
    match e.consumeMData with
    | .proj n 1 x => if n == s then some x.consumeMData else none
    | e => if e.isAppOfArity f 3 then some e.appArg!.consumeMData else none
  match snd? e ``Prod ``Prod.snd with
  | none => none
  | some x => match snd? x ``Sigma ``Sigma.snd with
    | none => none
    | some w =>
      let args := w.getAppArgs
      if w.isAppOf ``Prog.wk && args.size ≥ 3 then
        match args[args.size - 3]?.bind (·.getAppFn.constName?) with
        | some n => if isUp n then args.back? else none
        | none => none
      else none

/-- The name of the local a block's end prints as, before `fixBlockEnds`
turns it into `}`. -/
def blockEndName : Lean.Name := `core_block_end

end Delab

end Solidity
