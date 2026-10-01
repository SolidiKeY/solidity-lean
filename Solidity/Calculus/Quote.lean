import Solidity.Syntax
import Solidity.Update

/-!
# Quoting formulas back into Lean

A formula computed at compile time — by `dl[C]{ … }` reading one
(`Notation.lean`), or by `sol_symex` running the strategy on one
(`Symex.lean`) — has to become an `Expr` again to stand in a goal.  The
quoter is written by hand, as `Prog.quote` is, because a derived `ToExpr`
would spell the contract out instead of naming it: the result must mention
`StandardExample`, not its declarations, for the kernel to see that it is
the formula it started from.
-/

namespace Solidity

open Semantics

deriving instance Lean.ToExpr for Semantics.PrimVal

section Quote
open Lean (mkAppN mkConst toExpr)

variable {C : Contract} (c : Lean.Expr)

/-- A constant, quoted under its constructor's name. -/
def Op0.quote : Op0 s → Lean.Expr
  | .lit v => mkAppN (mkConst ``Term.lit) #[c, toExpr v]
  | .env k => mkAppN (mkConst ``Term.env) #[c, toExpr k]
  | .root r => mkAppN (mkConst ``PTerm.root) #[c, toExpr r]
  | .storage => mkAppN (mkConst ``STerm.storage) #[c]
  | .memory => mkAppN (mkConst ``MTerm.memory) #[c]

/-- A unary symbol over its quoted argument `x`. -/
def Op1.quote : Op1 a s → Lean.Expr → Lean.Expr
  | .unop op p, x => mkAppN (mkConst ``Term.unop) #[c, toExpr op, toExpr p, x]
  | .net, x => mkAppN (mkConst ``Term.net) #[c, x]
  | .netOf y, x => mkAppN (mkConst ``Term.netOf) #[c, toExpr y, x]
  | .field f, x => mkAppN (mkConst ``PTerm.field) #[c, x, toExpr f]
  | .next, x => mkAppN (mkConst ``PTerm.next) #[c, x]
  | .select r, x => mkAppN (mkConst ``STerm.select) #[c, x, toExpr r]
  | .sval, x => mkAppN (mkConst ``SValT.val) #[c, x]
  | .newArr R, x => mkAppN (mkConst ``SValT.newArr) #[c, toExpr R, x]
  | .alloc R, x => mkAppN (mkConst ``ITerm.alloc) #[c, x, toExpr R]
  | .mfield f, x => mkAppN (mkConst ``MAddr.field) #[c, x, toExpr f]
  | .addM R, x => mkAppN (mkConst ``MTerm.addM) #[c, x, toExpr R]
  | .mval, x => mkAppN (mkConst ``MValT.val) #[c, x]
  | .ref, x => mkAppN (mkConst ``MValT.ref) #[c, x]

/-- A binary symbol over its quoted arguments. -/
def Op2.quote : Op2 a b s → Lean.Expr → Lean.Expr → Lean.Expr
  | .binop op p, x, y => mkAppN (mkConst ``Term.binop) #[c, toExpr op, toExpr p, x, y]
  | .find, x, y => mkAppN (mkConst ``Term.find) #[c, x, y]
  | .len, x, y => mkAppN (mkConst ``Term.len) #[c, x, y]
  | .read, x, y => mkAppN (mkConst ``Term.read) #[c, x, y]
  | .mlen, x, y => mkAppN (mkConst ``Term.mlen) #[c, x, y]
  | .at, x, y => mkAppN (mkConst ``PTerm.at) #[c, x, y]
  | .delAt, x, y => mkAppN (mkConst ``STerm.delAt) #[c, x, y]
  | .pushSlot E, x, y => mkAppN (mkConst ``STerm.pushSlot) #[c, x, y, toExpr E]
  | .pop, x, y => mkAppN (mkConst ``STerm.pop) #[c, x, y]
  | .shrink, x, y => mkAppN (mkConst ``STerm.shrink) #[c, x, y]
  | .extend E, x, y => mkAppN (mkConst ``STerm.extend) #[c, x, y, toExpr E]
  | .sfind, x, y => mkAppN (mkConst ``SValT.find) #[c, x, y]
  | .copyMem, x, y => mkAppN (mkConst ``SValT.copyMem) #[c, x, y]
  | .iread, x, y => mkAppN (mkConst ``ITerm.read) #[c, x, y]
  | .copy, x, y => mkAppN (mkConst ``ITerm.copy) #[c, x, y]
  | .mat, x, y => mkAppN (mkConst ``MAddr.at) #[c, x, y]
  | .copySt, x, y => mkAppN (mkConst ``MTerm.copySt) #[c, x, y]

/-- A ternary symbol over its quoted arguments. -/
def Op3.quote : Op3 a b d s → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr
  | .ite, x, y, z => mkAppN (mkConst ``Term.ite) #[c, x, y, z]
  | .save, x, y, z => mkAppN (mkConst ``STerm.save) #[c, x, y, z]
  | .push, x, y, z => mkAppN (mkConst ``STerm.push) #[c, x, y, z]
  | .write, x, y, z => mkAppN (mkConst ``MTerm.write) #[c, x, y, z]

/-- A term, quoted under its constructors' names (`Term.find`, …), so that
it reads back as it was written. -/
def Tm.quote : Tm C s → Lean.Expr
  | .pvV x => mkAppN (mkConst ``Term.pv) #[c, toExpr x]
  | .pvP x => mkAppN (mkConst ``PTerm.pv) #[c, toExpr x]
  | .pvS x => mkAppN (mkConst ``STerm.pv) #[c, toExpr x]
  | .pvI x => mkAppN (mkConst ``ITerm.pv) #[c, toExpr x]
  | .app0 o => o.quote c
  | .app1 o x => o.quote c (x.quote)
  | .app2 o x y => o.quote c (x.quote) (y.quote)
  | .app3 o x y z => o.quote c (x.quote) (y.quote) (z.quote)

def IntOp.quote : IntOp → Lean.Expr
  | .add => mkConst ``IntOp.add
  | .sub => mkConst ``IntOp.sub

def UpdElem.quote : UpdElem C → Lean.Expr
  | .val x t => mkAppN (mkConst ``UpdElem.val) #[c, toExpr x, Tm.quote c t]
  | .path x p => mkAppN (mkConst ``UpdElem.path) #[c, toExpr x, Tm.quote c p]
  | .mref x i => mkAppN (mkConst ``UpdElem.mref) #[c, toExpr x, Tm.quote c i]
  | .storage s => mkAppN (mkConst ``UpdElem.storage) #[c, Tm.quote c s]
  | .store x s => mkAppN (mkConst ``UpdElem.store) #[c, toExpr x, Tm.quote c s]
  | .memory m => mkAppN (mkConst ``UpdElem.memory) #[c, Tm.quote c m]
  | .selfBalance op a => mkAppN (mkConst ``UpdElem.selfBalance) #[c, IntOp.quote op, Tm.quote c a]
  | .net r op a =>
    mkAppN (mkConst ``UpdElem.net) #[c, Tm.quote c r, IntOp.quote op, Tm.quote c a]
  | .saveNet x => mkAppN (mkConst ``UpdElem.saveNet) #[c, toExpr x]

def Upd.quote : List (UpdElem C) → Lean.Expr
  | [] => mkAppN (mkConst ``List.nil [0]) #[mkAppN (mkConst ``UpdElem) #[c]]
  | u :: U => mkAppN (mkConst ``List.cons [0])
      #[mkAppN (mkConst ``UpdElem) #[c], UpdElem.quote c u, Upd.quote U]

def Fml.quote : Fml C → Lean.Expr
  | .tt => mkAppN (mkConst ``Fml.tt) #[c]
  | .eq a b => mkAppN (mkConst ``Fml.eq) #[c, Tm.quote c a, Tm.quote c b]
  | .defined t => mkAppN (mkConst ``Fml.defined) #[c, Tm.quote c t]
  | .not φ => mkAppN (mkConst ``Fml.not) #[c, Fml.quote φ]
  | .and φ ψ => mkAppN (mkConst ``Fml.and) #[c, Fml.quote φ, Fml.quote ψ]
  | .imp φ ψ => mkAppN (mkConst ``Fml.imp) #[c, Fml.quote φ, Fml.quote ψ]
  | .upd m U φ => mkAppN (mkConst ``Fml.upd) #[c, toExpr m, Upd.quote c U, Fml.quote φ]
  | .modal m P φ => mkAppN (mkConst ``Fml.modal) #[c, toExpr m, Prog.quote c P, Fml.quote φ]
  | .havoc φ => mkAppN (mkConst ``Fml.havoc) #[c, Fml.quote φ]
  | .all x p φ => mkAppN (mkConst ``Fml.all) #[c, toExpr x, toExpr p, Fml.quote φ]

/-- The expression `Lean.mkConst n []`: the `c` a quoter takes for the
contract named `n`, when the quoter runs as compiled code (`evalExpr`). -/
def quoteConstName (n : Lean.Name) : Lean.Expr :=
  mkAppN (mkConst ``Lean.mkConst)
    #[toExpr n, mkAppN (mkConst ``List.nil [0]) #[mkConst ``Lean.Level]]

end Quote

end Solidity
