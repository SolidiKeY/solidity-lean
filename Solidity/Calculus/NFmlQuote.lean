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
  | .mtSt vs => mkAppN (mkConst ``STerm.mtSt) #[c, toExpr vs]

/-- A unary symbol over its quoted argument `x`. -/
def Op1.quote : Op1 a s → Lean.Expr → Lean.Expr
  | .unop op p, x => mkAppN (mkConst ``Term.unop) #[c, toExpr op, toExpr p, x]
  | .net, x => mkAppN (mkConst ``Term.net) #[c, x]
  | .netOf y, x => mkAppN (mkConst ``Term.netOf) #[c, toExpr y, x]
  | .delValue, x => mkAppN (mkConst ``Term.delValue) #[c, x]
  | .field f, x => mkAppN (mkConst ``PTerm.field) #[c, x, toExpr f]
  | .next, x => mkAppN (mkConst ``PTerm.next) #[c, x]
  | .select r, x => mkAppN (mkConst ``STerm.select) #[c, x, toExpr r]
  | .sval, x => mkAppN (mkConst ``SValT.val) #[c, x]
  | .newArr R, x => mkAppN (mkConst ``SValT.newArr) #[c, toExpr R, x]
  | .alloc R, x => mkAppN (mkConst ``ITerm.alloc) #[c, x, toExpr R]
  | .mfield f, x => mkAppN (mkConst ``Surface.MAddr.field) #[c, x, toExpr f]
  | .addM R, x => mkAppN (mkConst ``MTerm.addM) #[c, x, toExpr R]
  | .mval, x => mkAppN (mkConst ``MValT.val) #[c, x]
  | .ref, x => mkAppN (mkConst ``MValT.ref) #[c, x]
  | .wt vs, x => mkAppN (mkConst ``Term.wt) #[c, toExpr vs, x]

/-- A binary symbol over its quoted arguments. -/
def Op2.quote : Op2 a b s → Lean.Expr → Lean.Expr → Lean.Expr
  | .binop op p, x, y => mkAppN (mkConst ``Term.binop) #[c, toExpr op, toExpr p, x, y]
  | .find, x, y => mkAppN (mkConst ``Term.find) #[c, x, y]
  | .len, x, y => mkAppN (mkConst ``Term.len) #[c, x, y]
  | .read, x, y => mkAppN (mkConst ``Term.read) #[c, x, y]
  | .mlen, x, y => mkAppN (mkConst ``Term.mlen) #[c, x, y]
  | .at, x, y => mkAppN (mkConst ``PTerm.at) #[c, x, y]
  | .nextIn, x, y => mkAppN (mkConst ``PTerm.nextIn) #[c, x, y]
  | .delAt, x, y => mkAppN (mkConst ``STerm.delAt) #[c, x, y]
  | .pushSlot E, x, y => mkAppN (mkConst ``STerm.pushSlot) #[c, x, y, toExpr E]
  | .pop, x, y => mkAppN (mkConst ``STerm.pop) #[c, x, y]
  | .shrink, x, y => mkAppN (mkConst ``STerm.shrink) #[c, x, y]
  | .extend E, x, y => mkAppN (mkConst ``STerm.extend) #[c, x, y, toExpr E]
  | .sfind, x, y => mkAppN (mkConst ``SValT.find) #[c, x, y]
  | .copyMem, x, y => mkAppN (mkConst ``SValT.copyMem) #[c, x, y]
  | .iread, x, y => mkAppN (mkConst ``ITerm.read) #[c, x, y]
  | .copy, x, y => mkAppN (mkConst ``ITerm.copy) #[c, x, y]
  | .mat, x, y => mkAppN (mkConst ``Surface.MAddr.at) #[c, x, y]
  | .copySt, x, y => mkAppN (mkConst ``MTerm.copySt) #[c, x, y]

/-- A ternary symbol over its quoted arguments. -/
def Op3.quote : Op3 a b d s → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr
  | .ite, x, y, z => mkAppN (mkConst ``Term.ite) #[c, x, y, z]
  | .save, x, y, z => mkAppN (mkConst ``STerm.save) #[c, x, y, z]
  | .push, x, y, z => mkAppN (mkConst ``STerm.push) #[c, x, y, z]
  | .atIn, x, y, z => mkAppN (mkConst ``PTerm.atIn) #[c, x, y, z]
  | .write, x, y, z => mkAppN (mkConst ``MTerm.write) #[c, x, y, z]

/-- A term, quoted under its constructors' names (`Term.find`, …), so that
it reads back as it was written. -/
def Surface.Tm.quote : Surface.Tm C s → Lean.Expr
  | .pvV x => mkAppN (mkConst ``Term.pv) #[c, toExpr x]
  | .pvP x => mkAppN (mkConst ``PTerm.pv) #[c, toExpr x]
  | .pvS x => mkAppN (mkConst ``STerm.pv) #[c, toExpr x]
  | .pvI x => mkAppN (mkConst ``ITerm.pv) #[c, toExpr x]
  | .app0 o => o.quote c
  | .app1 o x => o.quote c (x.quote)
  | .app2 o x y => o.quote c (x.quote) (y.quote)
  | .app3 o x y z => o.quote c (x.quote) (y.quote) (z.quote)

def Surface.UpdElem.quote : Surface.UpdElem C → Lean.Expr
  | .val x t => mkAppN (mkConst ``Surface.UpdElem.val) #[c, toExpr x, Surface.Tm.quote c t]
  | .path x p => mkAppN (mkConst ``Surface.UpdElem.path) #[c, toExpr x, Surface.Tm.quote c p]
  | .unset x => mkAppN (mkConst ``Surface.UpdElem.unset) #[c, toExpr x]
  | .mref x i => mkAppN (mkConst ``Surface.UpdElem.mref) #[c, toExpr x, Surface.Tm.quote c i]
  | .storage s => mkAppN (mkConst ``Surface.UpdElem.storage) #[c, Surface.Tm.quote c s]
  | .store x s => mkAppN (mkConst ``Surface.UpdElem.store) #[c, toExpr x, Surface.Tm.quote c s]
  | .memory m => mkAppN (mkConst ``Surface.UpdElem.memory) #[c, Surface.Tm.quote c m]
  | .selfBalance op a => mkAppN (mkConst ``Surface.UpdElem.selfBalance) #[c, IntOp.quote op, Surface.Tm.quote c a]
  | .net r op a =>
    mkAppN (mkConst ``Surface.UpdElem.net) #[c, Surface.Tm.quote c r, IntOp.quote op, Surface.Tm.quote c a]
  | .pay r a => mkAppN (mkConst ``Surface.UpdElem.pay) #[c, Surface.Tm.quote c r, Surface.Tm.quote c a]
  | .saveNet x => mkAppN (mkConst ``Surface.UpdElem.saveNet) #[c, toExpr x]
  | .saveNetMt x => mkAppN (mkConst ``Surface.UpdElem.saveNetMt) #[c, toExpr x]
  | .netMt r a => mkAppN (mkConst ``Surface.UpdElem.netMt) #[c, Surface.Tm.quote c r, Surface.Tm.quote c a]
  | .setBalance a => mkAppN (mkConst ``Surface.UpdElem.setBalance) #[c, Surface.Tm.quote c a]

def Surface.Upd.quote : List (Surface.UpdElem C) → Lean.Expr
  | [] => mkAppN (mkConst ``List.nil [0]) #[mkAppN (mkConst ``Surface.UpdElem) #[c]]
  | u :: U => mkAppN (mkConst ``List.cons [0])
      #[mkAppN (mkConst ``Surface.UpdElem) #[c], Surface.UpdElem.quote c u, Surface.Upd.quote U]

def NFml.quote : NFml C → Lean.Expr
  | .tt => mkAppN (mkConst ``NFml.tt) #[c]
  | .eq a b => mkAppN (mkConst ``NFml.eq) #[c, Surface.Tm.quote c a, Surface.Tm.quote c b]
  | .defined t => mkAppN (mkConst ``NFml.defined) #[c, Surface.Tm.quote c t]
  | .not φ => mkAppN (mkConst ``NFml.not) #[c, NFml.quote φ]
  | .and φ ψ => mkAppN (mkConst ``NFml.and) #[c, NFml.quote φ, NFml.quote ψ]
  | .imp φ ψ => mkAppN (mkConst ``NFml.imp) #[c, NFml.quote φ, NFml.quote ψ]
  | .upd m U φ => mkAppN (mkConst ``NFml.upd) #[c, toExpr m, Surface.Upd.quote c U, NFml.quote φ]
  | .havoc φ => mkAppN (mkConst ``NFml.havoc) #[c, NFml.quote φ]
  | .all x p φ => mkAppN (mkConst ``NFml.all) #[c, toExpr x, toExpr p, NFml.quote φ]
  | .anon xs φ => mkAppN (mkConst ``NFml.anon) #[c, toExpr xs, NFml.quote φ]

/-- A formula as written (`Surface.Fml`), quoted. -/
def Surface.Fml.quote : Surface.Fml C → Lean.Expr
  | .tt => mkAppN (mkConst ``Surface.Fml.tt) #[c]
  | .eq a b => mkAppN (mkConst ``Surface.Fml.eq) #[c, Surface.Tm.quote c a, Surface.Tm.quote c b]
  | .defined t => mkAppN (mkConst ``Surface.Fml.defined) #[c, Surface.Tm.quote c t]
  | .not φ => mkAppN (mkConst ``Surface.Fml.not) #[c, Surface.Fml.quote φ]
  | .and φ ψ => mkAppN (mkConst ``Surface.Fml.and) #[c, Surface.Fml.quote φ, Surface.Fml.quote ψ]
  | .imp φ ψ => mkAppN (mkConst ``Surface.Fml.imp) #[c, Surface.Fml.quote φ, Surface.Fml.quote ψ]
  | .upd m U φ =>
    mkAppN (mkConst ``Surface.Fml.upd) #[c, toExpr m, Surface.Upd.quote c U, Surface.Fml.quote φ]
  | .modal m P φ =>
    mkAppN (mkConst ``Surface.Fml.modal) #[c, toExpr m, Surface.Prog.quote c P, Surface.Fml.quote φ]
  | .havoc φ => mkAppN (mkConst ``Surface.Fml.havoc) #[c, Surface.Fml.quote φ]
  | .all x p φ => mkAppN (mkConst ``Surface.Fml.all) #[c, toExpr x, toExpr p, Surface.Fml.quote φ]
  | .anon xs φ => mkAppN (mkConst ``Surface.Fml.anon) #[c, toExpr xs, Surface.Fml.quote φ]

/-- The expression `Lean.mkConst n []`: the `c` a quoter takes for the
contract named `n`, when the quoter runs as compiled code (`evalExpr`). -/
def quoteConstName (n : Lean.Name) : Lean.Expr :=
  mkAppN (mkConst ``Lean.mkConst)
    #[toExpr n, mkAppN (mkConst ``List.nil [0]) #[mkConst ``Lean.Level]]

end Quote

end Solidity
