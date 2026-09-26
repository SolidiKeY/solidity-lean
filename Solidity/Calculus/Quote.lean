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

mutual

def Term.quote : Term C → Lean.Expr
  | .lit v => mkAppN (mkConst ``Term.lit) #[c, toExpr v]
  | .pv x => mkAppN (mkConst ``Term.pv) #[c, toExpr x]
  | .binop op p a b =>
    mkAppN (mkConst ``Term.binop) #[c, toExpr op, toExpr p, Term.quote a, Term.quote b]
  | .unop op p a => mkAppN (mkConst ``Term.unop) #[c, toExpr op, toExpr p, Term.quote a]
  | .find s p => mkAppN (mkConst ``Term.find) #[c, STerm.quote s, PTerm.quote p]
  | .len s p => mkAppN (mkConst ``Term.len) #[c, STerm.quote s, PTerm.quote p]
  | .read m a => mkAppN (mkConst ``Term.read) #[c, MTerm.quote m, MAddr.quote a]
  | .ite i a b => mkAppN (mkConst ``Term.ite) #[c, Term.quote i, Term.quote a, Term.quote b]

def PTerm.quote : PTerm C → Lean.Expr
  | .root r => mkAppN (mkConst ``PTerm.root) #[c, toExpr r]
  | .pv x => mkAppN (mkConst ``PTerm.pv) #[c, toExpr x]
  | .field p f => mkAppN (mkConst ``PTerm.field) #[c, PTerm.quote p, toExpr f]
  | .at p i => mkAppN (mkConst ``PTerm.at) #[c, PTerm.quote p, Term.quote i]

def STerm.quote : STerm C → Lean.Expr
  | .storage => mkAppN (mkConst ``STerm.storage) #[c]
  | .save s p v => mkAppN (mkConst ``STerm.save) #[c, STerm.quote s, PTerm.quote p, SValT.quote v]
  | .delAt s p => mkAppN (mkConst ``STerm.delAt) #[c, STerm.quote s, PTerm.quote p]
  | .push s p v => mkAppN (mkConst ``STerm.push) #[c, STerm.quote s, PTerm.quote p, SValT.quote v]
  | .pushSlot s p E =>
    mkAppN (mkConst ``STerm.pushSlot) #[c, STerm.quote s, PTerm.quote p, toExpr E]
  | .pop s p => mkAppN (mkConst ``STerm.pop) #[c, STerm.quote s, PTerm.quote p]
  | .extend s p E => mkAppN (mkConst ``STerm.extend) #[c, STerm.quote s, PTerm.quote p, toExpr E]

def SValT.quote : SValT C → Lean.Expr
  | .val t => mkAppN (mkConst ``SValT.val) #[c, Term.quote t]
  | .find s p => mkAppN (mkConst ``SValT.find) #[c, STerm.quote s, PTerm.quote p]
  | .copyMem m i => mkAppN (mkConst ``SValT.copyMem) #[c, MTerm.quote m, ITerm.quote i]

def ITerm.quote : ITerm C → Lean.Expr
  | .pv x => mkAppN (mkConst ``ITerm.pv) #[c, toExpr x]
  | .read m a => mkAppN (mkConst ``ITerm.read) #[c, MTerm.quote m, MAddr.quote a]
  | .alloc m R => mkAppN (mkConst ``ITerm.alloc) #[c, MTerm.quote m, toExpr R]
  | .copy m v => mkAppN (mkConst ``ITerm.copy) #[c, MTerm.quote m, SValT.quote v]

def MAddr.quote : MAddr C → Lean.Expr
  | .field i f => mkAppN (mkConst ``MAddr.field) #[c, ITerm.quote i, toExpr f]
  | .at i k => mkAppN (mkConst ``MAddr.at) #[c, ITerm.quote i, Term.quote k]

def MTerm.quote : MTerm C → Lean.Expr
  | .memory => mkAppN (mkConst ``MTerm.memory) #[c]
  | .write m a v => mkAppN (mkConst ``MTerm.write) #[c, MTerm.quote m, MAddr.quote a, MValT.quote v]
  | .addM m R => mkAppN (mkConst ``MTerm.addM) #[c, MTerm.quote m, toExpr R]
  | .copySt m v => mkAppN (mkConst ``MTerm.copySt) #[c, MTerm.quote m, SValT.quote v]

def MValT.quote : MValT C → Lean.Expr
  | .val t => mkAppN (mkConst ``MValT.val) #[c, Term.quote t]
  | .ref i => mkAppN (mkConst ``MValT.ref) #[c, ITerm.quote i]

end

def UpdElem.quote : UpdElem C → Lean.Expr
  | .val x t => mkAppN (mkConst ``UpdElem.val) #[c, toExpr x, Term.quote c t]
  | .path x p => mkAppN (mkConst ``UpdElem.path) #[c, toExpr x, PTerm.quote c p]
  | .mref x i => mkAppN (mkConst ``UpdElem.mref) #[c, toExpr x, ITerm.quote c i]
  | .storage s => mkAppN (mkConst ``UpdElem.storage) #[c, STerm.quote c s]
  | .memory m => mkAppN (mkConst ``UpdElem.memory) #[c, MTerm.quote c m]
  | .transfer r a => mkAppN (mkConst ``UpdElem.transfer) #[c, Term.quote c r, Term.quote c a]

def Upd.quote : List (UpdElem C) → Lean.Expr
  | [] => mkAppN (mkConst ``List.nil [0]) #[mkAppN (mkConst ``UpdElem) #[c]]
  | u :: U => mkAppN (mkConst ``List.cons [0])
      #[mkAppN (mkConst ``UpdElem) #[c], UpdElem.quote c u, Upd.quote U]

def Fml.quote : Fml C → Lean.Expr
  | .tt => mkAppN (mkConst ``Fml.tt) #[c]
  | .eq a b => mkAppN (mkConst ``Fml.eq) #[c, Term.quote c a, Term.quote c b]
  | .not φ => mkAppN (mkConst ``Fml.not) #[c, Fml.quote φ]
  | .and φ ψ => mkAppN (mkConst ``Fml.and) #[c, Fml.quote φ, Fml.quote ψ]
  | .imp φ ψ => mkAppN (mkConst ``Fml.imp) #[c, Fml.quote φ, Fml.quote ψ]
  | .upd m U φ => mkAppN (mkConst ``Fml.upd) #[c, toExpr m, Upd.quote c U, Fml.quote φ]
  | .modal m P φ => mkAppN (mkConst ``Fml.modal) #[c, toExpr m, Prog.quote c P, Fml.quote φ]

end Quote

end Solidity
