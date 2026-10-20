import Lean.Util.ShareCommon
import Solidity.Syntax.Elab

/-!
# Quoting the scoped syntax

`Syntax/Scoped.lean`'s programs turned back into terms by hand (no
`deriving ToExpr` for an indexed family whose constructors carry proofs), the contract the constant
it names, every proof `Eq.refl` (`rflTrue`, `rflSome`, `rflPrim`), so the
kernel re-checks each one.

A position is its `Idx.here`/`Idx.there` chain.  Every node carries its
context, so the quoted term is a DAG, not a tree (Gate G0, condition 7): each
quoter takes the term of its context `Γe`, a context a statement leaves is
the locals it pushes consed onto `Γe` (`ctxFrom`), and `Prog.quoteShared`
hash-conses the whole (`ShareCommon`), which shares the types and the
equal contexts of sibling scopes too.  Unshared, the tree is 26–37 times
larger (the spike's measure).

The quoter is a pure function: the compiled elaborator runs it, and the
kernel checks its result where it is spliced (`sol{ … }`,
`Syntax/Splice.lean`) or declared (`Prog.define`, as `solc_import`,
`Frontend/Import.lean`, declares every imported program).
-/

namespace Solidity

open Lean (mkConst mkAppN toExpr)

deriving instance Lean.ToExpr for LTy

/-- The expression `Lean.mkConst n []`: the `c` a quoter takes for the
contract named `n`, when the quoter runs as compiled code (`evalExpr`). -/
def quoteConstName (n : Lean.Name) : Lean.Expr :=
  mkAppN (mkConst ``Lean.mkConst)
    #[toExpr n, mkAppN (mkConst ``List.nil [0]) #[mkConst ``Lean.Level]]

/-- `LTy`, the type of a context's elements. -/
def ltyE : Lean.Expr := mkConst ``LTy

/-- `t :: Γ`, at `LTy`. -/
def consE (t : LTy) (Γe : Lean.Expr) : Lean.Expr :=
  mkAppN (mkConst ``List.cons [0]) #[ltyE, toExpr t, Γe]

/-- A context, consed onto `Γe`: `ρ ++ Γ` with `Γe` the term of `Γ`. -/
def ctxOnto (Γe : Lean.Expr) (ρ : Ctx) : Lean.Expr := ρ.foldr consE Γe

/-- A context, as a literal list. -/
def ctxE (Γ : Ctx) : Lean.Expr := ctxOnto (mkAppN (mkConst ``List.nil [0]) #[ltyE]) Γ

/-- The term of `Δ`, sharing `Γe` (the term of `Γ`) when `Δ` is `Γ` with
locals pushed, as every context a statement or block leaves is. -/
def ctxFrom (Γ : Ctx) (Γe : Lean.Expr) (Δ : Ctx) : Lean.Expr :=
  let n := Γ.length
  let m := Δ.length
  if n ≤ m && Δ.drop (m - n) == Γ then ctxOnto Γe (Δ.take (m - n)) else ctxE Δ

/-- The tail of a literal context's term. -/
private def tailE (Γe : Lean.Expr) : Lean.Expr := Γe.appArg!

variable {C : Contract} (c : Lean.Expr)

def Idx.quote : {Γ : Ctx} → {t : LTy} → Lean.Expr → Idx Γ t → Lean.Expr
  | _, _, Γe, @Idx.here t _ => mkAppN (mkConst ``Idx.here) #[toExpr t, tailE Γe]
  | _, _, Γe, @Idx.there u t _ i =>
    mkAppN (mkConst ``Idx.there) #[toExpr u, toExpr t, tailE Γe, Idx.quote (tailE Γe) i]

def Binders.quote : {ρ : Ctx} → Binders ρ → Lean.Expr
  | _, .nil => mkConst ``Binders.nil
  | _, @Binders.snoc ρ bs p x => mkAppN (mkConst ``Binders.snoc) #[ctxE ρ, Binders.quote bs, toExpr p, toExpr x]

def CodeBinder.quote : {κ : Ctx} → CodeBinder κ → Lean.Expr
  | _, .none => mkConst ``CodeBinder.none
  | _, .some x => mkAppN (mkConst ``CodeBinder.some) #[toExpr x]

section Parts

variable {Γ : Ctx} (Γe : Lean.Expr)

def Simple.quote : {p : PrimTy} → Simple C Γ p → Lean.Expr
  | p, .lit n _ => mkAppN (mkConst ``Simple.lit) #[c, Γe, toExpr p, toExpr n, rflTrue]
  | _, .bool b => mkAppN (mkConst ``Simple.bool) #[c, Γe, toExpr b]
  | p, .local i => mkAppN (mkConst ``Simple.local) #[c, Γe, toExpr p, Idx.quote Γe i]
  | p, .env k _ => mkAppN (mkConst ``Simple.env) #[c, Γe, toExpr p, toExpr k, rflPrim p]

mutual

def SPath.quote : {T : Ty} → SPath C Γ T → Lean.Expr
  | _, @SPath.alias _ _ R i => mkAppN (mkConst ``SPath.alias) #[c, Γe, toExpr R, Idx.quote Γe i]
  | T, .loc l => mkAppN (mkConst ``SPath.loc) #[c, Γe, toExpr T, Loc.quote l]

def Loc.quote : {T : Ty} → Loc C Γ T → Lean.Expr
  | T, .root r _ => mkAppN (mkConst ``Loc.root) #[c, Γe, toExpr T, toExpr r, rflSome T]
  | T, @Loc.field _ _ s _ b f _ =>
    mkAppN (mkConst ``Loc.field) #[c, Γe, toExpr s, toExpr T, SPath.quote b, toExpr f, rflSome T]
  | V, @Loc.index _ _ R k _ it b i =>
    mkAppN (mkConst ``Loc.index) #[c, Γe, toExpr R, toExpr k, toExpr V, IndexTy.quote it,
      SPath.quote b, Val.quote i]

def MPath.quote : {T : Ty} → MPath C Γ T → Lean.Expr
  | _, @MPath.var _ _ R i _ =>
    mkAppN (mkConst ``MPath.var) #[c, Γe, toExpr R, Idx.quote Γe i, rflTrue]
  | T, .loc l => mkAppN (mkConst ``MPath.loc) #[c, Γe, toExpr T, MLoc.quote l]

def MLoc.quote : {T : Ty} → MLoc C Γ T → Lean.Expr
  | T, @MLoc.field _ _ s _ b f _ =>
    mkAppN (mkConst ``MLoc.field) #[c, Γe, toExpr s, toExpr T, MPath.quote b, toExpr f, rflSome T]
  | E', @MLoc.index _ _ R _ a b i =>
    mkAppN (mkConst ``MLoc.index) #[c, Γe, toExpr R, toExpr E', ArrTy.quote a, MPath.quote b,
      Val.quote i]

def Val.quote : {p : PrimTy} → Val C Γ p → Lean.Expr
  | p, .simple s => mkAppN (mkConst ``Val.simple) #[c, Γe, toExpr p, Simple.quote c Γe s]
  | p, .read l => mkAppN (mkConst ``Val.read) #[c, Γe, toExpr p, Loc.quote l]
  | _, @Val.binop _ _ p q op _ _ a b =>
    mkAppN (mkConst ``Val.binop) #[c, Γe, toExpr p, toExpr q, toExpr op, rflTrue, rflPrim q,
      Val.quote a, Val.quote b]
  | _, @Val.unop _ _ p q op _ _ a =>
    mkAppN (mkConst ``Val.unop) #[c, Γe, toExpr p, toExpr q, toExpr op, rflTrue, rflPrim q,
      Val.quote a]
  | p, .ternary cv a b =>
    mkAppN (mkConst ``Val.ternary) #[c, Γe, toExpr p, Val.quote cv, Val.quote a, Val.quote b]
  | p, .readMem l => mkAppN (mkConst ``Val.readMem) #[c, Γe, toExpr p, MLoc.quote l]
  | p, @Val.len _ _ _ E' b _ =>
    mkAppN (mkConst ``Val.len) #[c, Γe, toExpr p, toExpr E', SPath.quote b, rflPrim p]
  | p, @Val.mlen _ _ _ E' b _ =>
    mkAppN (mkConst ``Val.mlen) #[c, Γe, toExpr p, toExpr E', MPath.quote b, rflPrim p]
  | _, .modular op a b k =>
    mkAppN (mkConst ``Val.modular) #[c, Γe, toExpr op, Val.quote a, Val.quote b, Val.quote k]

end

/-- `Option α`'s term, at `α` = `ty`. -/
private def optQ {α : Type} (ty : Lean.Expr) (q : α → Lean.Expr) (o : Option α) : Lean.Expr := optE ty (o.map q)

/-- A shape witness: `uint[2] -> uint[]` or `uint[2] -> uint[4]`. -/
def FixedCopy.quote {E : Ty} {n : Nat} {R : RefTy} : FixedCopy E n R → Lean.Expr
  | .dynamic _ => mkAppN (mkConst ``FixedCopy.dynamicChecked) #[toExpr E, toExpr n, rflTrue]
  | .fixed m _ => mkAppN (mkConst ``FixedCopy.fixedChecked) #[toExpr E, toExpr n, toExpr m, rflTrue]

def Src.quote : {T : Ty} → Src C Γ T → Lean.Expr
  | _, @Src.val _ _ p v => mkAppN (mkConst ``Src.val) #[c, Γe, toExpr p, Val.quote c Γe v]
  | _, @Src.copy _ _ R p _ =>
    mkAppN (mkConst ``Src.copy) #[c, Γe, toExpr R, SPath.quote c Γe p, rflTrue]
  | _, @Src.fixedCopy _ _ E n R p shape _ =>
    mkAppN (mkConst ``Src.fixedCopy) #[c, Γe, toExpr E, toExpr n, toExpr R,
      SPath.quote c Γe p, FixedCopy.quote shape, rflTrue]
  | _, @Src.copyMem _ _ R p =>
    mkAppN (mkConst ``Src.copyMem) #[c, Γe, toExpr R, MPath.quote c Γe p]

def ARhs.quote {R : RefTy} : ARhs C Γ R → Lean.Expr
  | .path p => mkAppN (mkConst ``ARhs.path) #[c, Γe, toExpr R, SPath.quote c Γe p]
  | .push b _ => mkAppN (mkConst ``ARhs.push) #[c, Γe, toExpr R, SPath.quote c Γe b, rflTrue]

def MRhs.quote {R : RefTy} : MRhs C Γ R → Lean.Expr
  | .alias p => mkAppN (mkConst ``MRhs.alias) #[c, Γe, toExpr R, MPath.quote c Γe p]
  | .copy p _ => mkAppN (mkConst ``MRhs.copy) #[c, Γe, toExpr R, SPath.quote c Γe p, rflTrue]
  | .newArr n _ =>
    mkAppN (mkConst ``MRhs.newArr) #[c, Γe, toExpr R, Simple.quote c Γe n, rflTrue]

def NewLhs.quote : {R : RefTy} → NewLhs C Γ R → Lean.Expr
  | R, .store l => mkAppN (mkConst ``NewLhs.store) #[c, Γe, toExpr R, Loc.quote c Γe l]
  | R, .mem l => mkAppN (mkConst ``NewLhs.mem) #[c, Γe, toExpr R, MLoc.quote c Γe l]

def MSrc.quote : {T : Ty} → MSrc C Γ T → Lean.Expr
  | _, @MSrc.val _ _ p v => mkAppN (mkConst ``MSrc.val) #[c, Γe, toExpr p, Val.quote c Γe v]
  | _, @MSrc.ref _ _ R p => mkAppN (mkConst ``MSrc.ref) #[c, Γe, toExpr R, MPath.quote c Γe p]

def OpLoc.quote : {p : PrimTy} → OpLoc C Γ p → Lean.Expr
  | p, .local i => mkAppN (mkConst ``OpLoc.local) #[c, Γe, toExpr p, Idx.quote Γe i]
  | p, .root r _ => mkAppN (mkConst ``OpLoc.root) #[c, Γe, toExpr p, toExpr r, rflSome (.prim p)]
  | p, @OpLoc.field _ _ s _ b f _ =>
    mkAppN (mkConst ``OpLoc.field) #[c, Γe, toExpr s, toExpr p, SPath.quote c Γe b, toExpr f,
      rflSome (.prim p)]
  | p, @OpLoc.index _ _ R k _ it b i =>
    mkAppN (mkConst ``OpLoc.index) #[c, Γe, toExpr R, toExpr k, toExpr p, IndexTy.quote it,
      SPath.quote c Γe b, Simple.quote c Γe i]
  | p, @OpLoc.mfield _ _ s _ b f _ =>
    mkAppN (mkConst ``OpLoc.mfield) #[c, Γe, toExpr s, toExpr p, MPath.quote c Γe b, toExpr f,
      rflSome (.prim p)]
  | p, @OpLoc.mindex _ _ R _ a b i =>
    mkAppN (mkConst ``OpLoc.mindex) #[c, Γe, toExpr R, toExpr p, ArrTy.quote a,
      MPath.quote c Γe b, Simple.quote c Γe i]

/-- An external call, each argument a `Sigma.mk` of its type and value. -/
def ExtCall.quote (call : ExtCall C Γ) : Lean.Expr :=
  let argTy := mkAppN (mkConst ``ExtArg) #[c, Γe]
  let args := call.args.foldr (fun a acc => mkAppN (mkConst ``List.cons [0]) #[argTy,
      mkAppN (mkConst ``Sigma.mk [0, 0]) #[mkConst ``PrimTy, mkAppN (mkConst ``Simple) #[c, Γe],
        toExpr a.1, Simple.quote c Γe a.2], acc])
    (mkAppN (mkConst ``List.nil [0]) #[argTy])
  mkAppN (mkConst ``ExtCall.mk) #[c, Γe, Simple.quote c Γe call.addr, toExpr call.fn, args]

/-- A quantified invariant clause, its body under the bound local's
context. -/
def LoopQ.quote : {Δ : Ctx} → Lean.Expr → LoopQ C Δ → Lean.Expr
  | _, Δe, .val a => mkAppN (mkConst ``LoopQ.val) #[c, Δe, Val.quote c Δe a]
  | _, Δe, .imp a d => mkAppN (mkConst ``LoopQ.imp) #[c, Δe, Val.quote c Δe a, Val.quote c Δe d]
  | _, Δe, .all x p b =>
    mkAppN (mkConst ``LoopQ.all) #[c, Δe, toExpr x, toExpr p, LoopQ.quote (consE (.val p) Δe) b]

def LoopAnn.quote : LoopAnn C Γ → Lean.Expr
  | .unwind k => mkAppN (mkConst ``LoopAnn.unwind) #[c, Γe, toExpr k]
  | .auto => mkAppN (mkConst ``LoopAnn.auto) #[c, Γe]
  | .inv I dec brk qs =>
    let qTy := mkAppN (mkConst ``LoopQ) #[c, Γe]
    mkAppN (mkConst ``LoopAnn.inv) #[c, Γe, Val.quote c Γe I,
      optQ (mkAppN (mkConst ``Val) #[c, Γe, toExpr PrimTy.uint]) (Val.quote c Γe) dec, toExpr brk,
      qs.foldr (fun q acc => mkAppN (mkConst ``List.cons [0]) #[qTy, LoopQ.quote c Γe q, acc])
        (mkAppN (mkConst ``List.nil [0]) #[qTy])]

/-- A call's arguments, and the term of the parameters' context they bind. -/
def Args.quote : {ps : Ctx} → Args C Γ ps → Lean.Expr × Lean.Expr
  | _, .nil => (mkAppN (mkConst ``Args.nil) #[c, Γe], ctxE [])
  | _, @Args.snoc _ _ ps as p x e =>
    let (ase, pse) := Args.quote as
    (mkAppN (mkConst ``Args.snoc) #[c, Γe, pse, ase, toExpr p, toExpr x, Val.quote c Γe e],
      consE (.val p) pse)
  | _, @Args.snocStorage _ _ ps as R x e =>
    let (ase, pse) := Args.quote as
    (mkAppN (mkConst ``Args.snocStorage) #[c, Γe, pse, ase, toExpr R, toExpr x,
      SPath.quote c Γe e], consE (.alias R) pse)
  | _, @Args.snocMemory _ _ ps as R x e =>
    let (ase, pse) := Args.quote as
    (mkAppN (mkConst ``Args.snocMemory) #[c, Γe, pse, ase, toExpr R, toExpr x,
      MPath.quote c Γe e], consE (.mem R) pse)

/-- What a call leaves its caller. -/
def CallRet.quote : {rs Γ' : Ctx} → CallRet Γ rs Γ' → Lean.Expr
  | _, _, .none => mkAppN (mkConst ``CallRet.none) #[Γe]
  | _, _, .val p r res =>
    mkAppN (mkConst ``CallRet.val) #[Γe, toExpr p, toExpr r,
      optQ (mkAppN (mkConst ``Idx) #[Γe, toExpr (LTy.val p)]) (Idx.quote Γe) res]
  | _, _, @CallRet.rets _ rs bs => mkAppN (mkConst ``CallRet.rets) #[Γe, ctxE rs, Binders.quote bs]
  | _, _, .mem R r _ _ => mkAppN (mkConst ``CallRet.mem) #[Γe, toExpr R, toExpr r, rflTrue, rflTrue]
  | _, _, .storage R r => mkAppN (mkConst ``CallRet.storage) #[Γe, toExpr R, toExpr r]

def ReceiverOp.quote {E : Ty} : ReceiverOp C Γ E → Lean.Expr
  | .push v _ => mkAppN (mkConst ``ReceiverOp.push) #[c, Γe, toExpr E,
      optE (mkAppN (mkConst ``Src) #[c, Γe, toExpr E]) (v.map (Src.quote c Γe)), rflTrue]
  | .pop => mkAppN (mkConst ``ReceiverOp.pop) #[c, Γe, toExpr E]

end Parts

mutual

/-- A statement read in `Γ` (its term `Γe`) leaving `Γ'` (its term `Γ'e`). -/
def Stmt.quote : {Γ Γ' : Ctx} → Lean.Expr → Lean.Expr → Stmt C Γ Γ' → Lean.Expr
  | _, _, Γe, _, @Stmt.assign _ _ T l r =>
    mkAppN (mkConst ``Stmt.assign) #[c, Γe, toExpr T, Loc.quote c Γe l, Src.quote c Γe r]
  | _, _, Γe, _, @Stmt.rebind _ _ R i r =>
    mkAppN (mkConst ``Stmt.rebind) #[c, Γe, toExpr R, Idx.quote Γe i, ARhs.quote c Γe r]
  | _, _, Γe, _, @Stmt.assignLocal _ _ p i r =>
    mkAppN (mkConst ``Stmt.assignLocal) #[c, Γe, toExpr p, Idx.quote Γe i, Val.quote c Γe r]
  | _, _, Γe, _, .declLocal p x init =>
    mkAppN (mkConst ``Stmt.declLocal) #[c, Γe, toExpr p, toExpr x,
      optE (mkAppN (mkConst ``Val) #[c, Γe, toExpr p]) (init.map (Val.quote c Γe))]
  | _, _, Γe, _, .declStorage R x init =>
    mkAppN (mkConst ``Stmt.declStorage) #[c, Γe, toExpr R, toExpr x,
      optE (mkAppN (mkConst ``ARhs) #[c, Γe, toExpr R]) (init.map (ARhs.quote c Γe))]
  | _, _, Γe, _, @Stmt.opAssign _ _ p op _ _ l r =>
    mkAppN (mkConst ``Stmt.opAssign) #[c, Γe, toExpr p, toExpr op, rflTrue, rflTrue,
      OpLoc.quote c Γe l, Val.quote c Γe r]
  | _, _, Γe, _, @Stmt.incDec _ _ p op _ l =>
    mkAppN (mkConst ``Stmt.incDec) #[c, Γe, toExpr p, toExpr op, rflTrue, OpLoc.quote c Γe l]
  | _, _, Γe, _, @Stmt.pushOpAssign _ _ p op _ _ b r =>
    mkAppN (mkConst ``Stmt.pushOpAssign) #[c, Γe, toExpr p, toExpr op, rflTrue, rflTrue,
      SPath.quote c Γe b, Val.quote c Γe r]
  | _, _, Γe, _, @Stmt.pushIncDec _ _ p op _ b =>
    mkAppN (mkConst ``Stmt.pushIncDec) #[c, Γe, toExpr p, toExpr op, rflTrue,
      SPath.quote c Γe b]
  | _, _, Γe, _, @Stmt.assignIncDec _ _ p i op _ l _ =>
    mkAppN (mkConst ``Stmt.assignIncDec) #[c, Γe, toExpr p, Idx.quote Γe i, toExpr op, rflTrue,
      OpLoc.quote c Γe l, rflTrue]
  | _, _, Γe, _, @Stmt.assignLocalPush _ _ p i b =>
    mkAppN (mkConst ``Stmt.assignLocalPush) #[c, Γe, toExpr p, Idx.quote Γe i,
      SPath.quote c Γe b]
  | _, _, Γe, _, @Stmt.push _ _ E' b v _ =>
    mkAppN (mkConst ``Stmt.push) #[c, Γe, toExpr E', SPath.quote c Γe b,
      optE (mkAppN (mkConst ``Src) #[c, Γe, toExpr E']) (v.map (Src.quote c Γe)), rflTrue]
  | _, _, Γe, _, @Stmt.pop _ _ E' b => mkAppN (mkConst ``Stmt.pop) #[c, Γe, toExpr E', SPath.quote c Γe b]
  | _, _, Γe, _, @Stmt.callReceiver _ _ ps Γf E' f args r body op =>
    let (ase, pse) := Args.quote c Γe args
    let Γfe := ctxOnto pse [.alias (.array E')]
    mkAppN (mkConst ``Stmt.callReceiver) #[c, Γe, pse,
      ctxFrom ([.alias (.array E')] ++ ps) Γfe Γf, toExpr E', toExpr f,
      ase, toExpr r, Prog.quote Γfe (ctxFrom ([.alias (.array E')] ++ ps) Γfe Γf) body,
      ReceiverOp.quote c Γe op]
  | Γ, _, Γe, _, @Stmt.callReceiverPush _ _ ps Γf Γv E' f args r body code value =>
    let (ase, pse) := Args.quote c Γe args
    let Γfe := ctxOnto pse [.alias (.array E')]
    let Γve := ctxFrom Γ Γe Γv
    mkAppN (mkConst ``Stmt.callReceiverPush) #[c, Γe, pse,
      ctxFrom ([.alias (.array E')] ++ ps) Γfe Γf, Γve, toExpr E', toExpr f,
      ase, toExpr r, Prog.quote Γfe (ctxFrom ([.alias (.array E')] ++ ps) Γfe Γf) body,
      Prog.quote Γe Γve code, Src.quote c Γve value]
  | _, _, Γe, _, .transfer r a =>
    mkAppN (mkConst ``Stmt.transfer) #[c, Γe, Val.quote c Γe r, Val.quote c Γe a]
  | _, _, Γe, _, .send pv r a g =>
    mkAppN (mkConst ``Stmt.send) #[c, Γe, Idx.quote Γe pv, Val.quote c Γe r, Val.quote c Γe a,
      toExpr g]
  | _, _, Γe, _, .declMem R x init _ _ =>
    mkAppN (mkConst ``Stmt.declMem) #[c, Γe, toExpr R, toExpr x,
      optE (mkAppN (mkConst ``MRhs) #[c, Γe, toExpr R]) (init.map (MRhs.quote c Γe)),
      rflTrue, rflTrue]
  | _, _, Γe, _, @Stmt.rebindMem _ _ R i r =>
    mkAppN (mkConst ``Stmt.rebindMem) #[c, Γe, toExpr R, Idx.quote Γe i, MRhs.quote c Γe r]
  | _, _, Γe, _, @Stmt.assignFromMem _ _ R l p =>
    mkAppN (mkConst ``Stmt.assignFromMem) #[c, Γe, toExpr R, Loc.quote c Γe l, MPath.quote c Γe p]
  | _, _, Γe, _, @Stmt.assignMem _ _ T l r =>
    mkAppN (mkConst ``Stmt.assignMem) #[c, Γe, toExpr T, MLoc.quote c Γe l, MSrc.quote c Γe r]
  | _, _, Γe, _, @Stmt.delete _ _ T l => mkAppN (mkConst ``Stmt.delete) #[c, Γe, toExpr T, Loc.quote c Γe l]
  | _, _, Γe, _, @Stmt.deleteMem _ _ T p _ =>
    mkAppN (mkConst ``Stmt.deleteMem) #[c, Γe, toExpr T, MPath.quote c Γe p, rflTrue]
  | _, _, Γe, _, @Stmt.assignNew _ _ R l n _ =>
    mkAppN (mkConst ``Stmt.assignNew) #[c, Γe, toExpr R, NewLhs.quote c Γe l,
      Simple.quote c Γe n, rflTrue]
  | Γ, _, Γe, _, @Stmt.ite _ _ Γ₁ Γ₂ cv thn els =>
    let Γ₁e := ctxFrom Γ Γe Γ₁
    let Γ₂e := ctxFrom Γ Γe Γ₂
    mkAppN (mkConst ``Stmt.ite) #[c, Γe, Γ₁e, Γ₂e, Val.quote c Γe cv,
      Prog.quote Γe Γ₁e thn, Prog.quote Γe Γ₂e els]
  | _, _, Γe, _, .require cv => mkAppN (mkConst ``Stmt.require) #[c, Γe, Val.quote c Γe cv]
  | _, _, Γe, _, .assert cv => mkAppN (mkConst ``Stmt.assert) #[c, Γe, Val.quote c Γe cv]
  | _, _, Γe, _, .revert => mkAppN (mkConst ``Stmt.revert) #[c, Γe]
  | _, _, Γe, _, .assumeFalse => mkAppN (mkConst ``Stmt.assumeFalse) #[c, Γe]
  | _, _, Γe, Γ'e, @Stmt.call _ _ _ ps rs Γf f args ret body =>
    let (ase, pse) := Args.quote c Γe args
    let fre := ctxOnto pse rs
    let Γfe := ctxFrom (rs ++ ps) fre Γf
    mkAppN (mkConst ``Stmt.call) #[c, Γe, Γ'e, pse, ctxE rs, Γfe, toExpr f, ase,
      CallRet.quote Γe ret, Prog.quote fre Γfe body]
  | Γ, _, Γe, _, @Stmt.tryCall _ _ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf call rets ok err code pnc other
      sargs sbody self =>
    let oke := ctxOnto Γe ρ
    let pne := ctxOnto Γe κ
    let Γ₁e := ctxFrom (ρ ++ Γ) oke Γ₁
    let Γ₂e := ctxFrom Γ Γe Γ₂
    let Γ₃e := ctxFrom (κ ++ Γ) pne Γ₃
    let Γ₄e := ctxFrom Γ Γe Γ₄
    let (ase, pse) := Args.quote c Γe sargs
    let fre := ctxOnto pse ρ
    let Γfe := ctxFrom (ρ ++ ps) fre Γf
    mkAppN (mkConst ``Stmt.tryCall) #[c, Γe, ctxE ρ, ctxE κ, Γ₁e, Γ₂e, Γ₃e, Γ₄e, pse, Γfe,
      ExtCall.quote c Γe call, Binders.quote rets, Prog.quote oke Γ₁e ok, Prog.quote Γe Γ₂e err,
      CodeBinder.quote code, Prog.quote pne Γ₃e pnc, Prog.quote Γe Γ₄e other, ase,
      Prog.quote fre Γfe sbody, toExpr self]
  | Γ, _, Γe, _, @Stmt.loop _ _ Γ₁ a cv body =>
    let Γ₁e := ctxFrom Γ Γe Γ₁
    mkAppN (mkConst ``Stmt.loop) #[c, Γe, Γ₁e, LoopAnn.quote c Γe a, Val.quote c Γe cv,
      Prog.quote Γe Γ₁e body]
  | Γ, _, Γe, _, @Stmt.block _ _ Γ₁ body =>
    let Γ₁e := ctxFrom Γ Γe Γ₁
    mkAppN (mkConst ``Stmt.block) #[c, Γe, Γ₁e, Prog.quote Γe Γ₁e body]

/-- A block read in `Γ` (its term `Γe`) leaving `Γ'` (its term `Γ'e`). -/
def Prog.quote : {Γ Γ' : Ctx} → Lean.Expr → Lean.Expr → Prog C Γ Γ' → Lean.Expr
  | _, _, Γe, _, .nil => mkAppN (mkConst ``Prog.nil) #[c, Γe]
  | Γ, _, Γe, Γ₂e, @Prog.cons _ _ Γ₁ _ s P =>
    let Γ₁e := ctxFrom Γ Γe Γ₁
    mkAppN (mkConst ``Prog.cons) #[c, Γe, Γ₁e, Γ₂e, Stmt.quote Γe Γ₁e s, Prog.quote Γ₁e Γ₂e P]

end

/-- A block of `C` (the constant `c`) from `Γ`, quoted and hash-consed, with
the terms of its contexts: the value, `Γ` and `Γ'`. -/
def Prog.quoteShared {Γ Γ' : Ctx} (P : Prog C Γ Γ') : Lean.Expr × Lean.Expr × Lean.Expr :=
  let Γe := ctxE Γ
  let Γ'e := ctxFrom Γ Γe Γ'
  Lean.ShareCommon.shareCommon (Prog.quote c Γe Γ'e P, Γe, Γ'e)

/-- The type `Prog C Γ Γ'` of a quoted block, from the terms of its contexts. -/
def Prog.quoteType (Γe Γ'e : Lean.Expr) : Lean.Expr := mkAppN (mkConst ``Prog) #[c, Γe, Γ'e]

open Lean in
/-- Declare `n : Prog C Γ Γ'`, the block `P` of the contract the constant
`cn` names, quoted (`quoteShared`) and checked by the kernel: `none`, or why
the kernel rejects it. -/
def Prog.define (n cn : Lean.Name) {Γ Γ' : Ctx} (P : Prog C Γ Γ') : CoreM (Option String) := do
  let c := mkConst cn
  let (v, Γe, Γ'e) := Prog.quoteShared c P
  let decl := Declaration.defnDecl {
    name := n, levelParams := [], type := Prog.quoteType c Γe Γ'e, value := v,
    hints := .abbrev, safety := .safe }
  tryCatchRuntimeEx (do addDecl decl; pure none)
    fun ex => do pure (some s!"the kernel rejects the scoped program: {← ex.toMessageData.toString}")

end Solidity
