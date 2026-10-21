import Solidity.Calculus.Fml
import Solidity.Syntax.Quote

/-!
# Quoting scoped formulas back into Lean

Entry points: `Fml.quote`, `Tm.quote`, `Upd.quote`, `Frames.quote` and
`Premise.quote`, each hash-consed.

The quoter for the scoped formulas of `Calculus/Fml.lean` and the
programs of `Syntax/Scoped.lean`: a formula
computed by compiled code (the strategy, `Calculus/Step.lean`) becomes
an `Expr` again, written with the constructors' names and the contract by
its name, for the kernel to check that it is what the formula steps to.

Every constructor carries its contexts as arguments, so a tree written out
is many times the formula (Gate G0 measured 26–37×).  The quoter therefore
hash-conses its result (`ShareCommon`): every copy of a context, and every
other repeated subterm, is one object, and the kernel's caches see it once
(condition 7).  A side condition is
`Eq.refl`, which the kernel checks by evaluating it.

The quoter runs at elaboration time, so it may `match` on the indexed
families; it is `partial`, since it is never unfolded.
-/

namespace Solidity

deriving instance Lean.ToExpr for Srt

open Lean (Expr mkAppN mkConst mkApp mkApp2 mkApp3 mkApp4 toExpr levelZero)
open Solidity (Srt Op0 Op1 Op2 Op3 Modality IntOp rflTrue rflPrim rflSome optE quoteRefl)

namespace Quote

/-! ## Types and contexts -/

def qLTy : LTy → Expr
  | .val p => mkApp (mkConst ``LTy.val) (toExpr p)
  | .alias R => mkApp (mkConst ``LTy.alias) (toExpr R)
  | .mem R => mkApp (mkConst ``LTy.mem) (toExpr R)
  | .old => mkConst ``LTy.old
  | .oldNet => mkConst ``LTy.oldNet
  | .kint => mkConst ``LTy.kint

def ltyE : Expr := mkConst ``LTy

def qCtxRaw : Ctx → Expr
  | [] => mkApp (mkConst ``List.nil [levelZero]) ltyE
  | t :: Γ => mkApp3 (mkConst ``List.cons [levelZero]) ltyE (qLTy t) (qCtxRaw Γ)

def qSrt (s : Srt) : Expr := toExpr s

end Quote

open Quote

/-- The quoting monad: the contract's `Expr`. -/
abbrev QM := ReaderT Expr Id

namespace Quote

/-- A context, written out; `Fml.quote` shares the copies afterwards. -/
def qCtx (Γ : Ctx) : QM Expr := pure (qCtxRaw Γ)

def contract : QM Expr := read

def qIdx : (Γ : Ctx) → (t : LTy) → Idx Γ t → QM Expr
  | t :: Γ, _, .here => return mkApp2 (mkConst ``Idx.here) (qLTy t) (← qCtx Γ)
  | u :: Γ, t, .there i => do
    let i ← qIdx Γ t i
    return mkApp4 (mkConst ``Idx.there) (qLTy u) (qLTy t) (← qCtx Γ) i

def qExt (Γ : Ctx) {Δ : Ctx} (h : Ext Γ Δ) : QM Expr :=
  match Δ, h with
  | _, .refl => return mkApp (mkConst ``Ext.refl) (← qCtx Γ)
  | _, @Ext.push _ t Δ h => do
    let he ← qExt Γ h
    return mkApp4 (mkConst ``Ext.push) (← qCtx Γ) (qLTy t) (← qCtx Δ) he

partial def qThin : (Γ Δ : Ctx) → Thin Γ Δ → QM Expr
  | Γ, _, .refl => return mkApp (mkConst ``Thin.refl) (← qCtx Γ)
  | t :: Γ, _ :: Δ, .keep h => do
    return mkApp4 (mkConst ``Thin.keep) (qLTy t) (← qCtx Γ) (← qCtx Δ) (← qThin Γ Δ h)
  | Γ, t :: Δ, .drop h => do
    return mkApp4 (mkConst ``Thin.drop) (qLTy t) (← qCtx Γ) (← qCtx Δ) (← qThin Γ Δ h)

def qBinders : (ρ : Ctx) → Binders ρ → QM Expr
  | _, .nil => return mkConst ``Binders.nil
  | _ :: ρ, .snoc bs p x => do
    let b ← qBinders ρ bs
    return mkApp4 (mkConst ``Binders.snoc) (← qCtx ρ) b (toExpr p) (toExpr x)

def qCode : (κ : Ctx) → CodeBinder κ → Expr
  | _, .none => mkConst ``CodeBinder.none
  | _, .some x => mkApp (mkConst ``CodeBinder.some) (toExpr x)

/-! ## Expressions -/

variable {C : Contract}

/-- `F C Γ`, the family applied to its parameters. -/
def fam (n : Lean.Name) (Γ : Ctx) : QM Expr := return mkApp2 (mkConst n) (← contract) (← qCtx Γ)

/-- A constructor of a family with parameters `C Γ`, applied to `args`. -/
def ctor (n : Lean.Name) (Γ : Ctx) (args : Array Expr) : QM Expr :=
  return mkAppN (mkConst n) (#[← contract, ← qCtx Γ] ++ args)

def qSimple (Γ : Ctx) : (p : PrimTy) → Simple C Γ p → QM Expr
  | p, .lit n _ => ctor ``Simple.lit Γ #[toExpr p, toExpr n, rflTrue]
  | _, .bool b => ctor ``Simple.bool Γ #[toExpr b]
  | p, .local i => do ctor ``Simple.local Γ #[toExpr p, ← qIdx Γ (.val p) i]
  | p, .env k _ => ctor ``Simple.env Γ #[toExpr p, toExpr k, rflPrim p]

mutual

partial def qSPath (Γ : Ctx) : (T : Ty) → SPath C Γ T → QM Expr
  | _, @SPath.alias _ _ R i => do ctor ``SPath.alias Γ #[toExpr R, ← qIdx Γ (.alias R) i]
  | T, .loc l => do ctor ``SPath.loc Γ #[toExpr T, ← qLoc Γ T l]

partial def qLoc (Γ : Ctx) : (T : Ty) → Loc C Γ T → QM Expr
  | T, .root r _ => ctor ``Loc.root Γ #[toExpr T, toExpr r, rflSome T]
  | T, @Loc.field _ _ s _ b f _ => do
    ctor ``Loc.field Γ #[toExpr s, toExpr T, ← qSPath Γ _ b, toExpr f, rflSome T]
  | V, @Loc.index _ _ R k _ it b i => do
    ctor ``Loc.index Γ #[toExpr R, toExpr k, toExpr V, IndexTy.quote it, ← qSPath Γ _ b,
      ← qVal Γ k i]

partial def qMPath (Γ : Ctx) : (T : Ty) → MPath C Γ T → QM Expr
  | _, @MPath.var _ _ R i _ => do ctor ``MPath.var Γ #[toExpr R, ← qIdx Γ (.mem R) i, rflTrue]
  | T, .loc l => do ctor ``MPath.loc Γ #[toExpr T, ← qMLoc Γ T l]

partial def qMLoc (Γ : Ctx) : (T : Ty) → MLoc C Γ T → QM Expr
  | T, @MLoc.field _ _ s _ b f _ => do
    ctor ``MLoc.field Γ #[toExpr s, toExpr T, ← qMPath Γ _ b, toExpr f, rflSome T]
  | E, @MLoc.index _ _ R _ a b i => do
    ctor ``MLoc.index Γ #[toExpr R, toExpr E, ArrTy.quote a, ← qMPath Γ _ b, ← qVal Γ .uint i]

partial def qVal (Γ : Ctx) : (p : PrimTy) → Val C Γ p → QM Expr
  | p, .simple s => do ctor ``Val.simple Γ #[toExpr p, ← qSimple Γ p s]
  | p, .read l => do ctor ``Val.read Γ #[toExpr p, ← qLoc Γ _ l]
  | _, @Val.binop _ _ p q op _ _ a b => do
    ctor ``Val.binop Γ #[toExpr p, toExpr q, toExpr op, rflTrue, rflPrim q, ← qVal Γ p a,
      ← qVal Γ p b]
  | _, @Val.unop _ _ p q op _ _ a => do
    ctor ``Val.unop Γ #[toExpr p, toExpr q, toExpr op, rflTrue, rflPrim q, ← qVal Γ p a]
  | p, .ternary c a b => do
    ctor ``Val.ternary Γ #[toExpr p, ← qVal Γ .bool c, ← qVal Γ p a, ← qVal Γ p b]
  | p, .readMem l => do ctor ``Val.readMem Γ #[toExpr p, ← qMLoc Γ _ l]
  | p, @Val.len _ _ _ E b _ => do ctor ``Val.len Γ #[toExpr p, toExpr E, ← qSPath Γ _ b, rflPrim p]
  | p, @Val.mlen _ _ _ E b _ => do
    ctor ``Val.mlen Γ #[toExpr p, toExpr E, ← qMPath Γ _ b, rflPrim p]
  | _, .modular op a b k => do
    ctor ``Val.modular Γ #[toExpr op, ← qVal Γ .uint a, ← qVal Γ .uint b, ← qVal Γ .uint k]
  | p, @Val.keccak _ _ _ R b _ => do
    ctor ``Val.keccak Γ #[toExpr p, toExpr R, ← qMPath Γ _ b, rflPrim p]

end

def qSrc (Γ : Ctx) : (T : Ty) → Src C Γ T → QM Expr
  | _, @Src.val _ _ p v => do ctor ``Src.val Γ #[toExpr p, ← qVal Γ p v]
  | _, @Src.copy _ _ R p _ => do ctor ``Src.copy Γ #[toExpr R, ← qSPath Γ _ p, rflTrue]
  | _, @Src.fixedCopy _ _ E n R p shape _ => do
    ctor ``Src.fixedCopy Γ #[toExpr E, toExpr n, toExpr R, ← qSPath Γ _ p, FixedCopy.quote shape, rflTrue]
  | _, @Src.copyMem _ _ R p => do ctor ``Src.copyMem Γ #[toExpr R, ← qMPath Γ _ p]

def qARhs (Γ : Ctx) (R : RefTy) : ARhs C Γ R → QM Expr
  | .path p => do ctor ``ARhs.path Γ #[toExpr R, ← qSPath Γ _ p]
  | .push b _ => do ctor ``ARhs.push Γ #[toExpr R, ← qSPath Γ _ b, rflTrue]

def qMRhs (Γ : Ctx) (R : RefTy) : MRhs C Γ R → QM Expr
  | .alias p => do ctor ``MRhs.alias Γ #[toExpr R, ← qMPath Γ _ p]
  | .copy p _ => do ctor ``MRhs.copy Γ #[toExpr R, ← qSPath Γ _ p, rflTrue]
  | .newArr n _ => do ctor ``MRhs.newArr Γ #[toExpr R, ← qSimple Γ .uint n, rflTrue]

def qNewLhs (Γ : Ctx) : (R : RefTy) → NewLhs C Γ R → QM Expr
  | R, .store l => do ctor ``NewLhs.store Γ #[toExpr R, ← qLoc Γ _ l]
  | R, .mem l => do ctor ``NewLhs.mem Γ #[toExpr R, ← qMLoc Γ _ l]

def qMSrc (Γ : Ctx) : (T : Ty) → MSrc C Γ T → QM Expr
  | _, @MSrc.val _ _ p v => do ctor ``MSrc.val Γ #[toExpr p, ← qVal Γ p v]
  | _, @MSrc.ref _ _ R p => do ctor ``MSrc.ref Γ #[toExpr R, ← qMPath Γ _ p]

def qOpLoc (Γ : Ctx) : (p : PrimTy) → OpLoc C Γ p → QM Expr
  | p, .local i => do ctor ``OpLoc.local Γ #[toExpr p, ← qIdx Γ (.val p) i]
  | p, .root r _ => ctor ``OpLoc.root Γ #[toExpr p, toExpr r, rflSome (.prim p)]
  | p, @OpLoc.field _ _ s _ b f _ => do
    ctor ``OpLoc.field Γ #[toExpr s, toExpr p, ← qSPath Γ _ b, toExpr f, rflSome (.prim p)]
  | p, @OpLoc.index _ _ R k _ it b i => do
    ctor ``OpLoc.index Γ #[toExpr R, toExpr k, toExpr p, IndexTy.quote it, ← qSPath Γ _ b,
      ← qSimple Γ k i]
  | p, @OpLoc.mfield _ _ s _ b f _ => do
    ctor ``OpLoc.mfield Γ #[toExpr s, toExpr p, ← qMPath Γ _ b, toExpr f, rflSome (.prim p)]
  | p, @OpLoc.mindex _ _ R _ a b i => do
    ctor ``OpLoc.mindex Γ #[toExpr R, toExpr p, ArrTy.quote a, ← qMPath Γ _ b,
      ← qSimple Γ .uint i]

def qArgs (Γ : Ctx) : (ps : Ctx) → Args C Γ ps → QM Expr
  | _, .nil => ctor ``Args.nil Γ #[]
  | _ :: ps, .snoc as p x e => do
    ctor ``Args.snoc Γ #[← qCtx ps, ← qArgs Γ ps as, toExpr p, toExpr x, ← qVal Γ p e]
  | _ :: ps, .snocStorage as R x e => do
    ctor ``Args.snocStorage Γ #[← qCtx ps, ← qArgs Γ ps as, toExpr R, toExpr x,
      ← qSPath Γ (.ref R) e]
  | _ :: ps, .snocMemory as R x e => do
    ctor ``Args.snocMemory Γ #[← qCtx ps, ← qArgs Γ ps as, toExpr R, toExpr x,
      ← qMPath Γ (.ref R) e]

def qCallRet (Γ : Ctx) : (rs Γ' : Ctx) → CallRet Γ rs Γ' → QM Expr
  | _, _, .none => return mkApp (mkConst ``CallRet.none) (← qCtx Γ)
  | _, _, .val p r res => do
    let ty := mkApp2 (mkConst ``Idx) (← qCtx Γ) (mkApp (mkConst ``LTy.val) (toExpr p))
    let res ← match res with
      | none => pure (optE ty none)
      | some i => pure (optE ty (some (← qIdx Γ (.val p) i)))
    return mkApp4 (mkConst ``CallRet.val) (← qCtx Γ) (toExpr p) (toExpr r) res
  | rs, _, .rets bs => do
    let b ← qBinders rs bs
    return mkApp3 (mkConst ``CallRet.rets) (← qCtx Γ) (← qCtx rs) b
  | _, _, .mem R r _ _ => do
    return mkAppN (mkConst ``CallRet.mem) #[← qCtx Γ, toExpr R, toExpr r, rflTrue, rflTrue]
  | _, _, .storage R r => do
    return mkAppN (mkConst ``CallRet.storage) #[← qCtx Γ, toExpr R, toExpr r]

def qExtCall (Γ : Ctx) (call : ExtCall C Γ) : QM Expr := do
  let argTy ← fam ``ExtArg Γ
  let simpleF ← fam ``Simple Γ
  let mut args := mkApp (mkConst ``List.nil [levelZero]) argTy
  for a in call.args.reverse do
    let ae := mkAppN (mkConst ``Sigma.mk [levelZero, levelZero])
      #[mkConst ``PrimTy, simpleF, toExpr a.1, ← qSimple Γ a.1 a.2]
    args := mkApp3 (mkConst ``List.cons [levelZero]) argTy ae args
  ctor ``ExtCall.mk Γ #[← qSimple Γ .uint call.addr, toExpr call.fn, args]

/-- A quantified invariant clause. -/
def qLoopQ : (Γ : Ctx) → LoopQ C Γ → QM Expr
  | Γ, .val a => do ctor ``LoopQ.val Γ #[← qVal Γ .bool a]
  | Γ, .imp a c => do ctor ``LoopQ.imp Γ #[← qVal Γ .bool a, ← qVal Γ .bool c]
  | Γ, .all x p b => do ctor ``LoopQ.all Γ #[toExpr x, toExpr p, ← qLoopQ (.val p :: Γ) b]

def qLoopAnn (Γ : Ctx) : LoopAnn C Γ → QM Expr
  | .unwind k => ctor ``LoopAnn.unwind Γ #[toExpr k]
  | .auto => ctor ``LoopAnn.auto Γ #[]
  | .inv I dec brk qs => do
    let ty := mkApp3 (mkConst ``Val) (← contract) (← qCtx Γ) (toExpr PrimTy.uint)
    let d ← match dec with
      | none => pure (optE ty none)
      | some d => pure (optE ty (some (← qVal Γ .uint d)))
    let qTy := mkApp2 (mkConst ``LoopQ) (← contract) (← qCtx Γ)
    let mut l := mkApp (mkConst ``List.nil [levelZero]) qTy
    for q in qs.reverse do
      l := mkApp3 (mkConst ``List.cons [levelZero]) qTy (← qLoopQ Γ q) l
    ctor ``LoopAnn.inv Γ #[← qVal Γ .bool I, d, toExpr brk, l]

/-! ## Statements -/

/-- The placeholder of a free program thunk `i` where the compiled strategy
runs a goal that has one (a recursive call's frame below in an induction
step, `Calculus/Recursion.lean`; `Symex.normValid`): a body no elaborated
program has, which the quoter writes back as the constant `_recFVar.i`. -/
def _root_.Solidity.Prog.recSentinel {F : Ctx} (i : Nat) : Prog C F F :=
  .cons (.block (.cons (.declLocal .bool (.fresh "⟪recfvar⟫" i) none) .nil)) .nil

/-- Which placeholder a body is, if it is one. -/
def _root_.Solidity.Prog.recSentinel? {F : Ctx} : Prog C F F → Option Nat
  | .cons (.block (.cons (.declLocal _ (.fresh b i) none) .nil)) .nil =>
    if b == "⟪recfvar⟫" then some i else none
  | _ => none

/-- A constructor of `Stmt C`/`Prog C`, the contract its only parameter. -/
def sctor (n : Lean.Name) (args : Array Expr) : QM Expr :=
  return mkAppN (mkConst n) (#[← contract] ++ args)

/-- `Option (F C Γ x)` of a quoted option. -/
def qOpt {α : Type} (ty : Expr) (q : α → QM Expr) : Option α → QM Expr
  | none => pure (optE ty none)
  | some a => return optE ty (some (← q a))

/-- Quote the typed operation of `f().push(e)` or `f().pop()`. -/
def qReceiverOp (Γ : Ctx) (E : Ty) : ReceiverOp C Γ E → QM Expr
  | .push v _ => do
    sctor ``ReceiverOp.push #[← qCtx Γ, toExpr E,
      ← qOpt (mkApp3 (mkConst ``Src) (← contract) (← qCtx Γ) (toExpr E)) (qSrc Γ E) v,
      rflTrue]
  | .pop => do sctor ``ReceiverOp.pop #[← qCtx Γ, toExpr E]

mutual

partial def qStmtH (hs : List Name) (Γ Γ' : Ctx) (s : Stmt C Γ Γ') : QM Expr := do
  let Γe ← qCtx Γ
  match s with
  | @Stmt.assign _ _ T l r => sctor ``Stmt.assign #[Γe, toExpr T, ← qLoc Γ T l, ← qSrc Γ T r]
  | @Stmt.rebind _ _ R i r =>
    sctor ``Stmt.rebind #[Γe, toExpr R, ← qIdx Γ (.alias R) i, ← qARhs Γ R r]
  | @Stmt.assignLocal _ _ p i r =>
    sctor ``Stmt.assignLocal #[Γe, toExpr p, ← qIdx Γ (.val p) i, ← qVal Γ p r]
  | .declLocal p x init =>
    sctor ``Stmt.declLocal #[Γe, toExpr p, toExpr x,
      ← qOpt (mkApp3 (mkConst ``Val) (← contract) Γe (toExpr p)) (qVal Γ p) init]
  | .declStorage R x init =>
    sctor ``Stmt.declStorage #[Γe, toExpr R, toExpr x,
      ← qOpt (mkApp3 (mkConst ``ARhs) (← contract) Γe (toExpr R)) (qARhs Γ R) init]
  | @Stmt.opAssign _ _ p op _ _ l r =>
    sctor ``Stmt.opAssign #[Γe, toExpr p, toExpr op, rflTrue, rflTrue, ← qOpLoc Γ p l,
      ← qVal Γ p r]
  | @Stmt.incDec _ _ p op _ l =>
    sctor ``Stmt.incDec #[Γe, toExpr p, toExpr op, rflTrue, ← qOpLoc Γ p l]
  | @Stmt.assignIncDec _ _ p i op _ l _ =>
    sctor ``Stmt.assignIncDec #[Γe, toExpr p, ← qIdx Γ (.val p) i, toExpr op, rflTrue,
      ← qOpLoc Γ p l, rflTrue]
  | @Stmt.assignLocalPush _ _ p i b =>
    sctor ``Stmt.assignLocalPush #[Γe, toExpr p, ← qIdx Γ (.val p) i, ← qSPath Γ _ b]
  | @Stmt.pushOpAssign _ _ p op _ _ b r =>
    sctor ``Stmt.pushOpAssign #[Γe, toExpr p, toExpr op, rflTrue, rflTrue,
      ← qSPath Γ _ b, ← qVal Γ p r]
  | @Stmt.pushIncDec _ _ p op _ b =>
    sctor ``Stmt.pushIncDec #[Γe, toExpr p, toExpr op, rflTrue, ← qSPath Γ _ b]
  | @Stmt.push _ _ E b v _ =>
    sctor ``Stmt.push #[Γe, toExpr E, ← qSPath Γ _ b,
      ← qOpt (mkApp3 (mkConst ``Src) (← contract) Γe (toExpr E)) (qSrc Γ E) v, rflTrue]
  | @Stmt.pop _ _ E b => sctor ``Stmt.pop #[Γe, toExpr E, ← qSPath Γ _ b]
  | .transfer r a => sctor ``Stmt.transfer #[Γe, ← qVal Γ .uint r, ← qVal Γ .uint a]
  | .send pv r a g =>
    sctor ``Stmt.send #[Γe, ← qIdx Γ (.val .bool) pv, ← qVal Γ .uint r, ← qVal Γ .uint a,
      toExpr g]
  | .declMem R x init _ _ =>
    sctor ``Stmt.declMem #[Γe, toExpr R, toExpr x,
      ← qOpt (mkApp3 (mkConst ``MRhs) (← contract) Γe (toExpr R)) (qMRhs Γ R) init,
      rflTrue, rflTrue]
  | @Stmt.rebindMem _ _ R i r =>
    sctor ``Stmt.rebindMem #[Γe, toExpr R, ← qIdx Γ (.mem R) i, ← qMRhs Γ R r]
  | @Stmt.assignFromMem _ _ R l p =>
    sctor ``Stmt.assignFromMem #[Γe, toExpr R, ← qLoc Γ _ l, ← qMPath Γ _ p]
  | @Stmt.assignMem _ _ T l r => sctor ``Stmt.assignMem #[Γe, toExpr T, ← qMLoc Γ T l, ← qMSrc Γ T r]
  | @Stmt.delete _ _ T l => sctor ``Stmt.delete #[Γe, toExpr T, ← qLoc Γ T l]
  | @Stmt.deleteMem _ _ T p _ => sctor ``Stmt.deleteMem #[Γe, toExpr T, ← qMPath Γ T p, rflTrue]
  | @Stmt.assignNew _ _ R l n _ =>
    sctor ``Stmt.assignNew #[Γe, toExpr R, ← qNewLhs Γ R l, ← qSimple Γ .uint n, rflTrue]
  | @Stmt.ite _ _ Γ₁ Γ₂ c thn els =>
    sctor ``Stmt.ite #[Γe, ← qCtx Γ₁, ← qCtx Γ₂, ← qVal Γ .bool c, ← qProgH hs Γ Γ₁ thn,
      ← qProgH hs Γ Γ₂ els]
  | .require c => sctor ``Stmt.require #[Γe, ← qVal Γ .bool c]
  | .assert c => sctor ``Stmt.assert #[Γe, ← qVal Γ .bool c]
  | .revert => sctor ``Stmt.revert #[Γe]
  | .assumeFalse => sctor ``Stmt.assumeFalse #[Γe]
  | .revertData d => do
    let ty := mkApp2 (mkConst ``RevPart) (← contract) Γe
    let parts ← d.mapM fun
      | .bytes bs => ctor ``RevPart.bytes Γ #[toExpr bs]
      | .sel sig => ctor ``RevPart.sel Γ #[toExpr sig]
      | @RevPart.word _ _ p v => do ctor ``RevPart.word Γ #[toExpr p, ← qVal Γ p v]
    sctor ``Stmt.revertData #[Γe, parts.foldr
      (fun x acc => mkApp3 (mkConst ``List.cons [levelZero]) ty x acc)
      (mkApp (mkConst ``List.nil [levelZero]) ty)]
  | @Stmt.catchData _ _ ρ ps Γf Γ₁ call rets sargs sbody self kind x body =>
    sctor ``Stmt.catchData #[Γe, ← qCtx ρ, ← qCtx ps, ← qCtx Γf, ← qCtx Γ₁,
      ← qExtCall Γ call, ← qBinders ρ rets, ← qArgs Γ ps sargs, ← qProgH hs (ρ ++ ps) Γf sbody,
      toExpr self, CatchKind.quote kind, toExpr x, ← qProgH hs (.mem bytesR :: Γ) Γ₁ body]
  | @Stmt.call _ _ _ ps rs Γf f args ret body =>
    sctor ``Stmt.call #[Γe, ← qCtx Γ', ← qCtx ps, ← qCtx rs, ← qCtx Γf, toExpr f,
      ← qArgs Γ ps args, ← qCallRet Γ rs Γ' ret, ← qProgH hs (rs ++ ps) Γf body]
  | @Stmt.callReceiver _ _ ps Γf E f args r body op =>
    sctor ``Stmt.callReceiver #[Γe, ← qCtx ps, ← qCtx Γf, toExpr E, toExpr f,
      ← qArgs Γ ps args, toExpr r, ← qProgH hs ([.alias (.array E)] ++ ps) Γf body,
      ← qReceiverOp Γ E op]
  | @Stmt.callReceiverPush _ _ ps Γf Γv E f args r body code value =>
    sctor ``Stmt.callReceiverPush #[Γe, ← qCtx ps, ← qCtx Γf, ← qCtx Γv, toExpr E, toExpr f,
      ← qArgs Γ ps args, toExpr r, ← qProgH hs ([.alias (.array E)] ++ ps) Γf body,
      ← qProgH hs Γ Γv code, ← qSrc Γv E value]
  | @Stmt.tryCall _ _ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf call rets ok err code pnc other sargs sbody self =>
    sctor ``Stmt.tryCall #[Γe, ← qCtx ρ, ← qCtx κ, ← qCtx Γ₁, ← qCtx Γ₂, ← qCtx Γ₃, ← qCtx Γ₄,
      ← qCtx ps, ← qCtx Γf,
      ← qExtCall Γ call, ← qBinders ρ rets, ← qProgH hs (ρ ++ Γ) Γ₁ ok, ← qProgH hs Γ Γ₂ err,
      qCode κ code, ← qProgH hs (κ ++ Γ) Γ₃ pnc, ← qProgH hs Γ Γ₄ other, ← qArgs Γ ps sargs,
      ← qProgH hs (ρ ++ ps) Γf sbody, toExpr self]
  | @Stmt.loop _ _ Γ₁ a c body =>
    sctor ``Stmt.loop #[Γe, ← qCtx Γ₁, ← qLoopAnn Γ a, ← qVal Γ .bool c, ← qProgH hs Γ Γ₁ body]
  | @Stmt.block _ _ Γ₁ body => sctor ``Stmt.block #[Γe, ← qCtx Γ₁, ← qProgH hs Γ Γ₁ body]
  | @Stmt.callRec _ _ _ ps rs f d args ret body => do
    let head := #[Γe, ← qCtx Γ', ← qCtx ps, ← qCtx rs, toExpr f]
    let ase ← qArgs Γ ps args
    let rete ← qCallRet Γ rs Γ' ret
    match hs.idxOf? f with
    -- a call of the function whose unrolling is being quoted: the frame below
    | some j => sctor ``Stmt.callRec (head ++ #[.bvar (3 * j + 1), ase, rete, .bvar (3 * j)])
    -- `fun _ => recUnroll Prog.recBase (fun n bt => body) d`, as `Syntax/Quote.lean`
    | none =>
      if let some i := (body ()).recSentinel? then
        return ← sctor ``Stmt.callRec (head ++ #[Lean.mkRawNatLit d, ase, rete,
          mkConst (.num `_recFVar i)])
      let fre ← qCtx (rs ++ ps)
      let progTy := mkApp3 (mkConst ``Prog) (← contract) fre fre
      let thunkTy := Lean.mkForall `u .default (mkConst ``Unit) progTy
      let inner ← qProgH (f :: hs) (rs ++ ps) (rs ++ ps) (body ())
      let stepE := Lean.mkLambda `n .default (mkConst ``Nat)
        (Lean.mkLambda `bt .default thunkTy inner)
      let unroll := mkAppN (mkConst ``recUnroll) #[progTy,
        mkApp2 (mkConst ``Prog.recBase) (← contract) fre, stepE, Lean.mkRawNatLit d]
      sctor ``Stmt.callRec (head ++ #[Lean.mkRawNatLit d, ase, rete,
        Lean.mkLambda `u .default (mkConst ``Unit) unroll])

partial def qProgH (hs : List Name) (Γ Γ' : Ctx) (P : Prog C Γ Γ') : QM Expr := do
  match P with
  | .nil => sctor ``Prog.nil #[← qCtx Γ]
  | @Prog.cons _ _ Γ₁ _ s P =>
    sctor ``Prog.cons #[← qCtx Γ, ← qCtx Γ₁, ← qCtx Γ', ← qStmtH hs Γ Γ₁ s, ← qProgH hs Γ₁ Γ' P]

end

partial def qStmt (Γ Γ' : Ctx) (s : Stmt C Γ Γ') : QM Expr := qStmtH [] Γ Γ' s

partial def qProg (Γ Γ' : Ctx) (P : Prog C Γ Γ') : QM Expr := qProgH [] Γ Γ' P

/-! ## Terms, updates, formulas -/

/-- A value of a primitive type: a `Bool`, or `PrimTy.ofLit p n rfl` (the
lowering's literal, `Simple.lower`), its range checked by the kernel. -/
def qPrimVal : (p : PrimTy) → p.Denote → Expr
  | .bool, b => toExpr (show Bool from b)
  | .uint, v => mkApp3 (mkConst ``PrimTy.ofLit) (toExpr PrimTy.uint)
      (toExpr (v : {n : Int // PrimTy.uint.inRange n = true}).1) rflTrue
  | .int, v => mkApp3 (mkConst ``PrimTy.ofLit) (toExpr PrimTy.int)
      (toExpr (v : {n : Int // PrimTy.int.inRange n = true}).1) rflTrue

/-! A symbol is quoted with its implicit arguments and its proofs: a
contract lookup `Eq.refl (some T)` (`rflSome`), a Boolean side condition
`Eq.refl true` (`rflTrue`), as `Syntax/Quote.lean` quotes a program's, so
the kernel re-checks each by evaluation; an `IndexTy` or `ArrTy` as its
constructor. -/

def qOp0 : {s : Srt} → Op0 C s → QM Expr
  | _, @Op0.lit _ p v => do return mkApp3 (mkConst ``Op0.lit) (← contract) (toExpr p) (qPrimVal p v)
  | _, .env k => do return mkApp2 (mkConst ``Op0.env) (← contract) (toExpr k)
  | _, @Op0.root _ r T _ => do
    return mkApp4 (mkConst ``Op0.root) (← contract) (toExpr r) (toExpr T) (rflSome T)
  | _, .storage => do return mkApp (mkConst ``Op0.storage) (← contract)
  | _, .memory => do return mkApp (mkConst ``Op0.memory) (← contract)
  | _, .mtSt => do return mkApp (mkConst ``Op0.mtSt) (← contract)
  | _, @Op0.member _ s f T _ => do
    return mkAppN (mkConst ``Op0.member) #[← contract, toExpr s, toExpr f, toExpr T, rflSome T]
  | _, .zlit n => do return mkApp2 (mkConst ``Op0.zlit) (← contract) (toExpr n)

def qOp1 : {a s : Srt} → Op1 C a s → QM Expr
  | _, _, @Op1.unop _ op p _ => do
    return mkAppN (mkConst ``Op1.unop) #[← contract, toExpr op, toExpr p, rflTrue]
  | _, _, .net => do return mkApp (mkConst ``Op1.net) (← contract)
  | _, _, @Op1.delValue _ p => do return mkApp2 (mkConst ``Op1.delValue) (← contract) (toExpr p)
  | _, _, @Op1.field _ s f T _ => do
    return mkAppN (mkConst ``Op1.field) #[← contract, toExpr s, toExpr f, toExpr T, rflSome T]
  | _, _, @Op1.next _ E => do return mkApp2 (mkConst ``Op1.next) (← contract) (toExpr E)
  | _, _, @Op1.sval _ p => do return mkApp2 (mkConst ``Op1.sval) (← contract) (toExpr p)
  | _, _, @Op1.newArr _ R _ => do
    return mkApp3 (mkConst ``Op1.newArr) (← contract) (toExpr R) rflTrue
  | _, _, .alloc R _ => do return mkApp3 (mkConst ``Op1.alloc) (← contract) (toExpr R) rflTrue
  | _, _, @Op1.mfield _ s f T _ => do
    return mkAppN (mkConst ``Op1.mfield) #[← contract, toExpr s, toExpr f, toExpr T, rflSome T]
  | _, _, .addM R _ => do return mkApp3 (mkConst ``Op1.addM) (← contract) (toExpr R) rflTrue
  | _, _, @Op1.mval _ p => do return mkApp2 (mkConst ``Op1.mval) (← contract) (toExpr p)
  | _, _, @Op1.ref _ R => do return mkApp2 (mkConst ``Op1.ref) (← contract) (toExpr R)
  | _, _, .wt => do return mkApp (mkConst ``Op1.wt) (← contract)
  | _, _, .cleanTail => do return mkApp (mkConst ``Op1.cleanTail) (← contract)
  | _, _, @Op1.fixedCopy _ E n R shape => do
    return mkAppN (mkConst ``Op1.fixedCopy) #[← contract, toExpr E, toExpr n, toExpr R, FixedCopy.quote shape]
  | _, _, @Op1.select _ s r _ => do
    return mkAppN (mkConst ``Op1.select) #[← contract, toExpr s, toExpr r,
      rflSome (.ref (.struct s))]
  | _, _, @Op1.selectIn _ s s' f _ => do
    return mkAppN (mkConst ``Op1.selectIn) #[← contract, toExpr s, toExpr s', toExpr f,
      rflSome (.ref (.struct s'))]
  | _, _, @Op1.fieldIn _ s s' f T _ => do
    return mkAppN (mkConst ``Op1.fieldIn) #[← contract, toExpr s, toExpr s', toExpr f, toExpr T,
      rflSome T]
  | _, _, .toInt => do return mkApp (mkConst ``Op1.toInt) (← contract)

def qOp2 : {a b s : Srt} → Op2 C a b s → QM Expr
  | _, _, _, @Op2.binop _ op p _ => do
    return mkAppN (mkConst ``Op2.binop) #[← contract, toExpr op, toExpr p, rflTrue]
  | _, _, _, @Op2.find _ p => do return mkApp2 (mkConst ``Op2.find) (← contract) (toExpr p)
  | _, _, _, @Op2.len _ E => do return mkApp2 (mkConst ``Op2.len) (← contract) (toExpr E)
  | _, _, _, @Op2.read _ p => do return mkApp2 (mkConst ``Op2.read) (← contract) (toExpr p)
  | _, _, _, @Op2.mlen _ E => do return mkApp2 (mkConst ``Op2.mlen) (← contract) (toExpr E)
  | _, _, _, @Op2.keccak _ R => do return mkApp2 (mkConst ``Op2.keccak) (← contract) (toExpr R)
  | _, _, _, @Op2.at _ R k V it => do
    return mkAppN (mkConst ``Op2.at) #[← contract, toExpr R, toExpr k, toExpr V, IndexTy.quote it]
  | _, _, _, @Op2.nextIn _ E => do return mkApp2 (mkConst ``Op2.nextIn) (← contract) (toExpr E)
  | _, _, _, @Op2.delAt _ T => do return mkApp2 (mkConst ``Op2.delAt) (← contract) (toExpr T)
  | _, _, _, @Op2.pushSlot _ E => do return mkApp2 (mkConst ``Op2.pushSlot) (← contract) (toExpr E)
  | _, _, _, @Op2.pop _ E => do return mkApp2 (mkConst ``Op2.pop) (← contract) (toExpr E)
  | _, _, _, @Op2.shrink _ E => do return mkApp2 (mkConst ``Op2.shrink) (← contract) (toExpr E)
  | _, _, _, @Op2.extend _ E => do return mkApp2 (mkConst ``Op2.extend) (← contract) (toExpr E)
  | _, _, _, @Op2.sfind _ T => do return mkApp2 (mkConst ``Op2.sfind) (← contract) (toExpr T)
  | _, _, _, @Op2.copyMem _ R => do return mkApp2 (mkConst ``Op2.copyMem) (← contract) (toExpr R)
  | _, _, _, @Op2.iread _ R => do return mkApp2 (mkConst ``Op2.iread) (← contract) (toExpr R)
  | _, _, _, @Op2.copy _ R _ => do return mkApp3 (mkConst ``Op2.copy) (← contract) (toExpr R) rflTrue
  | _, _, _, @Op2.mat _ R E a => do
    return mkAppN (mkConst ``Op2.mat) #[← contract, toExpr R, toExpr E, ArrTy.quote a]
  | _, _, _, @Op2.copySt _ T _ => do
    return mkApp3 (mkConst ``Op2.copySt) (← contract) (toExpr T) rflTrue
  | _, _, _, @Op2.findIn _ s p => do
    return mkApp3 (mkConst ``Op2.findIn) (← contract) (toExpr s) (toExpr p)
  | _, _, _, @Op2.delAtIn _ s T => do
    return mkApp3 (mkConst ``Op2.delAtIn) (← contract) (toExpr s) (toExpr T)
  | _, _, _, @Op2.sfindIn _ s T => do
    return mkApp3 (mkConst ``Op2.sfindIn) (← contract) (toExpr s) (toExpr T)
  | _, _, _, .zbin op _ => do return mkApp3 (mkConst ``Op2.zbin) (← contract) (toExpr op) rflTrue
  | _, _, _, .zcmp op _ => do return mkApp3 (mkConst ``Op2.zcmp) (← contract) (toExpr op) rflTrue

def qOp3 : {a b c s : Srt} → Op3 C a b c s → QM Expr
  | _, _, _, _, @Op3.ite _ p => do return mkApp2 (mkConst ``Op3.ite) (← contract) (toExpr p)
  | _, _, _, _, @Op3.save _ T => do return mkApp2 (mkConst ``Op3.save) (← contract) (toExpr T)
  | _, _, _, _, @Op3.push _ E => do return mkApp2 (mkConst ``Op3.push) (← contract) (toExpr E)
  | _, _, _, _, @Op3.atIn _ R k V it => do
    return mkAppN (mkConst ``Op3.atIn) #[← contract, toExpr R, toExpr k, toExpr V, IndexTy.quote it]
  | _, _, _, _, @Op3.write _ T => do return mkApp2 (mkConst ``Op3.write) (← contract) (toExpr T)
  | _, _, _, _, @Op3.saveIn _ s T => do
    return mkApp3 (mkConst ``Op3.saveIn) (← contract) (toExpr s) (toExpr T)
  | _, _, _, _, .modular op => do return mkApp2 (mkConst ``Op3.modular) (← contract) (toExpr op)

partial def qTm (Γ : Ctx) : (s : Srt) → Tm C Γ s → QM Expr
  | _, @Tm.pvV _ _ p i => do ctor ``Tm.pvV Γ #[toExpr p, ← qIdx Γ (.val p) i]
  | _, @Tm.pvP _ _ R i => do ctor ``Tm.pvP Γ #[toExpr R, ← qIdx Γ (.alias R) i]
  | _, .pvS i => do ctor ``Tm.pvS Γ #[← qIdx Γ .old i]
  | _, @Tm.pvI _ _ R i => do ctor ``Tm.pvI Γ #[toExpr R, ← qIdx Γ (.mem R) i]
  | _, .netOf i a => do ctor ``Tm.netOf Γ #[← qIdx Γ .oldNet i, ← qTm Γ (.val .uint) a]
  | s, .app0 o => do ctor ``Tm.app0 Γ #[qSrt s, ← qOp0 o]
  | s, @Tm.app1 _ _ a _ o x => do
    ctor ``Tm.app1 Γ #[qSrt a, qSrt s, ← qOp1 o, ← qTm Γ a x]
  | s, @Tm.app2 _ _ a b _ o x y => do
    ctor ``Tm.app2 Γ #[qSrt a, qSrt b, qSrt s, ← qOp2 o, ← qTm Γ a x, ← qTm Γ b y]
  | s, @Tm.app3 _ _ a b c _ o x y z => do
    ctor ``Tm.app3 Γ #[qSrt a, qSrt b, qSrt c, qSrt s, ← qOp3 o, ← qTm Γ a x, ← qTm Γ b y,
      ← qTm Γ c z]
  | _, .pvZ i => do ctor ``Tm.pvZ Γ #[← qIdx Γ .kint i]

def qRhs (Γ : Ctx) : (t : LTy) → Rhs C Γ t → QM Expr
  | _, @Rhs.val _ _ p t => do ctor ``Rhs.val Γ #[toExpr p, ← qTm Γ (.val p) t]
  | _, @Rhs.path _ _ R p => do ctor ``Rhs.path Γ #[toExpr R, ← qTm Γ (.path (.ref R)) p]
  | _, @Rhs.unset _ _ R => ctor ``Rhs.unset Γ #[toExpr R]
  | _, @Rhs.mref _ _ R i => do ctor ``Rhs.mref Γ #[toExpr R, ← qTm Γ (.ident R) i]
  | _, .store s => do ctor ``Rhs.store Γ #[← qTm Γ .st s]
  | _, .saveNet => ctor ``Rhs.saveNet Γ #[]
  | _, .saveNetMt => ctor ``Rhs.saveNetMt Γ #[]
  | _, .zint t => do ctor ``Rhs.zint Γ #[← qTm Γ .kint t]

def qUpdElem (Γ Δ : Ctx) (e : UpdElem C Γ Δ) : QM Expr := do
  let pre := #[← contract, ← qCtx Γ, ← qCtx Δ]
  let mk (n : Lean.Name) (args : Array Expr) : Expr := mkAppN (mkConst n) (pre ++ args)
  match e with
  | @UpdElem.local _ _ _ t i r => return mk ``UpdElem.local #[qLTy t, ← qIdx Δ t i, ← qRhs Γ t r]
  | .storage s => return mk ``UpdElem.storage #[← qTm Γ .st s]
  | .memory m => return mk ``UpdElem.memory #[← qTm Γ .mem m]
  | .selfBalance op a => return mk ``UpdElem.selfBalance #[IntOp.quote op, ← qTm Γ (.val .uint) a]
  | .net r op a =>
    return mk ``UpdElem.net #[← qTm Γ (.val .uint) r, IntOp.quote op, ← qTm Γ (.val .uint) a]
  | .pay r a => return mk ``UpdElem.pay #[← qTm Γ (.val .uint) r, ← qTm Γ (.val .uint) a]
  | .netMt r a => return mk ``UpdElem.netMt #[← qTm Γ (.val .uint) r, ← qTm Γ (.val .uint) a]
  | .setBalance a => return mk ``UpdElem.setBalance #[← qTm Γ (.val .uint) a]

partial def qUpd (Γ : Ctx) : (Δ : Ctx) → Upd C Γ Δ → QM Expr
  | _, .nil => ctor ``Upd.nil Γ #[]
  | Δ, .snoc U e => do ctor ``Upd.snoc Γ #[← qCtx Δ, ← qUpd Γ Δ U, ← qUpdElem Γ Δ e]
  | _, @Upd.decl _ _ Δ t U x r => do
    ctor ``Upd.decl Γ #[← qCtx Δ, qLTy t, ← qUpd Γ Δ U, toExpr x, ← qRhs Γ t r]
  | Δ', @Upd.pop _ _ Δ _ U h => do
    ctor ``Upd.pop Γ #[← qCtx Δ, ← qCtx Δ', ← qUpd Γ Δ U, ← qExt Δ' h]
  | Δ', @Upd.drop _ _ Δ _ U h => do
    ctor ``Upd.drop Γ #[← qCtx Δ, ← qCtx Δ', ← qUpd Γ Δ U, ← qThin Δ' Δ h]

def qBlockKind : BlockKind → Expr
  | .block => mkConst ``BlockKind.block
  | .capture => mkConst ``BlockKind.capture

partial def qFrames (Γ Γ₀ : Ctx) (κ : Frames C Γ Γ₀) : QM Expr := do
  match κ with
  | .nil => sctor ``Frames.nil #[← qCtx Γ]
  | @Frames.seq _ _ Γ₁ _ ω κ =>
    sctor ``Frames.seq #[← qCtx Γ, ← qCtx Γ₁, ← qCtx Γ₀, ← qProg Γ Γ₁ ω, ← qFrames Γ₁ Γ₀ κ]
  | @Frames.pop _ Γ₁ _ _ b h κ =>
    sctor ``Frames.pop #[← qCtx Γ₁, ← qCtx Γ, ← qCtx Γ₀, qBlockKind b, ← qExt Γ₁ h,
      ← qFrames Γ₁ Γ₀ κ]
  | @Frames.drop _ Γ₁ _ _ h κ =>
    sctor ``Frames.drop #[← qCtx Γ₁, ← qCtx Γ, ← qCtx Γ₀, ← qThin Γ₁ Γ h, ← qFrames Γ₁ Γ₀ κ]

/-- A list of positions with their types (`{anon(xs)}`, an invariant's frame). -/
def qIdxList (Γ : Ctx) (xs : List ((t : LTy) × Idx Γ t)) : QM Expr := do
  let idxF := mkApp (mkConst ``Idx) (← qCtx Γ)
  let sigTy := mkApp2 (mkConst ``Sigma [levelZero, levelZero]) ltyE idxF
  let mut l := mkApp (mkConst ``List.nil [levelZero]) sigTy
  for ⟨t, i⟩ in xs.reverse do
    let e := mkAppN (mkConst ``Sigma.mk [levelZero, levelZero]) #[ltyE, idxF, qLTy t, ← qIdx Γ t i]
    l := mkApp3 (mkConst ``List.cons [levelZero]) sigTy e l
  return l

partial def qFml (Γ : Ctx) (φ : Fml C Γ) : QM Expr := do
  let Γe ← qCtx Γ
  match φ with
  | .tt => sctor ``Fml.tt #[Γe]
  | @Fml.eq _ _ p a b => sctor ``Fml.eq #[Γe, toExpr p, ← qTm Γ (.val p) a, ← qTm Γ (.val p) b]
  | @Fml.wellFormed _ _ s => sctor ``Fml.wellFormed #[Γe, ← qTm Γ .st s]
  | .not φ => sctor ``Fml.not #[Γe, ← qFml Γ φ]
  | .and φ ψ => sctor ``Fml.and #[Γe, ← qFml Γ φ, ← qFml Γ ψ]
  | .imp φ ψ => sctor ``Fml.imp #[Γe, ← qFml Γ φ, ← qFml Γ ψ]
  | @Fml.upd _ _ Γ' m U φ =>
    sctor ``Fml.upd #[Γe, ← qCtx Γ', toExpr m, ← qUpd Γ Γ' U, ← qFml Γ' φ]
  | @Fml.modal _ _ Γ₁ Γ₀ m P κ φ =>
    sctor ``Fml.modal #[Γe, ← qCtx Γ₁, ← qCtx Γ₀, toExpr m, ← qProg Γ Γ₁ P, ← qFrames Γ₁ Γ₀ κ,
      ← qFml Γ₀ φ]
  | .havoc φ => sctor ``Fml.havoc #[Γe, ← qFml Γ φ]
  | .all x p φ => sctor ``Fml.all #[Γe, toExpr x, toExpr p, ← qFml (.val p :: Γ) φ]
  | .bind m x t φ => sctor ``Fml.bind #[Γe, toExpr m, toExpr x, qLTy t, ← qFml (t :: Γ) φ]
  | .anon xs φ => do sctor ``Fml.anon #[Γe, ← qIdxList Γ xs, ← qFml Γ φ]
  | .allocAll x A φ => sctor ``Fml.allocAll #[Γe, toExpr x, toExpr A, ← qFml (.mem A :: Γ) φ]

/-- A list of a `try`'s blocks (`Premise.branches`). -/
def qBranches (Γ : Ctx) (bs : List (Branch C Γ)) : QM Expr := do
  let brTy := mkApp2 (mkConst ``Branch) (← contract) (← qCtx Γ)
  let mut l := mkApp (mkConst ``List.nil [levelZero]) brTy
  for b in bs.reverse do
    let fTy ← fam ``Fml Γ
    let hyp ← match b.hyp with
      | none => pure (mkApp (mkConst ``Option.none [levelZero]) fTy)
      | some c => pure (mkApp2 (mkConst ``Option.some [levelZero]) fTy (← qFml Γ c))
    let e := mkAppN (mkConst ``Branch.mk) #[← contract, ← qCtx Γ, ← qCtx b.ρ, ← qCtx b.Γ₁,
      ← qBinders b.ρ b.bs, ← qProg (b.ρ ++ Γ) b.Γ₁ b.P, hyp]
    l := mkApp3 (mkConst ``List.cons [levelZero]) brTy e l
  return l

def qPremise (Γ Γ' : Ctx) (p : Premise C Γ Γ') : QM Expr := do
  let pre := #[← contract, ← qCtx Γ]
  let mk (n : Lean.Name) (args : Array Expr) : Expr := mkAppN (mkConst n) (pre ++ args)
  match p with
  | .update U => return mk ``Premise.update #[← qCtx Γ', ← qUpd Γ Γ' U]
  | @Premise.updates _ _ Δ _ U V =>
    return mk ``Premise.updates #[← qCtx Δ, ← qCtx Γ', ← qUpd Γ Δ U, ← qUpd Δ Γ' V]
  | @Premise.guardedUpdates _ _ Δ c U V =>
    return mk ``Premise.guardedUpdates #[← qCtx Δ, ← qFml Γ c, ← qUpd Γ Δ U, ← qUpd Δ Γ V]
  | @Premise.unfold _ _ _ Γ'' P h =>
    return mk ``Premise.unfold #[← qCtx Γ', ← qCtx Γ'', ← qProg Γ Γ'' P, ← qExt Γ' h]
  | .bind x t P => return mk ``Premise.bind #[← qCtx Γ', toExpr x, qLTy t, ← qProg (t :: Γ) Γ' P]
  | @Premise.split _ _ Γ₁ Γ₂ b c c' P Q =>
    return mk ``Premise.split #[← qCtx Γ₁, ← qCtx Γ₂, qBlockKind b, ← qFml Γ c, ← qFml Γ c',
      ← qProg Γ Γ₁ P, ← qProg Γ Γ₂ Q]
  | .check c => return mk ``Premise.check #[← qFml Γ c]
  | .done b => return mk ``Premise.done #[← qCtx Γ', toExpr b]
  | .branches bs => return mk ``Premise.branches #[← qBranches Γ bs]
  | @Premise.allocBranches _ _ bs Q x A Γ₁ P =>
    return mk ``Premise.allocBranches #[← qBranches Γ bs, ← qProg Γ Γ Q, toExpr x, toExpr A,
      ← qCtx Γ₁,
      ← qProg (.mem A :: Γ) Γ₁ P]
  | .cases fs us => do
    let fTy ← fam ``Fml Γ
    let uTy := mkAppN (mkConst ``Upd) #[← contract, ← qCtx Γ, ← qCtx Γ]
    let mut lf := mkApp (mkConst ``List.nil [levelZero]) fTy
    for φ in fs.reverse do
      lf := mkApp3 (mkConst ``List.cons [levelZero]) fTy (← qFml Γ φ) lf
    let mut lu := mkApp (mkConst ``List.nil [levelZero]) uTy
    for U in us.reverse do
      lu := mkApp3 (mkConst ``List.cons [levelZero]) uTy (← qUpd Γ Γ U) lu
    return mk ``Premise.cases #[lf, lu]
  | @Premise.inv _ _ Δ₀ Δ Γ₁ I B xs hv U c c' hu hb P post => do
    let fTy := mkApp2 (mkConst ``Fml) (← contract) (← qCtx Γ)
    let B ← match B with
      | none => pure (optE fTy none)
      | some B => pure (optE fTy (some (← qFml Γ B)))
    return mk ``Premise.inv #[← qCtx Δ₀, ← qCtx Δ, ← qCtx Γ₁, ← qFml Γ I, B, ← qIdxList Γ xs,
      toExpr hv, ← qUpd Γ Δ U, ← qFml Δ c, ← qFml Δ c', ← qExt Γ hu, ← qExt Δ₀ hb,
      ← qProg Δ₀ Γ₁ P, ← qFml Δ₀ post]
  | @Premise.inline _ _ Γ' Γ'' P h =>
    return mk ``Premise.inline #[← qCtx Γ', ← qCtx Γ'', ← qProg Γ Γ'' P, ← qThin Γ' Γ'' h]

end Quote

/-! ## The entry points

Each quotes with every context written out, then hash-conses the result
(`ShareCommon`, Gate G0's condition 7): every copy of a context, and every
other repeated subterm, is one object, which the kernel's caches see once.
The contract is the `Expr` `c` that names it (`mkConst ``StandardExample`). -/

/-- A scoped formula. -/
def Fml.quote {C : Contract} (c : Expr) {Γ : Ctx} (φ : Fml C Γ) : Expr :=
  Lean.ShareCommon.shareCommon ((Quote.qFml Γ φ).run c)

/-- A term of sort `s`. -/
def Tm.quote {C : Contract} (c : Expr) {Γ : Ctx} {s : Srt} (t : Tm C Γ s) : Expr :=
  Lean.ShareCommon.shareCommon ((Quote.qTm Γ s t).run c)

/-- An update. -/
def Upd.quote {C : Contract} (c : Expr) {Γ Δ : Ctx} (U : Upd C Γ Δ) : Expr :=
  Lean.ShareCommon.shareCommon ((Quote.qUpd Γ Δ U).run c)

/-- The frames after a program. -/
def Frames.quote {C : Contract} (c : Expr) {Γ Γ₀ : Ctx} (κ : Frames C Γ Γ₀) : Expr :=
  Lean.ShareCommon.shareCommon ((Quote.qFrames Γ Γ₀ κ).run c)

/-- What a rule leaves (`Stmt.step`'s result). -/
def Premise.quote {C : Contract} (c : Expr) {Γ Γ' : Ctx} (p : Premise C Γ Γ') : Expr :=
  Lean.ShareCommon.shareCommon ((Quote.qPremise Γ Γ' p).run c)

/-! A scoped block on its own is quoted by `Syntax/Quote.lean`'s
`Prog.quoteShared`. -/

/-! ## Explicit quantifiers (decision 28)

A parameter `cdl!` binds and a `∀ uint x;` written in the formula are the
same term, `Fml.all`.  `cdl!` marks the written ones in its output, on the
quoted variable (an `Expr.mdata` the kernel, the compiled code and
unification do not see), so that the tactics can keep an explicit `∀` and
its range at a leaf (`Seq.paramCount`, `Derive.eraseLeaf`) and write its
`allRight` line in the short walk; a formula with no mark (a constant, a
term the strategy computed) reads every leading `∀` as a parameter. -/

/-- The annotation of an explicit `∀`'s variable. -/
def Fml.explicitKey : Lean.Name := `Solidity.explicitAll

/-- A quoted variable marked as an explicit `∀`'s (`explicitKey`). -/
def Fml.markExplicitVar (x : Expr) : Expr :=
  .mdata (Lean.KVMap.empty.insert Fml.explicitKey (.ofBool true)) x

/-- Whether a quoted formula is an explicit `∀` (`explicitKey`). -/
def Fml.isExplicitAll (e : Expr) : Bool :=
  e.isAppOfArity ``Fml.all 5 && match e.getArg! 2 with
    | .mdata d _ => d.getBool Fml.explicitKey
    | _ => false

/-- The leading `∀`s of a quoted formula past its first `n` binders (the
parameters `cdl!` bound, a `∀` or a hidden binder each), marked explicit;
hidden binders between them are passed. -/
partial def Fml.markExplicit (n : Nat) (e : Expr) : Expr :=
  let isAll := e.isAppOfArity ``Fml.all 5
  if isAll || e.isAppOfArity ``Fml.bind 6 then
    let args := e.getAppArgs
    let k := args.size - 1
    let args := args.set! k (Fml.markExplicit (n - 1) args[k]!)
    let args := if isAll && n == 0 then args.set! 2 (Fml.markExplicitVar args[2]!) else args
    mkAppN e.getAppFn args
  else e

/-- `Fml.markExplicit` on both sides of a quoted `Fml.and` (the readings of
`cdl[C, m]{ … }` at the diamond and at the box). -/
def Fml.markExplicitAnd (n₁ n₂ : Nat) (e : Expr) : Expr :=
  if e.isAppOfArity ``Fml.and 4 then
    let args := e.getAppArgs
    mkAppN e.getAppFn
      (args.set! 2 (Fml.markExplicit n₁ args[2]!) |>.set! 3 (Fml.markExplicit n₂ args[3]!))
  else e

end Solidity
