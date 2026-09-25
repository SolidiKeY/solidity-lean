import Solidity.Kernel.Syntax
import Solidity.Typing.Soundness

/-!
# Erasure

A kernel term erases to the untyped AST the interpreter, the rule table and
every existing soundness proof run on.  The erasure spells each name the way
the rule table does — a root as `fieldFor r T (some .global)`, an alias as
`Rules.aliasField`, a member as `fieldFor f T` — so a residual the table
computes and the erasure of the kernel's residual are the same term.

The headline is `Stmt.erase_wt`: **the erasure of a kernel statement is
well-typed**, with no hypothesis.  Whatever `stmtWt` checks at a node, the
kernel constructor for it carries as a proof, so the typed terms are among the
well-typed ones; `Prog.erase_wt` is the same for a block.
-/

namespace Solidity
namespace Kernel

open Semantics

mutual

def SPath.erase {C : Contract} {Γ : Ctx} {T : Ty} : SPath C Γ T → WrappedExpr
  | .alias (R := R) x _ => .var .storage (.ref R) (Field.identity x R (some .local))
  | .loc l => l.erase

def Loc.erase {C : Contract} {Γ : Ctx} {T : Ty} : Loc C Γ T → WrappedExpr
  | .root (T := T) r _ _ => .var .storage T (SoliditySyntax.fieldFor r T (some .global))
  | .field (T := T) b f _ => .field .storage T b.erase (SoliditySyntax.fieldFor f T)
  | .mapIndex (V := V) b i => .index .storage V b.erase i.erase
  | .arrIndex (E := E) b i => .index .storage E b.erase i.erase

def Val.erase {C : Contract} {Γ : Ctx} {p : PrimTy} : Val C Γ p → WrappedExpr
  | .lit (p := p) n _ => .intLit (.prim p) n
  | .bool b => .bool b
  | .local (p := p) x _ => .var .stack (.prim p) (Field.primitive x (.prim p))
  | .read l => l.erase
  | .binop op _ a b => .mkBinop op a.erase b.erase
  | .unop op _ a => .mkUnop op a.erase

end

def Src.erase {C : Contract} {Γ : Ctx} {T : Ty} : Src C Γ T → WrappedExpr
  | .val v => v.erase
  | .copy p _ => p.erase

/-! ## Erasure keeps the type -/

mutual

/-- A path erases at its type: `alice.account` is annotated `Account`. -/
theorem SPath.erase_ty {C : Contract} {Γ : Ctx} {T : Ty} :
    (p : SPath C Γ T) → p.erase.ty = T
  | .alias .. => rfl
  | .loc l => l.erase_ty

/-- A location erases at its type: `balances[i]` is annotated `uint`. -/
theorem Loc.erase_ty {C : Contract} {Γ : Ctx} {T : Ty} :
    (l : Loc C Γ T) → l.erase.ty = T
  | .root .. | .field .. | .mapIndex .. | .arrIndex .. => rfl

/-- A value erases at its type: `alice.age < 3` is annotated `bool`. -/
theorem Val.erase_ty {C : Contract} {Γ : Ctx} {p : PrimTy} :
    (v : Val C Γ p) → v.erase.ty = .prim p
  | .lit .. | .bool _ | .local .. => rfl
  | .read l => l.erase_ty
  | .binop op _ a _ => by
      simp only [Val.erase, Typed.WrappedExpr.ty, a.erase_ty, BinOp.retTy_prim]
  | .unop op _ a => by
      simp only [Val.erase, Typed.WrappedExpr.ty, a.erase_ty, UnOp.retTy_prim]

end

/-- A source erases at its type: in `folks[1] = bob;` the source is a `Person`. -/
theorem Src.erase_ty {C : Contract} {Γ : Ctx} {T : Ty} :
    (r : Src C Γ T) → r.erase.ty = T
  | .val v => v.erase_ty
  | .copy p _ => p.erase_ty

/-! ## Erasure is well-typed -/

mutual

/-- A path erases to a well-annotated expression: in `p.age`, `p` is the
local alias `Γ` binds, marked local. -/
theorem SPath.erase_wt {C : Contract} {Γ : Ctx} {T : Ty} :
    (p : SPath C Γ T) → wtExpr Γ C.layout p.erase = true
  | .alias x h => by simp [SPath.erase, wtExpr, h, Field.identity]
  | .loc l => l.erase_wt

/-- A location erases to a well-annotated expression: `alice.age` is the
root `alice`, marked global because no local shadows it, then `Person`'s
`age`. -/
theorem Loc.erase_wt {C : Contract} {Γ : Ctx} {T : Ty} :
    (l : Loc C Γ T) → wtExpr Γ C.layout l.erase = true
  | .root r hΓ h => by
      have h' : lookupBy r C.vars = some T := h
      cases T <;> simp [Loc.erase, wtExpr, hΓ, SoliditySyntax.fieldFor, Field.identity,
        Field.primitive, Contract.layout, h']
  | .field b f h => by
      have h' : lookupBy f (structDef _) = some _ := h
      simp [Loc.erase, wtExpr, b.erase_wt, b.erase_ty, segTy, SoliditySyntax.fieldFor]
      split <;> exact h'
  | .mapIndex b i => by
      simp [Loc.erase, wtExpr, b.erase_wt, i.erase_wt, b.erase_ty, elemTy]
  | .arrIndex b i => by
      simp [Loc.erase, wtExpr, b.erase_wt, i.erase_wt, b.erase_ty, elemTy]

/-- A value erases to a well-annotated expression: in `x + 1`, `x` is the
stack local `Γ` binds and `1` a number literal. -/
theorem Val.erase_wt {C : Contract} {Γ : Ctx} {p : PrimTy} :
    (v : Val C Γ p) → wtExpr Γ C.layout v.erase = true
  | .lit n h => by simp [Val.erase, wtExpr, isNumericTy, h]
  | .bool _ => rfl
  | .local x h => by simp [Val.erase, wtExpr, h, Field.primitive]
  | .read l => l.erase_wt
  | .binop _ _ a b => by simp [Val.erase, wtExpr, a.erase_wt, b.erase_wt]
  | .unop _ _ a => by simp [Val.erase, wtExpr, a.erase_wt]

end

/-- A source erases to a well-annotated expression, value or path. -/
theorem Src.erase_wt {C : Contract} {Γ : Ctx} {T : Ty} :
    (r : Src C Γ T) → wtExpr Γ C.layout r.erase = true
  | .val v => v.erase_wt
  | .copy p _ => p.erase_wt

/-! ## Statements -/

/-- A path erases to a place: every path is assignable. -/
def SPath.toPlace {C : Contract} {Γ : Ctx} {T : Ty} (p : SPath C Γ T) : PlaceExpr :=
  ⟨p.erase, by
    cases p with
    | alias => rfl
    | loc l => cases l <;> rfl⟩

def Loc.toPlace {C : Contract} {Γ : Ctx} {T : Ty} (l : Loc C Γ T) : PlaceExpr :=
  (SPath.loc l).toPlace

mutual

def Stmt.erase {C : Contract} {Γ Γ' : Ctx} : Stmt C Γ Γ' → Solidity.Stmt
  | .assign l r => .assign l.toPlace r.erase
  | .rebind (R := R) x _ r =>
      .assign (PlaceExpr.var .storage (.ref R) (Field.identity x R (some .local))) r.erase
  | .assignLocal (p := p) x _ r =>
      .assign (PlaceExpr.var .stack (.prim p) (Field.primitive x (.prim p))) r.erase
  | .declLocal p x init => .stackDecl (.prim p) x (init.map Val.erase)
  | .declStorage R x init => .storageDecl (.ref R) x (some init.erase)
  | .declStorageSkip R x => .storageDecl (.ref R) x none
  | .bindAlias R x init => .storagePlaceAlias (.ref R) x init.erase
  | .delete l => .delete l.toPlace
  | .ite c thn els => .ite c.erase thn.erase els.erase
  | .require c => .requireStmt c.erase
  | .assert c => .assertStmt c.erase
  | .revert => .revert none

def Prog.erase {C : Contract} {Γ Γ' : Ctx} : Prog C Γ Γ' → List Solidity.Stmt
  | .nil => []
  | .cons s P => s.erase :: P.erase

end

mutual

/-- **Erasure is well-typed.** A kernel statement from `Γ` to `Γ'` erases
to a statement `stmtWt` accepts at `Γ` with result `Γ'`, against the
contract's layout.  `uint x = alice.age;` in `StandardExample` is accepted
and binds `x : uint`, with no side condition left to check. -/
theorem Stmt.erase_wt {C : Contract} {Γ Γ' : Ctx} :
    (s : Stmt C Γ Γ') → stmtWt Γ C.layout s.erase = some Γ'
  | .assign l r => by
      simp [Stmt.erase, stmtWt, Loc.toPlace, SPath.toPlace, SPath.erase, l.erase_wt,
        r.erase_wt, l.erase_ty, r.erase_ty]
  | .rebind x h r => by
      simp [Stmt.erase, stmtWt, PlaceExpr.var, wtExpr, h, Field.identity, r.erase_wt,
        r.erase_ty, Typed.WrappedExpr.ty]
  | .assignLocal x h r => by
      simp [Stmt.erase, stmtWt, PlaceExpr.var, wtExpr, h, Field.primitive, r.erase_wt,
        r.erase_ty, Typed.WrappedExpr.ty]
  | .declLocal p x init => by
      cases init <;> simp [Stmt.erase, stmtWt, Ty.isPrimitive, Val.erase_wt, Val.erase_ty]
  | .declStorage R x init => by
      simp [Stmt.erase, stmtWt, init.erase_wt, init.erase_ty]
  | .declStorageSkip R x => rfl
  | .bindAlias R x init => by
      simp [Stmt.erase, stmtWt, init.erase_wt, init.erase_ty]
  | .delete l => by
      simp [Stmt.erase, stmtWt, Loc.toPlace, SPath.toPlace, SPath.erase, l.erase_wt]
      cases l <;> rfl
  | .ite c thn els => by
      simp [Stmt.erase, stmtWt, c.erase_wt, thn.erase_wt, els.erase_wt]
  | .require c => by simp [Stmt.erase, stmtWt, c.erase_wt]
  | .assert c => by simp [Stmt.erase, stmtWt, c.erase_wt]
  | .revert => rfl

/-- `Stmt.erase_wt` for a block: `blockWt` threads the same contexts. -/
theorem Prog.erase_wt {C : Contract} {Γ Γ' : Ctx} :
    (P : Prog C Γ Γ') → blockWt Γ C.layout P.erase = some Γ'
  | .nil => rfl
  | .cons s P => by simp [Prog.erase, blockWt, s.erase_wt, P.erase_wt]

end

end Kernel
end Solidity
