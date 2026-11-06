import Solidity.Source.StmtProgress
import Solidity.Lowering.P9.DeclarationIdentity

/-! Constructive decision procedures for the existing call-closed value fragment.
The propositions and source interpreter remain those on master.
-/
namespace Solidity.Source
namespace Calls
variable {E : Env}

private instance rationalDec (σ : STy) : Decidable (∃ q, σ = .rational q) := by
  cases σ <;> first
    | exact isTrue ⟨_, rfl⟩
    | exact isFalse (by rintro ⟨q, h⟩; cases h)

private instance hexDec (σ : STy) : Decidable (∃ q k, σ = .hexConst q k) := by
  cases σ <;> first
    | exact isTrue ⟨_, _, rfl⟩
    | exact isFalse (by rintro ⟨q, k, h⟩; cases h)

private instance mappingDec (σ : STy) : Decidable (∃ k v, σ = .mapping k v) := by
  cases σ <;> first
    | exact isTrue ⟨_, _, rfl⟩
    | exact isFalse (by rintro ⟨k, v, h⟩; cases h)

instance fragSrcDec (σ : STy) : Decidable σ.FragSrc :=
  inferInstanceAs (Decidable (σ.isValue = true ∨ (∃ q, σ = .rational q) ∨ (∃ q k, σ = .hexConst q k)))

mutual

def exprDec (A : Decl → Prop) [DecidablePred A] {Γ : RCtx} :
    {τ : STy} → (e : RExpr E Γ τ) → Decidable (e.ValFragC A)
  | _, .const _ | _, .bytesLit _ _ | _, .addressLit _ | _, .bool _ | _, .this _ | _, .compareConst _ _ _ => isTrue trivial
  | τ, .local _ => by exact inferInstanceAs (Decidable (τ.isValue = true))
  | τ, .state d _ => by exact inferInstanceAs (Decidable (d.isConst = false ∧ τ.byRef = false ∧ E.cellTy d.path = τ ∧ (Val.default E.layout τ).isSome = true ∧ τ.isValue = true))
  | τ, .unary _ a => by letI := exprDec A a; exact inferInstanceAs (Decidable (RExpr.ValFragC A a ∧ τ.isValue = true))
  | τ, .binary _ a b => by letI := exprDec A a; letI := exprDec A b; exact inferInstanceAs (Decidable (RExpr.ValFragC A a ∧ RExpr.ValFragC A b ∧ τ.isValue = true))
  | _, .compare (τ := τ) _ a b => by letI := exprDec A a; letI := exprDec A b; exact inferInstanceAs (Decidable (RExpr.ValFragC A a ∧ RExpr.ValFragC A b ∧ τ.isValue = true))
  | τ, .shiftLike _ a b _ => by letI := exprDec A a; letI := exprDec A b; exact inferInstanceAs (Decidable (RExpr.ValFragC A a ∧ RExpr.ValFragC A b ∧ τ.isValue = true))
  | τ, .cond c a b => by letI := exprDec A c; letI := exprDec A a; letI := exprDec A b; exact inferInstanceAs (Decidable (RExpr.ValFragC A c ∧ RExpr.ValFragC A a ∧ RExpr.ValFragC A b ∧ τ.isValue = true))
  | τ, .conv (σ := σ) a _ => by letI := exprDec A a; exact inferInstanceAs (Decidable (RExpr.ValFragC A a ∧ τ.isValue = true ∧ (σ.isValue = true ∨ (∃ q, σ = .rational q) ∨ (∃ q k, σ = .hexConst q k))))
  | τ, .assign l e => by letI := exprDec A e; letI := lvalDec A l; exact inferInstanceAs (Decidable (RLVal.IsSimpleC A l ∧ RExpr.ValFragC A e ∧ τ.isValue = true))
  | τ, .compound (σ := σ) _ l e _ => by letI := exprDec A e; letI := lvalDec A l; exact inferInstanceAs (Decidable (RLVal.IsSimpleC A l ∧ RExpr.ValFragC A e ∧ τ.isValue = true ∧ (σ.isValue = true ∨ (∃ q, σ = .rational q) ∨ (∃ q k, σ = .hexConst q k))))
  | _, .incDec _ _ l => by letI := lvalDec A l; exact inferInstanceAs (Decidable (RLVal.IsSimpleC A l))
  | τv, .indexMapping (τk := τk) a k => by letI := exprDec A k; letI := mapDec A a; exact inferInstanceAs (Decidable (RExpr.MapRefC A a ∧ RExpr.ValFragC A k ∧ τk.keyable = true ∧ τv.isValue = true ∧ (Val.default E.layout τv).isSome = true))
  | _, .call d _ args => by letI := argsDec A args; exact inferInstanceAs (Decidable (A d ∧ RConvArgs.ValFragC A args))
  | _, .str .. | _, .tuple .. | _, .convExplicit .. | _, .delete .. | _, .indexArray .. | _, .indexBytes .. | _, .length .. | _, .payable .. | _, .magic .. | _, .balance .. | _, .builtin .. | _, .member .. | _, .structNew .. | _, .extCall .. | _, .transfer .. | _, .send .. | _, .abiEncode .. | _, .assignCopy .. | _, .abiDecode .. | _, .slice .. | _, .inlineArray .. | _, .newArray .. => isFalse (by intro h; exact h)

def mapDec (A : Decl → Prop) [DecidablePred A] {Γ : RCtx} :
    {τ : STy} → (e : RExpr E Γ τ) → Decidable (e.MapRefC A)
  | τ, .state d _ => by exact inferInstanceAs (Decidable (d.isConst = false ∧ E.pathTy d.path = some τ ∧ (∃ k v, τ = .mapping k v)))
  | τv, .indexMapping (τk := τk) a k => by letI := exprDec A k; letI := mapDec A a; exact inferInstanceAs (Decidable (RExpr.MapRefC A a ∧ RExpr.ValFragC A k ∧ τk.keyable = true ∧ (∃ k' v', τv = .mapping k' v')))
  | _, .const .. | _, .bytesLit .. | _, .addressLit .. | _, .bool .. | _, .str .. | _, .local .. | _, .this .. | _, .tuple .. | _, .conv .. | _, .convExplicit .. | _, .unary .. | _, .incDec .. | _, .delete .. | _, .binary .. | _, .compare .. | _, .compareConst .. | _, .shiftLike .. | _, .cond .. | _, .assign .. | _, .compound .. | _, .indexArray .. | _, .indexBytes .. | _, .length .. | _, .payable .. | _, .call .. | _, .magic .. | _, .balance .. | _, .builtin .. | _, .member .. | _, .structNew .. | _, .extCall .. | _, .transfer .. | _, .send .. | _, .abiEncode .. | _, .assignCopy .. | _, .abiDecode .. | _, .slice .. | _, .inlineArray .. | _, .newArray .. => isFalse (by intro h; exact h)

def lvalDec (A : Decl → Prop) [DecidablePred A] {Γ : RCtx} :
    {τ : STy} → (l : RLVal E Γ τ) → Decidable (l.IsSimpleC A)
  | _, .local _ => isTrue trivial
  | τ, .state d _ _ => by exact inferInstanceAs (Decidable (τ.byRef = false ∧ E.cellTy d.path = τ ∧ (Val.default E.layout τ).isSome = true))
  | τv, .indexMapping (τk := τk) a k => by letI := exprDec A k; letI := mapDec A a; exact inferInstanceAs (Decidable (RExpr.MapRefC A a ∧ RExpr.ValFragC A k ∧ τk.keyable = true ∧ τv.isValue = true ∧ (Val.default E.layout τv).isSome = true))
  | _, .indexArray .. | _, .indexBytes .. | _, .member .. => isFalse (by intro h; exact h)

def argsDec (A : Decl → Prop) [DecidablePred A] {Γ : RCtx} :
    {τs : List STy} → (es : RConvArgs E Γ τs) → Decidable (es.ValFragC A)
  | _, .nil => isTrue trivial
  | _, .cons (σ := σ) (τ := τ) e _ es => by letI := exprDec A e; letI := argsDec A es; exact inferInstanceAs (Decidable (RExpr.ValFragC A e ∧ τ.isValue = true ∧ (σ.isValue = true ∨ (∃ q, σ = .rational q) ∨ (∃ q k, σ = .hexConst q k)) ∧ RConvArgs.ValFragC A es))

end

attribute [instance] exprDec mapDec lvalDec argsDec

instance optBoolDec (A : Decl → Prop) [DecidablePred A] {Γ : RCtx} :
    (x : ROptBool E Γ) → Decidable (x.ValFragC A)
  | .none => isTrue trivial
  | .some c => inferInstanceAs (Decidable (RExpr.ValFragC A c))

instance optExprDec (A : Decl → Prop) [DecidablePred A] {Γ : RCtx} :
    (x : ROptExpr E Γ) → Decidable (x.ValFragC A)
  | .none => isTrue trivial
  | .some (τ := τ) e => inferInstanceAs (Decidable (RExpr.ValFragC A e ∧ τ.isValue = true))

instance simpleDec {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') :
    Decidable s.Simple := by
  cases s <;> first | exact isTrue trivial | exact isFalse (by intro h; exact h)

mutual

def stmtDec (A : Decl → Prop) [DecidablePred A] {R : List STy} {M : Bool} :
    {k : SCtx} → {Γ Γ' : RCtx} → (s : RStmt E R M k Γ Γ') → Decidable (s.ValFragC A)
  | _, _, _, .expr e => by letI := exprDec A e; exact inferInstanceAs (Decidable (RExpr.ValFragC A e))
  | _, _, _, .declVar τ => by exact inferInstanceAs (Decidable ((Val.default E.layout τ).isSome = true))
  | _, _, _, .declInit (σ := σ) (τ := τ) e _ => by letI := exprDec A e; exact inferInstanceAs (Decidable (RExpr.ValFragC A e ∧ τ.isValue = true ∧ σ.FragSrc))
  | _, _, _, .block b => by letI := itemsDec A b; exact inferInstanceAs (Decidable (RItems.ValFragC A b))
  | _, _, _, .ifThen c s => by letI := exprDec A c; letI := stmtDec A s; exact inferInstanceAs (Decidable (RExpr.ValFragC A c ∧ RStmt.ValFragC A s))
  | _, _, _, .ifElse c s t => by letI := exprDec A c; letI := stmtDec A s; letI := stmtDec A t; exact inferInstanceAs (Decidable (RExpr.ValFragC A c ∧ RStmt.ValFragC A s ∧ RStmt.ValFragC A t))
  | _, _, _, .whileLoop c s => by letI := exprDec A c; letI := stmtDec A s; exact inferInstanceAs (Decidable (RExpr.ValFragC A c ∧ RStmt.ValFragC A s))
  | _, _, _, .doWhile s c => by letI := exprDec A c; letI := stmtDec A s; exact inferInstanceAs (Decidable (RStmt.ValFragC A s ∧ RExpr.ValFragC A c))
  | _, _, _, .forLoop i c p s => by letI := stmtDec A i; letI := stmtDec A s; exact inferInstanceAs (Decidable (i.Simple ∧ RStmt.ValFragC A i ∧ ROptBool.ValFragC A c ∧ ROptExpr.ValFragC A p ∧ RStmt.ValFragC A s))
  | _, _, _, .skip | _, _, _, .brk | _, _, _, .cont | _, _, _, .ret _ => isTrue trivial
  | _, _, _, .retVal (σ := σ) (τ := τ) _ e _ => by letI := exprDec A e; exact inferInstanceAs (Decidable (RExpr.ValFragC A e ∧ τ.isValue = true ∧ σ.FragSrc))
  | _, _, _, .retTuple es => by letI := argsDec A es; exact inferInstanceAs (Decidable (RConvArgs.ValFragC A es))
  | _, _, _, .placeholder .. | _, _, _, .emit .. | _, _, _, .revertError .. | _, _, _, .rethrow .. | _, _, _, .declTuple .. | _, _, _, .tryCall .. => isFalse (by intro h; exact h)

def itemsDec (A : Decl → Prop) [DecidablePred A] {R : List STy} {M : Bool} :
    {k : SCtx} → {Γ Γ' : RCtx} → (b : RItems E R M k Γ Γ') → Decidable (b.ValFragC A)
  | _, _, _, .nil => isTrue trivial
  | _, _, _, .stmt s rest => by letI := stmtDec A s; letI := itemsDec A rest; exact inferInstanceAs (Decidable (RStmt.ValFragC A s ∧ RItems.ValFragC A rest))
  | _, _, _, .unchecked b rest => by letI := itemsDec A b; letI := itemsDec A rest; exact inferInstanceAs (Decidable (RItems.ValFragC A b ∧ RItems.ValFragC A rest))

end

attribute [instance] stmtDec itemsDec
end Calls
end Solidity.Source
