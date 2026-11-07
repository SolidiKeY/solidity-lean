import Solidity.Semantics.Run

/-!
# O02 constant folding over the typed value IR

A total pass on the existing intrinsic `Val C Γ p` (no erased IR). An operator
whose operands are literals is evaluated by the interpreter's own operator
(`BinOp.shortT`, `BinOp.evalT`, `UnOp.evalT`, `ModOp.evalT`). A failing
operation (checked overflow, zero divisor, negative exponent, out-of-range
conversion) is **kept** as written: its halt is an observation, so folding
never turns a failure into a value. A conditional on a literal is replaced by
the branch it takes, and a short-circuit decided by a literal left operand
drops the right operand, exactly as the run skips it. Index expressions inside
storage and memory paths are folded too (`Loc.cfold`, `MLoc.cfold`, …, with
`Loc.cfold_resolveT` and `MLoc.cfold_addrT`).

Preservation is the strongest per-expression relation: for every typed state
the folded expression's result (value or halt) is the original's
(`Val.cfold_evalT`). Expression evaluation reads but does not write the state,
so this relation is not a D6 instance; it implies equality of every
observation of every statement built from the expression
(`Solidity/Optimizer/StmtFold.lean`).
-/
namespace Solidity.Optimizer.ConstFold
open Solidity

variable {C : Contract} {Γ : Ctx}

/-- The value of a state-independent simple value. -/
def _root_.Solidity.Simple.const? : {p : PrimTy} → Simple C Γ p → Option p.Denote
  | p, .lit n h => some (PrimTy.ofLit p n h)
  | _, .bool b => some b
  | _, .local _ => none
  | _, .env _ _ => none

/-- The value of a state-independent literal. -/
def _root_.Solidity.Val.const? : {p : PrimTy} → Val C Γ p → Option p.Denote
  | _, .simple s => s.const?
  | _, .read _ => none
  | _, .binop .. => none
  | _, .unop .. => none
  | _, .ternary .. => none
  | _, .readMem _ => none
  | _, .len .. => none
  | _, .mlen .. => none
  | _, .modular .. => none
  | _, .hash .. => none

/-- Index-generalizing literal view, additive beside the frozen matcher. -/
def _root_.Solidity.Simple.constView? : {p : PrimTy} → Simple C Γ p → Option p.Denote :=
  fun {_} value => Simple.casesOn (motive := fun p _ => Option p.Denote) value
    (fun {p} n h => some (PrimTy.ofLit p n h))
    (fun b => some b)
    (fun {_} _ => none)
    (fun {_} _ _ => none)

/-- The new view agrees with the unchanged matcher on every typed input. -/
theorem _root_.Solidity.Simple.constView?_eq {p : PrimTy} (value : Simple C Γ p) :
    value.constView? = value.const? := by
  cases value <;> rfl

/-- Index-generalizing literal view; existing optimizer callers stay unchanged. -/
def _root_.Solidity.Val.constView? : {p : PrimTy} → Val C Γ p → Option p.Denote :=
  fun {_} value => Val.casesOn (motive_5 := fun p _ => Option p.Denote) value
    (fun {_} s => s.constView?)
    (fun {_} _ => none)
    (fun {_ _} _ _ _ _ _ => none)
    (fun {_ _} _ _ _ _ => none)
    (fun {_} _ _ _ => none)
    (fun {_} _ => none)
    (fun {_ _} _ _ => none)
    (fun {_ _} _ _ => none)
    (fun _ _ _ _ => none)
    (fun {_ _} _ _ _ => none)

/-- Agreement with the frozen matcher, without changing any of its equations. -/
theorem _root_.Solidity.Val.constView?_eq {p : PrimTy} (value : Val C Γ p) :
    value.constView? = value.const? := by
  cases value <;> simp only [Val.constView?, Val.const?, Simple.constView?_eq]

/-- The literal denoting a value of a primitive type. -/
def litV : (p : PrimTy) → p.Denote → Val C Γ p
  | .bool, b => .simple (.bool b)
  | .uint, x => .simple (.lit x.1 x.2)
  | .int, x => .simple (.lit x.1 x.2)

theorem litV_evalT (σ : State C Γ) : ∀ (p : PrimTy) (x : p.Denote),
    (litV p x : Val C Γ p).evalT σ = .ok x
  | .bool, _ => rfl
  | .uint, _ => rfl
  | .int, _ => rfl

theorem litV_const? : ∀ (p : PrimTy) (x : p.Denote), (litV p x : Val C Γ p).const? = some x
  | .bool, _ => rfl
  | .uint, _ => rfl
  | .int, _ => rfl

theorem const?_evalT (σ : State C Γ) {p : PrimTy} {v : Val C Γ p} {x : p.Denote}
    (h : v.const? = some x) : v.evalT σ = .ok x := by
  cases v with
  | simple s =>
    cases s with
    | lit n hn =>
      simp only [Val.const?, Simple.const?, Option.some.injEq] at h
      subst h
      rfl
    | bool b =>
      simp only [Val.const?, Simple.const?, Option.some.injEq] at h
      subst h
      rfl
    | «local» i => simp only [Val.const?, Simple.const?, reduceCtorEq] at h
    | env k hp => simp only [Val.const?, Simple.const?, reduceCtorEq] at h
  | read | binop | unop | ternary | readMem | len | mlen | modular | hash =>
    simp only [Val.const?, reduceCtorEq] at h

/-! ## One node -/

/-- Fold one binary node whose operands are already folded. -/
def foldBin {p q : PrimTy} (op : BinOp) (h : op.accepts p = true) (hq : op.ret p = q)
    (a b : Val C Γ p) : Val C Γ q :=
  match a.const? with
  | none => .binop op h hq a b
  | some x =>
    match op.shortT x with
    | some y => litV q (hq ▸ y)
    | none =>
      match b.const? with
      | none => .binop op h hq a b
      | some y =>
        match op.evalT h x y with
        | some r => litV q (hq ▸ r)
        | none => .binop op h hq a b

/-- Fold one unary node whose operand is already folded. -/
def foldUn {p q : PrimTy} (op : UnOp) (h : op.accepts p = true) (hq : op.ret p = q)
    (a : Val C Γ p) : Val C Γ q :=
  match a.const? with
  | none => .unop op h hq a
  | some x =>
    match op.evalT h x with
    | some r => litV q (hq ▸ r)
    | none => .unop op h hq a

/-- A conditional on a literal is the branch it takes. -/
def foldTern {p : PrimTy} (c : Val C Γ .bool) (a b : Val C Γ p) : Val C Γ p :=
  match c.const? with
  | none => .ternary c a b
  | some v => if boolT v then a else b

/-- `addmod`/`mulmod` of literals; a zero modulus keeps its failure. -/
def foldMod (op : ModOp) (a b k : Val C Γ .uint) : Val C Γ .uint :=
  match a.const?, b.const?, k.const? with
  | some x, some y, some m =>
    match op.evalT x y m with
    | some r => litV .uint r
    | none => .modular op a b k
  | _, _, _ => .modular op a b k

theorem foldBin_evalT (σ : State C Γ) {p q : PrimTy} (op : BinOp) (h : op.accepts p = true)
    (hq : op.ret p = q) (a b : Val C Γ p) :
    (foldBin op h hq a b).evalT σ = (Val.binop op h hq a b).evalT σ := by
  subst hq
  unfold foldBin
  cases ha : a.const? with
  | none => rfl
  | some x =>
    have ea : a.evalT σ = .ok x := const?_evalT σ ha
    cases hs : op.shortT x with
    | some y =>
      simp only [litV_evalT, Val.evalT, ea, hs, bind, Except.bind, pure, Except.pure]
    | none =>
      cases hb : b.const? with
      | none => simp only [hs]
      | some y =>
        have eb : b.evalT σ = .ok y := const?_evalT σ hb
        cases he : op.evalT h x y with
        | some r =>
          simp only [litV_evalT, Val.evalT, ea, eb, hs, he, bind, Except.bind, TRes.ofOpt]
        | none => simp only [hs, he]

theorem foldUn_evalT (σ : State C Γ) {p q : PrimTy} (op : UnOp) (h : op.accepts p = true)
    (hq : op.ret p = q) (a : Val C Γ p) :
    (foldUn op h hq a).evalT σ = (Val.unop op h hq a).evalT σ := by
  subst hq
  unfold foldUn
  cases ha : a.const? with
  | none => rfl
  | some x =>
    have ea : a.evalT σ = .ok x := const?_evalT σ ha
    cases he : op.evalT h x with
    | some r => simp only [litV_evalT, Val.evalT, ea, he, bind, Except.bind, TRes.ofOpt]
    | none => simp only [he]

theorem foldTern_evalT (σ : State C Γ) {p : PrimTy} (c : Val C Γ .bool) (a b : Val C Γ p) :
    (foldTern c a b).evalT σ = (Val.ternary c a b).evalT σ := by
  unfold foldTern
  cases hc : c.const? with
  | none => rfl
  | some v =>
    have ec : c.evalT σ = .ok v := const?_evalT σ hc
    simp only [Val.evalT, ec, bind, Except.bind]
    cases boolT v <;> rfl

theorem foldMod_evalT (σ : State C Γ) (op : ModOp) (a b k : Val C Γ .uint) :
    (foldMod op a b k).evalT σ = (Val.modular op a b k).evalT σ := by
  unfold foldMod
  cases ha : a.const? with
  | none => rfl
  | some x =>
    cases hb : b.const? with
    | none => rfl
    | some y =>
      cases hk : k.const? with
      | none => rfl
      | some m =>
        cases he : op.evalT x y m with
        | some r =>
          simp only [litV_evalT, Val.evalT, const?_evalT σ ha, const?_evalT σ hb,
            const?_evalT σ hk, he, bind, Except.bind, TRes.ofOpt]
        | none => simp only [he]

/-! ## The pass -/

mutual
/-- Fold the index expressions of a storage path. -/
def _root_.Solidity.SPath.cfold : {T : Ty} → SPath C Γ T → SPath C Γ T
  | _, .alias i => .alias i
  | _, .loc l => .loc l.cfold

/-- Fold the index expressions of a storage location. -/
def _root_.Solidity.Loc.cfold : {T : Ty} → Loc C Γ T → Loc C Γ T
  | _, .root r h => .root r h
  | _, .field b f h => .field b.cfold f h
  | _, .index it b i => .index it b.cfold i.cfold

/-- Fold the index expressions of a memory path. -/
def _root_.Solidity.MPath.cfold : {T : Ty} → MPath C Γ T → MPath C Γ T
  | _, .var i hm => .var i hm
  | _, .loc l => .loc l.cfold

/-- Fold the index expressions of a memory location. -/
def _root_.Solidity.MLoc.cfold : {T : Ty} → MLoc C Γ T → MLoc C Γ T
  | _, .field b f h => .field b.cfold f h
  | _, .index a b i => .index a b.cfold i.cfold

/-- Bottom-up constant folding, including the index expressions of storage and
memory paths. -/
def _root_.Solidity.Val.cfold : {p : PrimTy} → Val C Γ p → Val C Γ p
  | _, .binop op h hq a b => foldBin op h hq a.cfold b.cfold
  | _, .unop op h hq a => foldUn op h hq a.cfold
  | _, .ternary c a b => foldTern c.cfold a.cfold b.cfold
  | _, .modular op a b k => foldMod op a.cfold b.cfold k.cfold
  | _, .simple s => .simple s
  | _, .read l => .read l.cfold
  | _, .readMem l => .readMem l.cfold
  | _, .len b hp => .len b.cfold hp
  | _, .mlen b hp => .mlen b.cfold hp
  | _, .hash k b hp => .hash k b.cfold hp
end

mutual
theorem _root_.Solidity.SPath.cfold_resolveT (σ : State C Γ) : {T : Ty} → (b : SPath C Γ T) →
    b.cfold.resolveT σ = b.resolveT σ
  | _, .alias _ => rfl
  | _, .loc l => by simp only [SPath.cfold, SPath.resolveT, Loc.cfold_resolveT σ l]

theorem _root_.Solidity.Loc.cfold_resolveT (σ : State C Γ) : {T : Ty} → (l : Loc C Γ T) →
    l.cfold.resolveT σ = l.resolveT σ
  | _, .root .. => rfl
  | _, .field b f h => by simp only [Loc.cfold, Loc.resolveT, SPath.cfold_resolveT σ b]
  | _, .index it b i => by
    simp only [Loc.cfold, Loc.resolveT, SPath.cfold_resolveT σ b, Val.cfold_evalT σ i]

theorem _root_.Solidity.MPath.cfold_mvalT (σ : State C Γ) : {T : Ty} → (b : MPath C Γ T) →
    b.cfold.mvalT σ = b.mvalT σ
  | _, .var .. => rfl
  | _, .loc l => by simp only [MPath.cfold, MPath.mvalT, MLoc.cfold_addrT σ l]

theorem _root_.Solidity.MLoc.cfold_addrT (σ : State C Γ) : {T : Ty} → (l : MLoc C Γ T) →
    l.cfold.addrT σ = l.addrT σ
  | _, .field b f h => by simp only [MLoc.cfold, MLoc.addrT, MPath.cfold_mvalT σ b]
  | _, .index a b i => by
    simp only [MLoc.cfold, MLoc.addrT, MPath.cfold_mvalT σ b, Val.cfold_evalT σ i]

/-- **Constant folding preserves every result**, value or halt, in every
typed state. -/
theorem _root_.Solidity.Val.cfold_evalT (σ : State C Γ) : {p : PrimTy} → (v : Val C Γ p) →
    v.cfold.evalT σ = v.evalT σ
  | _, .binop op h hq a b => by
    rw [Val.cfold, foldBin_evalT]
    simp only [Val.evalT, Val.cfold_evalT σ a, Val.cfold_evalT σ b]
  | _, .unop op h hq a => by
    rw [Val.cfold, foldUn_evalT]
    simp only [Val.evalT, Val.cfold_evalT σ a]
  | _, .ternary c a b => by
    rw [Val.cfold, foldTern_evalT]
    simp only [Val.evalT, Val.cfold_evalT σ c, Val.cfold_evalT σ a, Val.cfold_evalT σ b]
  | _, .modular op a b k => by
    rw [Val.cfold, foldMod_evalT]
    simp only [Val.evalT, Val.cfold_evalT σ a, Val.cfold_evalT σ b, Val.cfold_evalT σ k]
  | _, .simple _ => rfl
  | _, .read l => by simp only [Val.cfold, Val.evalT, Loc.cfold_resolveT σ l]
  | _, .readMem l => by simp only [Val.cfold, Val.evalT, MLoc.cfold_addrT σ l]
  | _, .len b hp => by simp only [Val.cfold, Val.evalT, SPath.cfold_resolveT σ b]
  | _, .mlen b hp => by simp only [Val.cfold, Val.evalT, MPath.cfold_mvalT σ b]
  | _, .hash k b hp => by simp only [Val.cfold, Val.evalT, MPath.cfold_mvalT σ b]
end

end Solidity.Optimizer.ConstFold
