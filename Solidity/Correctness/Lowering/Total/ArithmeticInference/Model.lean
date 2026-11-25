import Solidity.Correctness.Lowering.Total.ArithmeticInference.Steps
import Solidity.Correctness.Lowering.Total.Decode.Tables

/-!
# Model operators and their Source spelling

Which model operators spell the arithmetic Source forms (`family`,
`binop_family`): `add sub mul div mod` are `+ - * / %`, `band bor bxor` are
`& | ^`, `shl` is `<<` and `shr` is `sar`, `pow` is `**`, `lt gt le ge` and
`eqB neB` the comparisons; `and`/`or` are spelled but not of this family, and
the wrapping forms are not spelled. `fold` mirrors `Syn.const` on the spelling
(`fold_spec`: a folding model expression is spelled by every decoder version
and meets `tryConst`'s premises), and `depth` is the least fuel at which the
spelling infers.
-/

namespace Solidity.Correctness.Lowering.Total.ArithmeticInference

open Source (STy Syn Ctx Typed BinKind Inferred Q)
open Decode (Tables)

/-- The family a model operator's Source spelling belongs to. `&&`, `||` are
the scalar lane's; the wrapping forms have no Source spelling. -/
def family : BinOp → Option Family
  | .add | .sub | .mul | .div | .mod => some .arith
  | .band | .bor | .bxor => some .bit
  | .shl | .shr => some .shift
  | .pow => some .exp
  | .lt | .gt | .le | .ge => some .order
  | .eqB | .neB => some .eq
  | .and | .or | .addW | .subW | .mulW | .powW => none

/-- `/` and `%`. -/
def divMod : BinOp → Bool
  | .div | .mod => true
  | _ => false

/-- A comparison operator. -/
def cmpOp (op : BinOp) : Bool := (family op).any Family.cmp

/-- `Syn.const` on the spelling of a binary operator, from its operands' constants. -/
def foldBin : BinOp → Option Q → Option Q → Option Q
  | .add, qa, qb => do ((← qa).add (← qb)).bounded
  | .sub, qa, qb => do ((← qa).sub (← qb)).bounded
  | .mul, qa, qb => do ((← qa).mul (← qb)).bounded
  | .div, qa, qb => do (← (← qa).div (← qb)).bounded
  | .mod, qa, qb => do (← (← qa).mod (← qb)).bounded
  | .pow, qa, qb => do
      let k ← (← qb).int?
      (← qa).pow k
  | .shl, qa, qb => do
      let x ← (← qa).int?
      let y ← (← qb).int?
      if x = 0 ∧ 0 ≤ y then pure (Q.ofInt 0)
      else if 0 ≤ y ∧ Q.bitLen x.natAbs + y.toNat ≤ Q.maxBits + 1 then pure (Q.ofInt (x * 2 ^ y.toNat))
      else Option.none
  | .shr, qa, qb => do
      let x ← (← qa).int?
      let y ← (← qb).int?
      if 0 ≤ y then pure (Q.ofInt (if y.toNat ≤ Source.maxShift then x.fdiv (2 ^ y.toNat) else if x < 0 then -1 else 0))
      else Option.none
  | .band, qa, qb => do
      pure (Q.ofInt (Source.Int.bitAnd (← (← qa).int?) (← (← qb).int?)))
  | .bor, qa, qb => do
      pure (Q.ofInt (Source.Int.bitOr (← (← qa).int?) (← (← qb).int?)))
  | .bxor, qa, qb => do
      pure (Q.ofInt (Source.Int.bitXor (← (← qa).int?) (← (← qb).int?)))
  | _, _, _ => none

/-- The constant the spelling of a model expression folds to (`Syn.const`). -/
def fold : RawExpr → Option Q
  | .num n => some (Source.NumLit.dec n 0 0).value
  | .binop op a b => foldBin op (fold a) (fold b)
  | .unop .neg a => (fold a).map Q.neg
  | .unop .bnot a => do
      let k ← (← fold a).int?
      pure (Q.ofInt (Source.Int.bitNot k))
  | _ => none

/-- Both operands are constants. -/
def bothConst (a b : RawExpr) : Bool := (fold a).isSome && (fold b).isSome

/-- The least fuel at which the spelling infers: one for a constant, a local
or a comparison of constants, else one more than the operands need. -/
def depth : RawExpr → Nat
  | .binop op a b =>
    if (fold (.binop op a b)).isSome || (cmpOp op && bothConst a b) then 1
    else max (depth a) (depth b) + 1
  | .unop op a => if (fold (.unop op a)).isSome then 1 else depth a + 1
  | _ => 1

theorem binop_family {op : BinOp} {k : Family} (h : family op = some k) :
    ∃ f, Decode.binop op = some f ∧ ∀ a b : Syn .expr,
      (f a b).binOp? = some (k.kind, a, b) ∧ (f a b).isDivMod = divMod op ∧
      (f a b).const = foldBin op a.const b.const ∧ (f a b).isAddressLit = false ∧
      (f a b).hexLen? = none := by
  cases op <;> cases h <;> exact ⟨_, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

theorem foldBin_some {op : BinOp} {qa qb : Option Q} {q : Q} (h : foldBin op qa qb = some q) :
    ∃ k x y, family op = some k ∧ k.cmp = false ∧ qa = some x ∧ qb = some y := by
  cases qa <;> cases qb <;> cases op <;>
    first | exact ⟨_, _, _, rfl, rfl, rfl, rfl⟩ | (simp [foldBin] at h; done)

theorem foldBin_none_left {op : BinOp} {qb : Option Q} : foldBin op none qb = none := by
  cases h : foldBin op none qb with
  | none => rfl
  | some q => obtain ⟨_, _, _, _, _, h, _⟩ := foldBin_some h; cases h

theorem foldBin_none_right {op : BinOp} {qa : Option Q} : foldBin op qa none = none := by
  cases h : foldBin op qa none with
  | none => rfl
  | some q => obtain ⟨_, _, _, _, _, _, h⟩ := foldBin_some h; cases h

variable {T : Tables}

theorem expr_binop {op : BinOp} {a b : RawExpr} {s : Syn .expr} :
    T.expr (.binop op a b) = some s ↔
      ∃ f sa sb, Decode.binop op = some f ∧ T.expr a = some sa ∧ T.expr b = some sb ∧
        s = f sa sb := by
  cases h1 : Decode.binop op <;> cases h2 : T.expr a <;> cases h3 : T.expr b <;>
    simp [Tables.expr, h1, h2, h3, eq_comm]

theorem expr_neg {a : RawExpr} {s : Syn .expr} :
    T.expr (.unop .neg a) = some s ↔ ∃ sa, T.expr a = some sa ∧ s = .unaryPrefix .neg sa := by
  cases h : T.expr a <;> simp [Tables.expr, h, eq_comm]

theorem expr_bnot {a : RawExpr} {s : Syn .expr} :
    T.expr (.unop .bnot a) = some s ↔ ∃ sa, T.expr a = some sa ∧ s = .unaryPrefix .bitNot sa := by
  cases h : T.expr a <;> simp [Tables.expr, h, eq_comm]

theorem expr_num {n : Nat} : T.expr (.num n) = some (Decode.num n) := by simp only [Tables.expr]

theorem expr_name {x : String} : T.expr (.name x) = some (.ident x) := by simp only [Tables.expr]

/-- **Folding wins**: a model expression that folds is spelled, and its
spelling meets `tryConst`'s premises with that constant. -/
theorem fold_spec {e : RawExpr} {q : Q} (h : fold e = some q) :
    ∃ s, T.expr e = some s ∧ s.const = some q ∧ s.isAddressLit = false ∧ s.hexLen? = none := by
  induction e using fold.induct generalizing q with
  | case1 n => cases h; exact ⟨_, expr_num, rfl, rfl, rfl⟩
  | case2 op a b iha ihb =>
    rw [fold] at h
    obtain ⟨k, x, y, hk, _, hx, hy⟩ := foldBin_some h
    obtain ⟨sa, hsa, hca, _⟩ := iha hx
    obtain ⟨sb, hsb, hcb, _⟩ := ihb hy
    obtain ⟨f, hf, hspec⟩ := binop_family hk
    obtain ⟨_, _, hc, hal, hhx⟩ := hspec sa sb
    exact ⟨_, expr_binop.mpr ⟨f, sa, sb, hf, hsa, hsb, rfl⟩,
      by rw [hc, hca, hcb, ← hx, ← hy]; exact h, hal, hhx⟩
  | case3 a ih =>
    rw [fold] at h
    cases hx : fold a with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h; cases h
      obtain ⟨sa, hsa, hca, _⟩ := ih hx
      exact ⟨_, expr_neg.mpr ⟨sa, hsa, rfl⟩, by show sa.const.map Q.neg = _; rw [hca]; rfl, rfl, rfl⟩
  | case4 a ih =>
    rw [fold] at h
    cases hx : fold a with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      obtain ⟨sa, hsa, hca, _⟩ := ih hx
      refine ⟨_, expr_bnot.mpr ⟨sa, hsa, rfl⟩, ?_, rfl, rfl⟩
      show (sa.const.bind fun q => q.int?.bind fun k => _) = _
      rw [hca]; exact h
  | case5 e h1 h2 h3 h4 =>
    unfold fold at h
    split at h
    all_goals first | (cases h; done) | exact (h1 _ rfl).elim | exact (h2 _ _ _ rfl).elim
                    | exact (h3 _ rfl).elim | exact (h4 _ rfl).elim

end Solidity.Correctness.Lowering.Total.ArithmeticInference
