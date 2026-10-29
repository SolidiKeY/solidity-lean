import Solidity.Source.Resolved

/-!
# Uniqueness of typing derivations (Q1)

With solc's literal typing (a number literal is always a constant;
a hexadecimal literal's type `STy.hexConst` records its compatible bytes
length, `Typed.litBytes`), an expression's derivations agree: any two
derivations of one expression have the same type and elaborate to the same
resolved term (`Typed.unique`).  So a unit's meaning does not depend on which
derivation an elaboration carries.

The key lemma is `Typed.constShape`: a constant expression (`Syn.const`)
has only its constant type, or, for a bare or parenthesized hexadecimal
literal, its `hexConst` type, and elaborates to that constant.  Operators,
shifts and comparisons on two constants are folded, never typed as
operations (`Syn.const_binOp`, `STy.common?_const`).
-/

namespace Solidity.Source

/-- The hexadecimal literal an expression is, through parentheses. -/
def Syn.hexLit? : {c : Cat} → Syn c → Option NumLit
  | _, .lit (.num n) => Option.some n
  | _, .tuple (.some e) .nil => e.hexLit?
  | _, _ => Option.none

/-- A constant's type: its rational, or a hexadecimal literal's. -/
def STy.isConstTy : STy → Bool
  | .rational _ | .hexConst _ _ => true
  | _ => false

/-- **Two constant types never meet**: no implicit conversion between them. -/
theorem STy.common?_const {B : DeclName → DeclName → Bool} {a b : STy} (ha : a.isConstTy = true)
    (hb : b.isConstTy = true) : STy.common? B a b = Option.none := by
  cases a <;> cases b <;> first | rfl | (simp only [STy.isConstTy, Bool.false_eq_true] at ha hb)

/-- A bind that succeeds had a value. -/
theorem Option.isSome_of_bind_eq_some {α β : Type} {o : Option α} {f : α → Option β} {b : β}
    (h : o.bind f = Option.some b) : o.isSome = true := by
  cases o
  · cases h
  · rfl

theorem Syn.const_add (a b : Syn .expr) :
    (Syn.addSub .add a b).const = a.const.bind fun x => b.const.bind fun y => (x.add y).bounded := rfl
theorem Syn.const_sub (a b : Syn .expr) :
    (Syn.addSub .sub a b).const = a.const.bind fun x => b.const.bind fun y => (x.sub y).bounded := rfl
theorem Syn.const_mul (a b : Syn .expr) :
    (Syn.mulDivMod .mul a b).const = a.const.bind fun x => b.const.bind fun y => (x.mul y).bounded := rfl
theorem Syn.const_div (a b : Syn .expr) :
    (Syn.mulDivMod .div a b).const = a.const.bind fun x => b.const.bind fun y => (x.div y).bind Q.bounded := rfl
theorem Syn.const_mod (a b : Syn .expr) :
    (Syn.mulDivMod .mod a b).const = a.const.bind fun x => b.const.bind fun y => (x.mod y).bind Q.bounded := rfl
theorem Syn.const_exp (a b : Syn .expr) :
    (Syn.exp a b).const = b.const.bind fun y => y.int?.bind fun k => a.const.bind fun x => x.pow k := rfl
theorem Syn.const_shl (a b : Syn .expr) :
    (Syn.shift .shl a b).const = a.const.bind fun x => x.int?.bind fun x' => b.const.bind fun y =>
      y.int?.bind fun y' => if x' = 0 ∧ 0 ≤ y' then Option.some (Q.ofInt 0)
        else if 0 ≤ y' ∧ Q.bitLen x'.natAbs + y'.toNat ≤ Q.maxBits + 1 then Option.some (Q.ofInt (x' * 2 ^ y'.toNat))
        else Option.none := rfl
theorem Syn.const_sar (a b : Syn .expr) :
    (Syn.shift .sar a b).const = a.const.bind fun x => x.int?.bind fun x' => b.const.bind fun y =>
      y.int?.bind fun y' => if 0 ≤ y' then Option.some (Q.ofInt (if y'.toNat ≤ maxShift then x'.fdiv (2 ^ y'.toNat)
        else if x' < 0 then -1 else 0)) else Option.none := rfl
theorem Syn.const_shr (a b : Syn .expr) : (Syn.shift .shr a b).const = Option.none := rfl
theorem Syn.const_bitAnd (a b : Syn .expr) :
    (Syn.bitAnd a b).const = a.const.bind fun x => x.int?.bind fun x' => b.const.bind fun y =>
      y.int?.bind fun y' => Option.some (Q.ofInt (Int.bitAnd x' y')) := rfl
theorem Syn.const_bitOr (a b : Syn .expr) :
    (Syn.bitOr a b).const = a.const.bind fun x => x.int?.bind fun x' => b.const.bind fun y =>
      y.int?.bind fun y' => Option.some (Q.ofInt (Int.bitOr x' y')) := rfl
theorem Syn.const_bitXor (a b : Syn .expr) :
    (Syn.bitXor a b).const = a.const.bind fun x => x.int?.bind fun x' => b.const.bind fun y =>
      y.int?.bind fun y' => Option.some (Q.ofInt (Int.bitXor x' y')) := rfl
theorem Syn.const_order (o : OrderOp) (a b : Syn .expr) : (Syn.order o a b).const = Option.none := rfl
theorem Syn.const_equality (o : EqOp) (a b : Syn .expr) : (Syn.equality o a b).const = Option.none := rfl
theorem Syn.const_and (a b : Syn .expr) : (Syn.and a b).const = Option.none := rfl
theorem Syn.const_or (a b : Syn .expr) : (Syn.or a b).const = Option.none := rfl

/-- **A constant operation has constant operands**, and comparisons and
logical operators never fold. -/
theorem Syn.const_binOp {e a b : Syn .expr} {k : BinKind} (hb : e.binOp? = Option.some (k, a, b)) {q : Q}
    (hq : e.const = Option.some q) :
    a.const.isSome = true ∧ b.const.isSome = true ∧ k ≠ .order ∧ k ≠ .eq ∧ k ≠ .logic := by
  cases e
  all_goals first
    | (cases hb; done)
    | skip
  all_goals cases hb
  all_goals (try (rename_i op; cases op))
  all_goals first
    | rw [Syn.const_add] at hq | rw [Syn.const_sub] at hq | rw [Syn.const_mul] at hq
    | rw [Syn.const_div] at hq | rw [Syn.const_mod] at hq | rw [Syn.const_exp] at hq
    | rw [Syn.const_shl] at hq | rw [Syn.const_sar] at hq | rw [Syn.const_shr] at hq
    | rw [Syn.const_bitAnd] at hq | rw [Syn.const_bitOr] at hq | rw [Syn.const_bitXor] at hq
    | rw [Syn.const_order] at hq | rw [Syn.const_equality] at hq | rw [Syn.const_and] at hq
    | rw [Syn.const_or] at hq
  all_goals (cases ha : Syn.const a <;> cases hb' : Syn.const b <;>
    simp only [ha, hb', Option.bind_none, Option.bind_some, Option.bind_fun_none, reduceCtorEq,
      Option.isSome_some, ne_eq, not_false_eq_true, and_self] at hq ⊢)

/-- The operands of a binary operation are smaller. -/
theorem Syn.binOp?_sizeOf {e a b : Syn .expr} {k : BinKind} (hb : e.binOp? = Option.some (k, a, b)) :
    sizeOf a < sizeOf e ∧ sizeOf b < sizeOf e := by
  cases e
  all_goals first
    | (cases hb; done)
    | skip
  all_goals (cases hb; simp only [Syn.mulDivMod.sizeOf_spec, Syn.addSub.sizeOf_spec, Syn.shift.sizeOf_spec,
    Syn.exp.sizeOf_spec, Syn.bitAnd.sizeOf_spec, Syn.bitOr.sizeOf_spec, Syn.bitXor.sizeOf_spec,
    Syn.order.sizeOf_spec, Syn.equality.sizeOf_spec, Syn.and.sizeOf_spec, Syn.or.sizeOf_spec]; omega)

/-- A hexadecimal literal of bytes length is a constant of its value (a
checksummed address literal is neither). -/
theorem Syn.const_hexLit {n : NumLit} {len : Nat} (h : (Syn.lit (.num n)).hexLen? = Option.some len) :
    (Syn.lit (.num n)).const = Option.some n.value := by
  cases n with
  | dec m f x => rfl
  | hex ds cs =>
    cases cs
    · rfl
    · by_cases h40 : ds.length = 40
      · change (if ds.length % 2 = 0 ∧ 2 ≤ ds.length ∧ ds.length ≤ 64 ∧ ¬ (true = true ∧ ds.length = 40) then
          Option.some (ds.length / 2) else Option.none) = Option.some len at h
        rw [if_neg (fun hc => hc.2.2.2 ⟨rfl, h40⟩)] at h
        cases h
      · show (if ds.length = 40 then Option.none else Option.some _) = _
        rw [if_neg h40]

/-- The shape of a constant expression's derivation: its rational, or a
hexadecimal literal's type; elaborated to that constant. -/
def ConstShape (Γ : Ctx) (e : Syn .expr) (q : Q) (τ : STy) (r : RExpr Γ.env Γ.tys τ) : Prop :=
  (τ = .rational q ∧ e.hexLen? = Option.none ∧ HEq r (RExpr.const (E := Γ.env) (Γ := Γ.tys) q)) ∨
  (∃ nl len, e.hexLit? = Option.some nl ∧ e.hexLen? = Option.some len ∧ nl.value = q ∧
    τ = .hexConst nl.value len ∧ HEq r (RExpr.bytesLit (E := Γ.env) (Γ := Γ.tys) nl len))

theorem ConstShape.isConstTy {Γ : Ctx} {e : Syn .expr} {q : Q} {τ : STy} {r : RExpr Γ.env Γ.tys τ}
    (h : ConstShape Γ e q τ r) : τ.isConstTy = true := by
  rcases h with ⟨rfl, _, _⟩ | ⟨_, _, _, _, _, rfl, _⟩ <;> rfl

/-- **Constant expressions have only their constant types**: no operation,
comparison or conversion types a constant (they fold). -/
theorem Typed.constShape {Γ : Ctx} {e : Syn .expr} {τ : STy} {q : Q} (d : Typed Γ e τ)
    (hq : e.const = Option.some q) : ConstShape Γ e q τ d.toR := by
  cases d
  all_goals first
    | (cases hq; done)
    | skip
  case const hc _ hx =>
    rw [hc] at hq; cases hq
    exact .inl ⟨rfl, hx, HEq.rfl⟩
  case litBytes n len hl =>
    rw [Syn.const_hexLit hl] at hq; cases hq
    exact .inr ⟨n, len, rfl, hl, rfl, rfl, HEq.rfl⟩
  case paren e' d' =>
    have h' := Typed.constShape d' hq
    simp only [Typed.toR]
    exact h'
  case litAddress ds h40 =>
    change (if ds.length = 40 then Option.none else Option.some _) = Option.some q at hq
    rw [if_pos h40] at hq; cases hq
  case tuple e s τ1 τs d1 sl hne =>
    cases sl
    · exact absurd rfl hne
    · cases hq
  case neg e t d' hs =>
    obtain ⟨q', hq', _⟩ := Option.map_eq_some_iff.1 hq
    have := (Typed.constShape d' hq').isConstTy
    cases this
  case negFixed e f d' =>
    obtain ⟨q', hq', _⟩ := Option.map_eq_some_iff.1 hq
    have := (Typed.constShape d' hq').isConstTy
    cases this
  case bitNot e' d' hbits =>
    obtain ⟨q', hq', -⟩ := Option.bind_eq_some_iff.1 hq
    have hc := (Typed.constShape d' hq').isConstTy
    cases τ <;> first | (cases hbits; done) | (cases hc; done)
  case incDec e op hop l hn =>
    rcases hop with rfl | rfl <;> cases hq
  case arith a b τa τb da db hb hz hc hn =>
    have hs := Syn.binOp?_sizeOf hb
    obtain ⟨ha, hb', -⟩ := Syn.const_binOp hb hq
    obtain ⟨qa, hqa⟩ := Option.isSome_iff_exists.1 ha
    obtain ⟨qb, hqb⟩ := Option.isSome_iff_exists.1 hb'
    rw [STy.common?_const (Typed.constShape da hqa).isConstTy (Typed.constShape db hqb).isConstTy] at hc
    cases hc
  case bit a b τa τb da db hb hc hn =>
    have hs := Syn.binOp?_sizeOf hb
    obtain ⟨ha, hb', -⟩ := Syn.const_binOp hb hq
    obtain ⟨qa, hqa⟩ := Option.isSome_iff_exists.1 ha
    obtain ⟨qb, hqb⟩ := Option.isSome_iff_exists.1 hb'
    rw [STy.common?_const (Typed.constShape da hqa).isConstTy (Typed.constShape db hqb).isConstTy] at hc
    cases hc
  case shift a b τa τb da db hm ham hn hb =>
    obtain ⟨ha, hb', -⟩ := Syn.const_binOp hb hq
    rw [ha, hb'] at hn; cases hn
  case exp a b τa τb da db hm ham hn hb =>
    obtain ⟨ha, hb', -⟩ := Syn.const_binOp hb hq
    rw [ha, hb'] at hn; cases hn
  case order a b τa τb τc da db hc ho hb =>
    exact absurd rfl (Syn.const_binOp hb hq).2.2.1
  case eq a b τa τb τc da db hc ho hb =>
    exact absurd rfl (Syn.const_binOp hb hq).2.2.2.1
  case compareConst a b k qa qb hk ha hb' hb =>
    have h := Syn.const_binOp hb hq
    rcases hk with rfl | rfl
    · exact absurd rfl h.2.2.1
    · exact absurd rfl h.2.2.2.1
  case logic a b da db hb =>
    exact absurd rfl (Syn.const_binOp hb hq).2.2.2.2
termination_by sizeOf e
decreasing_by
  all_goals first
    | (subst_vars; simp only [Syn.tuple.sizeOf_spec, Syn.some.sizeOf_spec, Syn.unaryPrefix.sizeOf_spec]; omega)
    | (subst_vars; omega)

end Solidity.Source
