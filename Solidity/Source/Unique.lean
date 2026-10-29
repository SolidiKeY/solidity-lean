import Solidity.Source.Resolved

/-!
# Uniqueness of meaning for constants (Q1)

With solc's literal typing (a number literal is always a constant; a
hexadecimal literal's type `STy.hexConst` records its compatible bytes
length, `Typed.litBytes`; a checksummed address literal folds into no
constant), literals no longer give an expression several types.

`Typed.constShape` proves it for every constant expression (`Syn.const`):
each derivation has its rational type, or, for a bare or parenthesized
hexadecimal literal, its `hexConst` type, and elaborates to that constant.
Operators, shifts and comparisons on two constants fold and are never typed
as operations (`Syn.const_binOp`, `STy.common?_const`).
`zeroLength_illTyped` is the negative control: `0.length`, which had 32
derivations before, has none.

Uniqueness for every expression (`Typed.unique`: any two derivations have one
type and one elaboration) is the remaining obligation of Q1.  This lemma
settles the literal cases; the rest is a per-constructor case analysis
recorded in `docs/feature-work/source-s02.md`, "Uniqueness".
-/

namespace Solidity.Source

/-- The hexadecimal literal an expression is, through parentheses. -/
def Syn.hexLit? : {c : Cat} → Syn c → Option NumLit
  | _, .lit (.num n) => Option.some n
  | _, .tuple (.some e) .nil => e.hexLit?
  | _, _ => Option.none

/-- **Two constant types never meet**: no implicit conversion between them. -/
theorem STy.common?_const {B : DeclName → DeclName → Bool} {a b : STy} (ha : a.isConstTy = true)
    (hb : b.isConstTy = true) : STy.common? B a b = Option.none := by
  simp only [STy.common?, ha, hb, Bool.true_or, Bool.and_self, if_true]

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
    change (if ds.length % 2 = 0 ∧ 2 ≤ ds.length ∧ ds.length ≤ 64 ∧ ¬ (39 ≤ ds.length ∧ ds.length ≤ 41) then
      Option.some (ds.length / 2) else Option.none) = Option.some len at h
    split at h
    · rename_i hc
      show (if 39 ≤ ds.length ∧ ds.length ≤ 41 then Option.none else Option.some _) = _
      rw [if_neg hc.2.2.2]
    · cases h

/-- The shape of a constant expression's derivation: its rational, or a
hexadecimal literal's type; elaborated to that constant. -/
def ConstShape (Γ : Ctx) (e : Syn .expr) (q : Q) (τ : STy) (r : RExpr Γ.env Γ.tys τ) : Prop :=
  (τ = .rational q ∧ e.hexLen? = Option.none ∧ HEq r (RExpr.const (E := Γ.env) (Γ := Γ.tys) q)) ∨
  (∃ nl len, e.hexLit? = Option.some nl ∧ e.hexLen? = Option.some len ∧ nl.value = q ∧
    τ = .hexConst nl.value len ∧ HEq r (RExpr.bytesLit (E := Γ.env) (Γ := Γ.tys) nl len))

theorem ConstShape.isConstTy {Γ : Ctx} {e : Syn .expr} {q : Q} {τ : STy} {r : RExpr Γ.env Γ.tys τ}
    (h : ConstShape Γ e q τ r) : τ.isConstTy = true := by
  rcases h with ⟨rfl, _, _⟩ | ⟨_, _, _, _, _, rfl, _⟩ <;> rfl

/-- **Constant expressions have only their constant types**: every
derivation of an expression that folds (`Syn.const`) is its constant (an
arithmetic, bitwise, shift or power operation on constants never types as
an operation), and elaborates to it.  This is uniqueness of meaning, not of
derivations: `(1)` is both `const` and `paren (const …)`, which elaborate
alike. -/
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
    change (if 39 ≤ ds.length ∧ ds.length ≤ 41 then Option.none else Option.some _) = Option.some q at hq
    rw [if_pos ⟨by omega, by omega⟩] at hq; cases hq
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

/-- **Two derivations of a constant expression have one type and one
elaboration.** -/
theorem Typed.const_unique {Γ : Ctx} {e : Syn .expr} {τ τ' : STy} {q : Q} (d : Typed Γ e τ)
    (d' : Typed Γ e τ') (hq : e.const = Option.some q) : τ = τ' ∧ HEq d.toR d'.toR := by
  rcases Typed.constShape d hq with ⟨rfl, hx, h1⟩ | ⟨nl, len, hl, hx, -, rfl, h1⟩ <;>
    rcases Typed.constShape d' hq with ⟨rfl, hx', h2⟩ | ⟨nl', len', hl', hx', -, rfl, h2⟩
  · exact ⟨rfl, h1.trans h2.symm⟩
  · rw [hx] at hx'; cases hx'
  · rw [hx] at hx'; cases hx'
  · rw [hl] at hl'; cases hl'; rw [hx] at hx'; cases hx'; exact ⟨rfl, h1.trans h2.symm⟩

/-! ## Uniqueness of meaning for every expression

By strong induction on the size of the syntax (`Uniq`), one lemma per
syntactic shape, each over the pairs of rules that type that shape. -/

/-- Uniqueness of meaning at one expression. -/
def UniqE (Γ : Ctx) (e : Syn .expr) : Prop :=
  ∀ {τ τ' : STy} (d : Typed Γ e τ) (d' : Typed Γ e τ'), τ = τ' ∧ HEq d.toR d'.toR

/-- … of its lvalue derivations. -/
def UniqL (Γ : Ctx) (e : Syn .expr) : Prop :=
  ∀ {τ τ' : STy} (l : LVal Γ e τ) (l' : LVal Γ e τ'), τ = τ' ∧ HEq l.toR l'.toR

/-- … of argument lists. -/
def UniqA (Γ : Ctx) (es : Syn (.list .expr)) : Prop :=
  ∀ {τs τs' : List STy} (d : TypedArgs Γ es τs) (d' : TypedArgs Γ es τs'), τs = τs' ∧ HEq d.toR d'.toR

/-- … of tuple slots (at mobile types and as arguments). -/
def UniqS (Γ : Ctx) (s : Syn (.list (.opt .expr))) : Prop :=
  ∀ {τs τs' : List STy} (d : TypedSlots Γ s τs) (d' : TypedSlots Γ s τs'),
    τs = τs' ∧ HEq d.toR d'.toR ∧ HEq (TypedArgs.ofSlots d) (TypedArgs.ofSlots d')

/-- The induction hypothesis: uniqueness below size `n`. -/
structure Uniq (Γ : Ctx) (n : Nat) : Prop where
  e : ∀ e : Syn .expr, sizeOf e < n → UniqE Γ e
  l : ∀ e : Syn .expr, sizeOf e < n → UniqL Γ e
  a : ∀ es : Syn (.list .expr), sizeOf es < n → UniqA Γ es
  s : ∀ s : Syn (.list (.opt .expr)), sizeOf s < n → UniqS Γ s

theorem no_binOp {e a b : Syn .expr} {k : BinKind} (hbo : e.binOp? = Option.none)
    (h : e.binOp? = Option.some (k, a, b)) : False := by
  rw [hbo] at h; cases h

theorem no_const {e : Syn .expr} {q : Q} (hce : e.const = Option.none) (h : e.const = Option.some q) :
    False := by
  rw [hce] at h; cases h

theorem uniqE_cond {Γ : Ctx} {c a b : Syn .expr} (ih : Uniq Γ (sizeOf (Syn.cond c a b))) :
    UniqE Γ (.cond c a b) := by
  intro τ τ' d d'
  have hce : (Syn.cond c a b).const = Option.none := rfl
  have hbo : (Syn.cond c a b).binOp? = Option.none := rfl
  cases d
  all_goals first
    | exact (no_const hce ‹_›).elim
    | (exfalso; apply no_binOp hbo; assumption)
    | skip
  cases d'
  all_goals first
    | exact (no_const hce ‹_›).elim
    | (exfalso; apply no_binOp hbo; assumption)
    | skip
  rename_i τa τb dc da db hc τa' τb' dc' da' db' hc'
  have hs : sizeOf c < sizeOf (Syn.cond c a b) ∧ sizeOf a < sizeOf (Syn.cond c a b) ∧
      sizeOf b < sizeOf (Syn.cond c a b) := by
    simp only [Syn.cond.sizeOf_spec]; omega
  obtain ⟨-, e1⟩ := ih.e c hs.1 dc dc'
  obtain ⟨rfl, e2⟩ := ih.e a hs.2.1 da da'
  obtain ⟨rfl, e3⟩ := ih.e b hs.2.2 db db'
  rw [hc] at hc'; cases hc'
  refine ⟨rfl, ?_⟩
  simp only [Typed.toR]
  rw [eq_of_heq e1, eq_of_heq e2, eq_of_heq e3]

theorem bin_same {e a b a' b' : Syn .expr} {k k' : BinKind} (hb : e.binOp? = Option.some (k, a, b))
    (h : e.binOp? = Option.some (k', a', b')) : k = k' ∧ a = a' ∧ b = b' := by
  rw [hb] at h; cases h; exact ⟨rfl, rfl, rfl⟩

/-- Two constant operands make no typed operation (they fold). -/
theorem bin_const_false {Γ : Ctx} {a b : Syn .expr} {qa qb : Q} {τa τb τ : STy} (ha : a.const = Option.some qa)
    (hb : b.const = Option.some qb) (da : Typed Γ a τa) (db : Typed Γ b τb)
    (hc : STy.common? Γ.isBase τa τb = Option.some τ) : False := by
  rw [STy.common?_const (Typed.constShape da ha).isConstTy (Typed.constShape db hb).isConstTy] at hc
  cases hc

/-- **Binary operations.** -/
theorem uniqE_bin {Γ : Ctx} {e a b : Syn .expr} {k : BinKind} (hb : e.binOp? = Option.some (k, a, b))
    (hce : e.const = Option.none) (ih : Uniq Γ (sizeOf e)) : UniqE Γ e := by
  intro τ τ' d d'
  have hs := Syn.binOp?_sizeOf hb
  cases d with
  | arith hb1 da1 db1 hc1 hn1 hz1 =>
    obtain ⟨rfl, rfl, rfl⟩ := bin_same hb hb1
    cases d' with
    | arith hb2 da2 db2 hc2 hn2 hz2 =>
        obtain ⟨-, rfl, rfl⟩ := bin_same hb hb2
        obtain ⟨rfl, e1⟩ := ih.e _ hs.1 da1 da2
        obtain ⟨rfl, e2⟩ := ih.e _ hs.2 db1 db2
        rw [hc1] at hc2; cases hc2
        refine ⟨rfl, ?_⟩
        simp only [Typed.toR]
        rw [eq_of_heq e1, eq_of_heq e2]
    | bit hb2 da2 db2 hc2 hn2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | shift hb2 da2 db2 hm2 ham2 hk2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | exp hb2 da2 db2 hm2 ham2 hk2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | order hb2 da2 db2 hc2 ho2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | eq hb2 da2 db2 hc2 ho2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | compareConst hb2 hk2 ha2 hq2 =>
        obtain ⟨rfl, -, -⟩ := bin_same hb hb2
        rcases hk2 with h | h <;> cases h
    | logic hb2 da2 db2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (cases hb; done)
  | bit hb1 da1 db1 hc1 hn1 =>
    obtain ⟨rfl, rfl, rfl⟩ := bin_same hb hb1
    cases d' with
    | arith hb2 da2 db2 hc2 hn2 hz2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | bit hb2 da2 db2 hc2 hn2 =>
        obtain ⟨-, rfl, rfl⟩ := bin_same hb hb2
        obtain ⟨rfl, e1⟩ := ih.e _ hs.1 da1 da2
        obtain ⟨rfl, e2⟩ := ih.e _ hs.2 db1 db2
        rw [hc1] at hc2; cases hc2
        refine ⟨rfl, ?_⟩
        simp only [Typed.toR]
        rw [eq_of_heq e1, eq_of_heq e2]
    | shift hb2 da2 db2 hm2 ham2 hk2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | exp hb2 da2 db2 hm2 ham2 hk2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | order hb2 da2 db2 hc2 ho2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | eq hb2 da2 db2 hc2 ho2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | compareConst hb2 hk2 ha2 hq2 =>
        obtain ⟨rfl, -, -⟩ := bin_same hb hb2
        rcases hk2 with h | h <;> cases h
    | logic hb2 da2 db2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (cases hb; done)
  | shift hb1 da1 db1 hm1 ham1 hk1 =>
    obtain ⟨rfl, rfl, rfl⟩ := bin_same hb hb1
    cases d' with
    | arith hb2 da2 db2 hc2 hn2 hz2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | bit hb2 da2 db2 hc2 hn2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | shift hb2 da2 db2 hm2 ham2 hk2 =>
        obtain ⟨-, rfl, rfl⟩ := bin_same hb hb2
        obtain ⟨rfl, e1⟩ := ih.e _ hs.1 da1 da2
        obtain ⟨rfl, e2⟩ := ih.e _ hs.2 db1 db2
        refine ⟨rfl, ?_⟩
        simp only [Typed.toR]
        rw [eq_of_heq e1, eq_of_heq e2]
    | exp hb2 da2 db2 hm2 ham2 hk2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | order hb2 da2 db2 hc2 ho2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | eq hb2 da2 db2 hc2 ho2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | compareConst hb2 hk2 ha2 hq2 =>
        obtain ⟨rfl, -, -⟩ := bin_same hb hb2
        rcases hk2 with h | h <;> cases h
    | logic hb2 da2 db2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (cases hb; done)
  | exp hb1 da1 db1 hm1 ham1 hk1 =>
    obtain ⟨rfl, rfl, rfl⟩ := bin_same hb hb1
    cases d' with
    | arith hb2 da2 db2 hc2 hn2 hz2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | bit hb2 da2 db2 hc2 hn2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | shift hb2 da2 db2 hm2 ham2 hk2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | exp hb2 da2 db2 hm2 ham2 hk2 =>
        obtain ⟨-, rfl, rfl⟩ := bin_same hb hb2
        obtain ⟨rfl, e1⟩ := ih.e _ hs.1 da1 da2
        obtain ⟨rfl, e2⟩ := ih.e _ hs.2 db1 db2
        refine ⟨rfl, ?_⟩
        simp only [Typed.toR]
        rw [eq_of_heq e1, eq_of_heq e2]
    | order hb2 da2 db2 hc2 ho2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | eq hb2 da2 db2 hc2 ho2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | compareConst hb2 hk2 ha2 hq2 =>
        obtain ⟨rfl, -, -⟩ := bin_same hb hb2
        rcases hk2 with h | h <;> cases h
    | logic hb2 da2 db2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (cases hb; done)
  | order hb1 da1 db1 hc1 ho1 =>
    obtain ⟨rfl, rfl, rfl⟩ := bin_same hb hb1
    cases d' with
    | arith hb2 da2 db2 hc2 hn2 hz2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | bit hb2 da2 db2 hc2 hn2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | shift hb2 da2 db2 hm2 ham2 hk2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | exp hb2 da2 db2 hm2 ham2 hk2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | order hb2 da2 db2 hc2 ho2 =>
        obtain ⟨-, rfl, rfl⟩ := bin_same hb hb2
        obtain ⟨rfl, e1⟩ := ih.e _ hs.1 da1 da2
        obtain ⟨rfl, e2⟩ := ih.e _ hs.2 db1 db2
        rw [hc1] at hc2; cases hc2
        refine ⟨rfl, ?_⟩
        simp only [Typed.toR]
        rw [eq_of_heq e1, eq_of_heq e2]
    | eq hb2 da2 db2 hc2 ho2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | compareConst hb2 hk2 ha2 hq2 =>
        obtain ⟨-, rfl, rfl⟩ := bin_same hb hb2
        exact (bin_const_false ha2 hq2 da1 db1 hc1).elim
    | logic hb2 da2 db2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (cases hb; done)
  | eq hb1 da1 db1 hc1 ho1 =>
    obtain ⟨rfl, rfl, rfl⟩ := bin_same hb hb1
    cases d' with
    | arith hb2 da2 db2 hc2 hn2 hz2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | bit hb2 da2 db2 hc2 hn2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | shift hb2 da2 db2 hm2 ham2 hk2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | exp hb2 da2 db2 hm2 ham2 hk2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | order hb2 da2 db2 hc2 ho2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | eq hb2 da2 db2 hc2 ho2 =>
        obtain ⟨-, rfl, rfl⟩ := bin_same hb hb2
        obtain ⟨rfl, e1⟩ := ih.e _ hs.1 da1 da2
        obtain ⟨rfl, e2⟩ := ih.e _ hs.2 db1 db2
        rw [hc1] at hc2; cases hc2
        refine ⟨rfl, ?_⟩
        simp only [Typed.toR]
        rw [eq_of_heq e1, eq_of_heq e2]
    | compareConst hb2 hk2 ha2 hq2 =>
        obtain ⟨-, rfl, rfl⟩ := bin_same hb hb2
        exact (bin_const_false ha2 hq2 da1 db1 hc1).elim
    | logic hb2 da2 db2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (cases hb; done)
  | compareConst hb1 hk1 ha1 hq1 =>
    obtain ⟨rfl, rfl, rfl⟩ := bin_same hb hb1
    cases d' with
    | arith hb2 da2 db2 hc2 hn2 hz2 =>
        rcases hk1 with rfl | rfl <;> exact absurd (bin_same hb hb2).1 (by decide)
    | bit hb2 da2 db2 hc2 hn2 =>
        rcases hk1 with rfl | rfl <;> exact absurd (bin_same hb hb2).1 (by decide)
    | shift hb2 da2 db2 hm2 ham2 hk2 =>
        rcases hk1 with rfl | rfl <;> exact absurd (bin_same hb hb2).1 (by decide)
    | exp hb2 da2 db2 hm2 ham2 hk2 =>
        rcases hk1 with rfl | rfl <;> exact absurd (bin_same hb hb2).1 (by decide)
    | order hb2 da2 db2 hc2 ho2 =>
        obtain ⟨-, rfl, rfl⟩ := bin_same hb hb2
        exact (bin_const_false ha1 hq1 da2 db2 hc2).elim
    | eq hb2 da2 db2 hc2 ho2 =>
        obtain ⟨-, rfl, rfl⟩ := bin_same hb hb2
        exact (bin_const_false ha1 hq1 da2 db2 hc2).elim
    | compareConst hb2 hk2 ha2 hq2 =>
        obtain ⟨-, rfl, rfl⟩ := bin_same hb hb2
        rw [ha1] at ha2; cases ha2
        rw [hq1] at hq2; cases hq2
        exact ⟨rfl, HEq.rfl⟩
    | logic hb2 da2 db2 =>
        rcases hk1 with rfl | rfl <;> exact absurd (bin_same hb hb2).1 (by decide)
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (cases hb; done)
  | logic hb1 da1 db1 =>
    obtain ⟨rfl, rfl, rfl⟩ := bin_same hb hb1
    cases d' with
    | arith hb2 da2 db2 hc2 hn2 hz2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | bit hb2 da2 db2 hc2 hn2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | shift hb2 da2 db2 hm2 ham2 hk2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | exp hb2 da2 db2 hm2 ham2 hk2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | order hb2 da2 db2 hc2 ho2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | eq hb2 da2 db2 hc2 ho2 =>
        exact absurd (bin_same hb hb2).1 (by decide)
    | compareConst hb2 hk2 ha2 hq2 =>
        obtain ⟨rfl, -, -⟩ := bin_same hb hb2
        rcases hk2 with h | h <;> cases h
    | logic hb2 da2 db2 =>
        obtain ⟨-, rfl, rfl⟩ := bin_same hb hb2
        obtain ⟨-, e1⟩ := ih.e _ hs.1 da1 da2
        obtain ⟨-, e2⟩ := ih.e _ hs.2 db1 db2
        refine ⟨rfl, ?_⟩
        simp only [Typed.toR]
        rw [eq_of_heq e1, eq_of_heq e2]
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (cases hb; done)
  | _ => first
    | exact (no_const hce ‹_›).elim
    | (cases hb; done)

theorem Uniq.mono {Γ : Ctx} {n m : Nat} (h : Uniq Γ n) (hm : m ≤ n) : Uniq Γ m :=
  ⟨fun e he => h.e e (by omega), fun e he => h.l e (by omega), fun es he => h.a es (by omega),
    fun s he => h.s s (by omega)⟩

/-- A name that denotes a builtin types only as `this`. -/
theorem Typed.ident_builtin {Γ : Ctx} {g : String} {b : Builtin} {τ : STy}
    (hr : Γ.resolve g = Option.some (.builtin b)) (d : Typed Γ (.ident g) τ) : b = .this := by
  have hce : (Syn.ident g).const = Option.none := rfl
  have hbo : (Syn.ident g).binOp? = Option.none := rfl
  cases d with
  | loc h _ => rw [hr] at h; cases h
  | state h _ => rw [hr] at h; cases h
  | this h _ => rw [hr] at h; cases h; rfl
  | _ => first
    | exact (no_const hce ‹_›).elim
    | (exfalso; apply no_binOp hbo; assumption)

/-- **Names.** -/
theorem uniqE_ident {Γ : Ctx} {x : String} (ih : Uniq Γ (sizeOf (Syn.ident x))) : UniqE Γ (.ident x) := by
  intro τ τ' d d'
  have hce : (Syn.ident x).const = Option.none := rfl
  have hbo : (Syn.ident x).binOp? = Option.none := rfl
  cases d with
  | loc hr ht =>
    cases d' with
    | loc hr' ht' => rw [hr] at hr'; cases hr'; rw [ht] at ht'; cases ht'; exact ⟨rfl, HEq.rfl⟩
    | state hr' _ => rw [hr] at hr'; cases hr'
    | this hr' _ => rw [hr] at hr'; cases hr'
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | state hr hv =>
    cases d' with
    | loc hr' _ => rw [hr] at hr'; cases hr'
    | state hr' hv' => rw [hr] at hr'; cases hr'; rw [hv] at hv'; cases hv'; exact ⟨rfl, HEq.rfl⟩
    | this hr' _ => rw [hr] at hr'; cases hr'
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | this hr hs =>
    cases d' with
    | loc hr' _ => rw [hr] at hr'; cases hr'
    | state hr' _ => rw [hr] at hr'; cases hr'
    | this hr' hs' => rw [hs] at hs'; cases hs'; exact ⟨rfl, HEq.rfl⟩
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | _ => first
    | exact (no_const hce ‹_›).elim
    | (exfalso; apply no_binOp hbo; assumption)

/-- A hexadecimal literal of 39 to 41 digits has no bytes length. -/
theorem Syn.hexLen?_addressLike {ds : List (Fin 16)} {cs : Bool} (h : ds.length = 40) :
    (Syn.lit (.num (.hex ds cs))).hexLen? = Option.none := by
  change (if ds.length % 2 = 0 ∧ 2 ≤ ds.length ∧ ds.length ≤ 64 ∧ ¬ (39 ≤ ds.length ∧ ds.length ≤ 41) then
    Option.some (ds.length / 2) else Option.none) = Option.none
  rw [if_neg (fun hc => hc.2.2.2 ⟨by omega, by omega⟩)]

/-- **Literals** (other than constants, which `Typed.const_unique` covers). -/
theorem uniqE_lit {Γ : Ctx} {l : Lit} (hce : (Syn.lit l).const = Option.none) : UniqE Γ (.lit l) := by
  intro τ τ' d d'
  have hbo : (Syn.lit l).binOp? = Option.none := rfl
  cases d with
  | litBytes hl =>
    cases d' with
    | litBytes hl' => rw [hl] at hl'; cases hl'; exact ⟨rfl, HEq.rfl⟩
    | litAddress h40 => rw [Syn.hexLen?_addressLike h40] at hl; cases hl
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | litAddress h40 =>
    cases d' with
    | litBytes hl' => rw [Syn.hexLen?_addressLike h40] at hl'; cases hl'
    | litAddress _ => exact ⟨rfl, HEq.rfl⟩
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | bool b => cases d' with
    | bool _ => exact ⟨rfl, HEq.rfl⟩
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | str bs => cases d' with
    | str _ => exact ⟨rfl, HEq.rfl⟩
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | hexStr bs => cases d' with
    | hexStr _ => exact ⟨rfl, HEq.rfl⟩
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | unicodeStr bs => cases d' with
    | unicodeStr _ => exact ⟨rfl, HEq.rfl⟩
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | _ => first
    | exact (no_const hce ‹_›).elim
    | (exfalso; apply no_binOp hbo; assumption)

/-- **`payable(x)`.** -/
theorem uniqE_payable {Γ : Ctx} {args : Syn .callArgs} (ih : Uniq Γ (sizeOf (Syn.payableConv args))) :
    UniqE Γ (.payableConv args) := by
  intro τ τ' d d'
  have hce : (Syn.payableConv args).const = Option.none := rfl
  have hbo : (Syn.payableConv args).binOp? = Option.none := rfl
  cases d with
  | @payable x σ dx h =>
    have hs : sizeOf x < sizeOf (Syn.payableConv (.positional (.cons x .nil))) := by
      simp only [Syn.payableConv.sizeOf_spec, Syn.positional.sizeOf_spec, Syn.cons.sizeOf_spec]; omega
    cases d' with
    | payable dx' h' =>
      obtain ⟨h1, e1⟩ := ih.e x hs dx dx'
      cases h1
      refine ⟨rfl, ?_⟩
      simp only [Typed.toR]
      rw [eq_of_heq e1]
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | _ => first
    | exact (no_const hce ‹_›).elim
    | (exfalso; apply no_binOp hbo; assumption)

/-- **Parentheses and tuples.** -/
theorem uniqE_tuple {Γ : Ctx} {o : Syn (.opt .expr)} {sl : Syn (.list (.opt .expr))}
    (hce : (Syn.tuple o sl).const = Option.none) (ih : Uniq Γ (sizeOf (Syn.tuple o sl))) :
    UniqE Γ (.tuple o sl) := by
  intro τ τ' d d'
  have hbo : (Syn.tuple o sl).binOp? = Option.none := rfl
  cases d with
  | @paren x σ d1 =>
    have hs : sizeOf x < sizeOf (Syn.tuple (.some x) .nil) := by
      simp only [Syn.tuple.sizeOf_spec, Syn.some.sizeOf_spec]; omega
    cases d' with
    | paren d2 =>
      obtain ⟨h1, e1⟩ := ih.e x hs d1 d2
      cases h1
      exact ⟨rfl, by simp only [Typed.toR]; exact e1⟩
    | tuple _ ds hne => cases ds; exact absurd rfl hne
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | @tuple x sl σ σs d1 ds hne =>
    have hs : sizeOf x < sizeOf (Syn.tuple (.some x) sl) ∧ sizeOf sl < sizeOf (Syn.tuple (.some x) sl) := by
      simp only [Syn.tuple.sizeOf_spec, Syn.some.sizeOf_spec]; omega
    cases d' with
    | paren _ => cases ds; exact absurd rfl hne
    | tuple d2 ds' _ =>
      obtain ⟨h1, e1⟩ := ih.e x hs.1 d1 d2
      cases h1
      obtain ⟨h2, e2, -⟩ := ih.s sl hs.2 ds ds'
      cases h2
      refine ⟨rfl, ?_⟩
      simp only [Typed.toR]
      rw [eq_of_heq e1, eq_of_heq e2]
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | _ => first
    | exact (no_const hce ‹_›).elim
    | (exfalso; apply no_binOp hbo; assumption)

/-- **Prefix operators.** -/
theorem uniqE_prefix {Γ : Ctx} {op : PrefixOp} {x : Syn .expr}
    (hce : (Syn.unaryPrefix op x).const = Option.none) (ih : Uniq Γ (sizeOf (Syn.unaryPrefix op x))) :
    UniqE Γ (.unaryPrefix op x) := by
  intro τ τ' d d'
  have hbo : (Syn.unaryPrefix op x).binOp? = Option.none := rfl
  have hs : sizeOf x < sizeOf (Syn.unaryPrefix op x) := by
    simp only [Syn.unaryPrefix.sizeOf_spec]; omega
  cases d with
  | neg d1 _ =>
    cases d' with
    | neg d2 _ =>
      obtain ⟨h1, e1⟩ := ih.e x hs d1 d2
      cases h1
      exact ⟨rfl, by simp only [Typed.toR]; rw [eq_of_heq e1]⟩
    | negFixed d2 => cases (ih.e x hs d1 d2).1
    | incDec hop _ _ => rcases hop with h | h <;> cases h
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | negFixed d1 =>
    cases d' with
    | neg d2 _ => cases (ih.e x hs d1 d2).1
    | negFixed d2 =>
      obtain ⟨h1, e1⟩ := ih.e x hs d1 d2
      cases h1
      exact ⟨rfl, by simp only [Typed.toR]; rw [eq_of_heq e1]⟩
    | incDec hop _ _ => rcases hop with h | h <;> cases h
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | not d1 =>
    cases d' with
    | not d2 =>
      obtain ⟨-, e1⟩ := ih.e x hs d1 d2
      exact ⟨rfl, by simp only [Typed.toR]; rw [eq_of_heq e1]⟩
    | incDec hop _ _ => rcases hop with h | h <;> cases h
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | bitNot d1 _ =>
    cases d' with
    | bitNot d2 _ =>
      obtain ⟨h1, e1⟩ := ih.e x hs d1 d2
      cases h1
      exact ⟨rfl, by simp only [Typed.toR]; rw [eq_of_heq e1]⟩
    | incDec hop _ _ => rcases hop with h | h <;> cases h
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | incDec hop l1 _ =>
    cases d' with
    | incDec _ l2 _ =>
      obtain ⟨h1, e1⟩ := ih.l x hs l1 l2
      cases h1
      exact ⟨rfl, by simp only [Typed.toR]; rw [eq_of_heq e1]⟩
    | delete _ _ => rcases hop with h | h <;> cases h
    | neg _ _ => rcases hop with h | h <;> cases h
    | negFixed _ => rcases hop with h | h <;> cases h
    | not _ => rcases hop with h | h <;> cases h
    | bitNot _ _ => rcases hop with h | h <;> cases h
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | delete l1 _ =>
    cases d' with
    | delete l2 _ =>
      obtain ⟨h1, e1⟩ := ih.l x hs l1 l2
      cases h1
      exact ⟨rfl, by simp only [Typed.toR]; rw [eq_of_heq e1]⟩
    | incDec hop _ _ => rcases hop with h | h <;> cases h
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | _ => first
    | exact (no_const hce ‹_›).elim
    | (exfalso; apply no_binOp hbo; assumption)

/-- **Postfix `++`/`--`.** -/
theorem uniqE_suffix {Γ : Ctx} {op : SuffixOp} {x : Syn .expr} (ih : Uniq Γ (sizeOf (Syn.unarySuffix op x))) :
    UniqE Γ (.unarySuffix op x) := by
  intro τ τ' d d'
  have hce : (Syn.unarySuffix op x).const = Option.none := rfl
  have hbo : (Syn.unarySuffix op x).binOp? = Option.none := rfl
  have hs : sizeOf x < sizeOf (Syn.unarySuffix op x) := by
    simp only [Syn.unarySuffix.sizeOf_spec]; omega
  cases d with
  | incDecSuffix l1 _ =>
    cases d' with
    | incDecSuffix l2 _ =>
      obtain ⟨h1, e1⟩ := ih.l x hs l1 l2
      cases h1
      exact ⟨rfl, by simp only [Typed.toR]; rw [eq_of_heq e1]⟩
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | _ => first
    | exact (no_const hce ‹_›).elim
    | (exfalso; apply no_binOp hbo; assumption)

/-! ### Controls of the conversion rules (solc's `RationalNumberType`) -/

/-- `bytes2 x = 0x1234;` converts. -/
theorem hex_to_bytes2 (B : DeclName → DeclName → Bool) :
    STy.implicit B (.hexConst (Q.ofInt 0x1234) 2) (.fixedBytes 2 (by decide)) = true := rfl
/-- `bytes4 x = 0x1234;` does not (solc requires the exact size). -/
theorem hex_to_bytes4_refused (B : DeclName → DeclName → Bool) :
    STy.implicit B (.hexConst (Q.ofInt 0x1234) 2) (.fixedBytes 4 (by decide)) = false := rfl
/-- `uint16 x = 0x1234;` converts by value. -/
theorem hex_to_uint16 (B : DeclName → DeclName → Bool) :
    STy.implicit B (.hexConst (Q.ofInt 0x1234) 2) (.int ⟨false, 16, by decide⟩) = true := rfl
/-- `bytes4 x = 0;` converts (zero to every `bytesN`); `bytes4 x = 1;` does not. -/
theorem zero_to_bytes4 (B : DeclName → DeclName → Bool) :
    STy.implicit B (.rational (Q.ofInt 0)) (.fixedBytes 4 (by decide)) = true ∧
    STy.implicit B (.rational (Q.ofInt 1)) (.fixedBytes 4 (by decide)) = false := ⟨rfl, rfl⟩

/-- **`0.length` is ill typed** (solc refuses it): `0` is a constant,
never a `bytesN`, and a constant has no `length`.  Under S01's former
literal typing it had a derivation at every `bytesN`, with lengths 1 to 32. -/
theorem zeroLength_illTyped (Γ : Ctx) (τ : STy) :
    ¬ HasType Γ (.member (.lit (.num (.dec 0 0 0))) "length") τ := by
  intro ⟨d⟩
  generalize hx : "length" = x at d
  cases d
  all_goals first
    | (cases ‹(Syn.member _ _).const = _›; done)
    | (cases ‹(Syn.member _ _).binOp? = _›; done)
    | skip
  case length σ da hl =>
    have hc := (Typed.constShape da rfl).isConstTy
    cases σ <;> first | (cases hc; done) | (cases hl; done)
  case balance p da =>
    cases (Typed.constShape da rfl).isConstTy
  case member l dn i da _ =>
    cases (Typed.constShape da rfl).isConstTy

/-- info: 'Solidity.Source.Typed.constShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Typed.constShape

/-- info: 'Solidity.Source.zeroLength_illTyped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zeroLength_illTyped

end Solidity.Source
