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

/-- A copy into storage is never an implicit conversion. -/
theorem STy.implicit_of_copiesTo {B : DeclName → DeclName → Bool} {σ τ : STy} (h : σ.copiesTo τ = true) :
    σ.implicit B τ = false := by
  cases σ <;> cases τ
  all_goals first
    | (cases h; done)
    | rfl
    | skip
  case bytes.bytes l1 l2 | string.string l1 l2 =>
    cases l1 <;> cases l2 <;> first | rfl | (cases h; done)
  case stringLit.bytes l2 | stringLit.string l2 =>
    cases l2 <;> first | rfl | (cases h; done)
  case array.array l1 e1 n1 l2 e2 n2 =>
    cases l1 <;> cases l2 <;> first
      | (cases h; done)
      | (change (_ && false) = false; exact Bool.and_false _)
  case struct.struct l1 d1 l2 d2 =>
    cases l1 <;> cases l2 <;> first
      | (cases h; done)
      | (change (_ && false) = false; exact Bool.and_false _)

/-- **Indexing.** -/
theorem uniqE_index {Γ : Ctx} {a : Syn .expr} {o : Syn (.opt .expr)} (ih : Uniq Γ (sizeOf (Syn.index a o))) :
    UniqE Γ (.index a o) := by
  intro τ τ' d d'
  have hce : (Syn.index a o).const = Option.none := rfl
  have hbo : (Syn.index a o).binOp? = Option.none := rfl
  cases d with
  | @indexArray a i l τe σ n da di h hb =>
    have hs : sizeOf a < sizeOf (Syn.index a (.some i)) ∧ sizeOf i < sizeOf (Syn.index a (.some i)) := by
      simp only [Syn.index.sizeOf_spec, Syn.some.sizeOf_spec]; omega
    cases d' with
    | indexArray da' di' _ _ =>
      obtain ⟨h1, e1⟩ := ih.e a hs.1 da da'
      cases h1
      obtain ⟨h2, e2⟩ := ih.e i hs.2 di di'
      cases h2
      refine ⟨rfl, ?_⟩
      simp only [Typed.toR]
      rw [eq_of_heq e1, eq_of_heq e2]
    | indexMapping da' _ _ => cases (ih.e a hs.1 da da').1
    | indexBytes da' hk _ _ _ =>
      obtain ⟨h1, -⟩ := ih.e a hs.1 da da'
      cases h1; cases hk
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | @indexMapping a i τk τv σ da di h =>
    have hs : sizeOf a < sizeOf (Syn.index a (.some i)) ∧ sizeOf i < sizeOf (Syn.index a (.some i)) := by
      simp only [Syn.index.sizeOf_spec, Syn.some.sizeOf_spec]; omega
    cases d' with
    | indexArray da' _ _ _ => cases (ih.e a hs.1 da da').1
    | indexMapping da' di' _ =>
      obtain ⟨h1, e1⟩ := ih.e a hs.1 da da'
      cases h1
      obtain ⟨h2, e2⟩ := ih.e i hs.2 di di'
      cases h2
      refine ⟨rfl, ?_⟩
      simp only [Typed.toR]
      rw [eq_of_heq e1, eq_of_heq e2]
    | indexBytes da' hk _ _ _ =>
      obtain ⟨h1, -⟩ := ih.e a hs.1 da da'
      cases h1; cases hk
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | @indexBytes a i τa σ da hk di h hb =>
    have hs : sizeOf a < sizeOf (Syn.index a (.some i)) ∧ sizeOf i < sizeOf (Syn.index a (.some i)) := by
      simp only [Syn.index.sizeOf_spec, Syn.some.sizeOf_spec]; omega
    cases d' with
    | indexArray da' _ _ _ =>
      obtain ⟨h1, -⟩ := ih.e a hs.1 da da'
      cases h1; cases hk
    | indexMapping da' _ _ =>
      obtain ⟨h1, -⟩ := ih.e a hs.1 da da'
      cases h1; cases hk
    | indexBytes da' _ di' _ _ =>
      obtain ⟨h1, e1⟩ := ih.e a hs.1 da da'
      cases h1
      obtain ⟨h2, e2⟩ := ih.e i hs.2 di di'
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

/-- **Assignments.** -/
theorem uniqE_assign {Γ : Ctx} {op : AssignOp} {a b : Syn .expr} (ih : Uniq Γ (sizeOf (Syn.assign op a b))) :
    UniqE Γ (.assign op a b) := by
  intro τ τ' d d'
  have hce : (Syn.assign op a b).const = Option.none := rfl
  have hbo : (Syn.assign op a b).binOp? = Option.none := rfl
  have hs : sizeOf a < sizeOf (Syn.assign op a b) ∧ sizeOf b < sizeOf (Syn.assign op a b) := by
    simp only [Syn.assign.sizeOf_spec]; omega
  cases d with
  | assign l1 db h _ =>
    cases d' with
    | assign l2 db' _ _ =>
      obtain ⟨h1, e1⟩ := ih.l a hs.1 l1 l2
      cases h1
      obtain ⟨h2, e2⟩ := ih.e b hs.2 db db'
      cases h2
      refine ⟨rfl, ?_⟩
      simp only [Typed.toR]
      rw [eq_of_heq e1, eq_of_heq e2]
    | compound _ _ h' => cases h'
    | assignCopy l2 db' h' =>
      obtain ⟨h1, -⟩ := ih.l a hs.1 l1 l2
      cases h1
      obtain ⟨h2, -⟩ := ih.e b hs.2 db db'
      cases h2
      rw [STy.implicit_of_copiesTo h'] at h; cases h
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | compound l1 db h =>
    cases d' with
    | assign _ _ _ _ => cases h
    | compound l2 db' _ =>
      obtain ⟨h1, e1⟩ := ih.l a hs.1 l1 l2
      cases h1
      obtain ⟨h2, e2⟩ := ih.e b hs.2 db db'
      cases h2
      refine ⟨rfl, ?_⟩
      simp only [Typed.toR]
      rw [eq_of_heq e1, eq_of_heq e2]
    | assignCopy _ _ _ => cases h
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | assignCopy l1 db h =>
    cases d' with
    | assign l2 db' h' _ =>
      obtain ⟨h1, -⟩ := ih.l a hs.1 l1 l2
      cases h1
      obtain ⟨h2, -⟩ := ih.e b hs.2 db db'
      cases h2
      rw [STy.implicit_of_copiesTo h] at h'; cases h'
    | compound _ _ h' => cases h'
    | assignCopy l2 db' _ =>
      obtain ⟨h1, e1⟩ := ih.l a hs.1 l1 l2
      cases h1
      obtain ⟨h2, e2⟩ := ih.e b hs.2 db db'
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

/-- **Members.** -/
theorem uniqE_member {Γ : Ctx} {a : Syn .expr} {x : String} (ih : Uniq Γ (sizeOf (Syn.member a x))) :
    UniqE Γ (.member a x) := by
  intro τ τ' d
  have hce : (Syn.member a x).const = Option.none := rfl
  have hbo : (Syn.member a x).binOp? = Option.none := rfl
  have hs : sizeOf a < sizeOf (Syn.member a x) := by simp only [Syn.member.sizeOf_spec]; omega
  suffices H : ∀ x0 (d' : Typed Γ (.member a x0) τ'), (x == x0) = true → τ = τ' ∧ HEq d.toR d'.toR from
    fun d' => H x d' (beq_self_eq_true x)
  intro x0 d' hx
  cases d with
  | length da h =>
    cases d' with
    | length da' h' =>
      obtain ⟨h1, e1⟩ := ih.e a hs da da'
      cases h1
      rw [h] at h'; cases h'
      exact ⟨rfl, by simp only [Typed.toR]; rw [eq_of_heq e1]⟩
    | balance _ => exact absurd hx (by decide)
    | magic hr _ hm _ => cases Typed.ident_builtin hr da; cases hm
    | member da' _ =>
      obtain ⟨h1, -⟩ := ih.e a hs da da'
      cases h1; cases h
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | balance da =>
    cases d' with
    | length _ _ => exact absurd hx (by decide)
    | balance da' =>
      obtain ⟨h1, e1⟩ := ih.e a hs da da'
      cases h1
      exact ⟨rfl, by simp only [Typed.toR]; rw [eq_of_heq e1]⟩
    | magic hr _ hm _ => cases Typed.ident_builtin hr da; cases hm
    | member da' _ => cases (ih.e a hs da da').1
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | magic hr _ hm _ =>
    cases d' with
    | length da' _ => cases Typed.ident_builtin hr da'; cases hm
    | balance da' => cases Typed.ident_builtin hr da'; cases hm
    | magic hr' _ hm' _ =>
      cases (eq_of_beq hx)
      rw [hr] at hr'; cases hr'
      rw [hm] at hm'; cases hm'
      exact ⟨rfl, HEq.rfl⟩
    | member da' _ => cases Typed.ident_builtin hr da'; cases hm
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | member da h =>
    cases d' with
    | length da' h' =>
      obtain ⟨h1, -⟩ := ih.e a hs da da'
      cases h1; cases h'
    | balance da' => cases (ih.e a hs da da').1
    | magic hr _ hm _ => cases Typed.ident_builtin hr da; cases hm
    | member da' h' =>
      cases (eq_of_beq hx)
      obtain ⟨h1, e1⟩ := ih.e a hs da da'
      cases h1
      rw [h] at h'; cases h'
      exact ⟨rfl, by simp only [Typed.toR]; rw [eq_of_heq e1]⟩
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | _ => first
    | exact (no_const hce ‹_›).elim
    | (exfalso; apply no_binOp hbo; assumption)

/-! ### What a callee name denotes -/

theorem Ctx.convTarget_spec {Γ : Ctx} {n : String} {τ : STy} (h : Γ.convTarget n = Option.some τ) :
    ∃ d, Γ.resolve n = Option.some (.decls [d]) ∧ d.kind ≠ .function ∧ d.kind ≠ .struct := by
  unfold Ctx.convTarget at h
  split at h
  · rename_i d hr
    refine ⟨d, hr, ?_⟩
    revert h
    cases d.kind <;> intro h <;> first | (cases h; done) | exact ⟨by decide, by decide⟩
  · cases h

theorem Ctx.structOf_spec {Γ : Ctx} {n : String} {dn : DeclName} (h : Γ.structOf n = Option.some dn) :
    ∃ d, Γ.resolve n = Option.some (.decls [d]) ∧ d.kind = .struct ∧ dn = ⟨d.scope, d.name⟩ := by
  unfold Ctx.structOf at h
  split at h
  · rename_i d hr
    by_cases hk : d.kind = .struct
    · simp only [hk, beq_self_eq_true, if_true, Option.some.injEq] at h
      exact ⟨d, hr, hk, h.symm⟩
    · have : (d.kind == DeclKind.struct) = false := by simp only [beq_eq_false_iff_ne, ne_eq, hk, not_false_eq_true]
      simp only [this, Bool.false_eq_true, if_false, reduceCtorEq] at h
  · cases h

theorem Ctx.functions_spec {Γ : Ctx} {n : String} {d : Decl} (h : d ∈ Γ.functions n) :
    ∃ ds, Γ.resolve n = Option.some (.decls ds) ∧ d ∈ ds ∧ d.kind = .function := by
  unfold Ctx.functions at h
  split at h
  · rename_i ds hr
    have hm := List.mem_filter.1 h
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    exact ⟨ds, hr, hm.1, hm.2.1⟩
  · cases h

theorem mem_of_filter_singleton {α : Type} {p : α → Bool} {l : List α} {d : α} (h : l.filter p = [d]) : d ∈ l :=
  (List.mem_filter.1 (h ▸ List.mem_singleton_self d)).1

/-- Two names that resolve differently. -/
theorem resolve_conflict {Γ : Ctx} {n : String} {a b : Denot} (ha : Γ.resolve n = Option.some a)
    (hb : Γ.resolve n = Option.some b) : a = b := by
  rw [ha] at hb; cases hb; rfl

/-- **Calls of a name**: conversions to a contract or enum, internal calls,
builtins, struct construction. -/
theorem uniqE_callIdent {Γ : Ctx} {n : String} {A : Syn .callArgs}
    (ih : Uniq Γ (sizeOf (Syn.call (.ident n) A))) : UniqE Γ (.call (.ident n) A) := by
  intro τ τ' d d'
  have hce : (Syn.call (.ident n) A).const = Option.none := rfl
  have hbo : (Syn.call (.ident n) A).binOp? = Option.none := rfl
  cases d with
  | @convUser x _ τ1 σ hc dx h =>
    obtain ⟨d0, hr0, hk1, hk2⟩ := Ctx.convTarget_spec hc
    cases d' with
    | convUser hc' dx' _ =>
      rw [hc] at hc'; cases hc'
      obtain ⟨h1, e1⟩ := ih.e x (by simp only [Syn.call.sizeOf_spec, Syn.ident.sizeOf_spec, Syn.positional.sizeOf_spec, Syn.cons.sizeOf_spec]; omega) dx dx'
      cases h1
      exact ⟨rfl, by simp only [Typed.toR]; rw [eq_of_heq e1]⟩
    | callInternal _ hf' _ =>
      obtain ⟨ds, hr1, hm, hk⟩ := Ctx.functions_spec (mem_of_filter_singleton hf')
      cases resolve_conflict hr0 hr1
      cases List.mem_singleton.1 hm
      exact absurd hk hk1
    | builtinCall hr _ _ _ => cases resolve_conflict hr0 hr
    | structNew hs _ _ _ =>
      obtain ⟨d1, hr1, hk, -⟩ := Ctx.structOf_spec hs
      cases resolve_conflict hr0 hr1
      exact absurd hk hk2
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | @callInternal _ args dd ps rs σs da hf hs =>
    obtain ⟨ds, hr0, hm0, hk0⟩ := Ctx.functions_spec (mem_of_filter_singleton hf)
    cases d' with
    | convUser hc _ _ =>
      obtain ⟨d1, hr1, hk1, -⟩ := Ctx.convTarget_spec hc
      cases resolve_conflict hr0 hr1
      cases List.mem_singleton.1 hm0
      exact absurd hk0 hk1
    | callInternal da' hf' hs' =>
      obtain ⟨h1, e1⟩ := ih.a args (by simp only [Syn.call.sizeOf_spec, Syn.ident.sizeOf_spec, Syn.positional.sizeOf_spec, Syn.cons.sizeOf_spec]; omega) da da'
      cases h1
      rw [hf] at hf'; cases hf'
      rw [hs] at hs'; cases hs'
      exact ⟨rfl, by simp only [Typed.toR]; rw [eq_of_heq e1]⟩
    | builtinCall hr _ _ _ => cases resolve_conflict hr0 hr
    | structNew hs' _ _ _ =>
      obtain ⟨d1, hr1, hk, -⟩ := Ctx.structOf_spec hs'
      cases resolve_conflict hr0 hr1
      cases List.mem_singleton.1 hm0
      rw [hk0] at hk; cases hk
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | @builtinCall _ args b σs τ1 _ hr hst da h =>
    cases d' with
    | convUser hc _ _ =>
      obtain ⟨d1, hr1, -, -⟩ := Ctx.convTarget_spec hc
      cases resolve_conflict hr hr1
    | callInternal _ hf' _ =>
      obtain ⟨ds, hr1, -, -⟩ := Ctx.functions_spec (mem_of_filter_singleton hf')
      cases resolve_conflict hr hr1
    | builtinCall hr' _ da' h' =>
      cases resolve_conflict hr hr'
      obtain ⟨h1, e1⟩ := ih.a args (by simp only [Syn.call.sizeOf_spec, Syn.ident.sizeOf_spec, Syn.positional.sizeOf_spec, Syn.cons.sizeOf_spec]; omega) da da'
      cases h1
      rw [h] at h'; cases h'
      exact ⟨rfl, by simp only [Typed.toR]; rw [eq_of_heq e1]⟩
    | structNew hs _ _ _ =>
      obtain ⟨d1, hr1, -, -⟩ := Ctx.structOf_spec hs
      cases resolve_conflict hr hr1
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | @structNew _ args dn fs σs hs hf da h =>
    obtain ⟨d0, hr0, hk0, -⟩ := Ctx.structOf_spec hs
    cases d' with
    | convUser hc _ _ =>
      obtain ⟨d1, hr1, -, hk1⟩ := Ctx.convTarget_spec hc
      cases resolve_conflict hr0 hr1
      exact absurd hk0 hk1
    | callInternal _ hf' _ =>
      obtain ⟨ds, hr1, hm, hk⟩ := Ctx.functions_spec (mem_of_filter_singleton hf')
      cases resolve_conflict hr0 hr1
      cases List.mem_singleton.1 hm
      rw [hk0] at hk; cases hk
    | builtinCall hr _ _ _ => cases resolve_conflict hr0 hr
    | structNew hs' hf' da' _ =>
      rw [hs] at hs'; cases hs'
      rw [hf] at hf'; cases hf'
      obtain ⟨h1, e1⟩ := ih.a args (by simp only [Syn.call.sizeOf_spec, Syn.ident.sizeOf_spec, Syn.positional.sizeOf_spec, Syn.cons.sizeOf_spec]; omega) da da'
      cases h1
      exact ⟨rfl, by simp only [Typed.toR]; rw [eq_of_heq e1]⟩
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | _ => first
    | exact (no_const hce ‹_›).elim
    | (exfalso; apply no_binOp hbo; assumption)

/-- **Calls through a member**: external calls, payments, ABI encoding. -/
theorem uniqE_callMember {Γ : Ctx} {c : Syn .expr} {n : String} {A : Syn .callArgs}
    (ih : Uniq Γ (sizeOf (Syn.call (.member c n) A))) : UniqE Γ (.call (.member c n) A) := by
  intro τ τ' d
  have hce : (Syn.call (.member c n) A).const = Option.none := rfl
  have hbo : (Syn.call (.member c n) A).binOp? = Option.none := rfl
  suffices H : ∀ n0 (d' : Typed Γ (.call (.member c n0) A) τ'), (n == n0) = true →
      τ = τ' ∧ HEq d.toR d'.toR from fun d' => H n d' (beq_self_eq_true n)
  intro n0 d' hn
  cases d with
  | @extCall c _ args dn dd ps rs σs dc da hf hs =>
    have hsz : sizeOf c < sizeOf (Syn.call (.member c n) (.positional args)) ∧
        sizeOf args < sizeOf (Syn.call (.member c n) (.positional args)) := by simp only [Syn.call.sizeOf_spec, Syn.member.sizeOf_spec, Syn.positional.sizeOf_spec, Syn.cons.sizeOf_spec]; omega
    cases d' with
    | extCall dc' da' hf' hs' =>
      cases (eq_of_beq hn)
      obtain ⟨h1, e1⟩ := ih.e c hsz.1 dc dc'
      cases h1
      obtain ⟨h2, e2⟩ := ih.a args hsz.2 da da'
      cases h2
      rw [hf] at hf'; cases hf'
      rw [hs] at hs'; cases hs'
      refine ⟨rfl, ?_⟩
      simp only [Typed.toR]
      rw [eq_of_heq e1, eq_of_heq e2]
    | transfer da' _ _ => cases (ih.e c hsz.1 dc da').1
    | send da' _ _ => cases (ih.e c hsz.1 dc da').1
    | abiEncode hr _ _ _ => cases Typed.ident_builtin hr dc
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | @transfer _ v σ da dv h =>
    have hsz : sizeOf c < sizeOf (Syn.call (.member c "transfer") (.positional (.cons v .nil))) ∧
        sizeOf v < sizeOf (Syn.call (.member c "transfer") (.positional (.cons v .nil))) := by simp only [Syn.call.sizeOf_spec, Syn.member.sizeOf_spec, Syn.positional.sizeOf_spec, Syn.cons.sizeOf_spec]; omega
    cases d' with
    | extCall dc' _ _ _ => cases (ih.e c hsz.1 da dc').1
    | transfer da' dv' _ =>
      obtain ⟨-, e1⟩ := ih.e c hsz.1 da da'
      obtain ⟨h2, e2⟩ := ih.e v hsz.2 dv dv'
      cases h2
      refine ⟨rfl, ?_⟩
      simp only [Typed.toR]
      rw [eq_of_heq e1, eq_of_heq e2]
    | send _ _ _ => exact absurd hn (by decide)
    | abiEncode hr _ _ _ => cases Typed.ident_builtin hr da
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | @send _ v σ da dv h =>
    have hsz : sizeOf c < sizeOf (Syn.call (.member c "send") (.positional (.cons v .nil))) ∧
        sizeOf v < sizeOf (Syn.call (.member c "send") (.positional (.cons v .nil))) := by simp only [Syn.call.sizeOf_spec, Syn.member.sizeOf_spec, Syn.positional.sizeOf_spec, Syn.cons.sizeOf_spec]; omega
    cases d' with
    | extCall dc' _ _ _ => cases (ih.e c hsz.1 da dc').1
    | transfer _ _ _ => exact absurd hn (by decide)
    | send da' dv' _ =>
      obtain ⟨-, e1⟩ := ih.e c hsz.1 da da'
      obtain ⟨h2, e2⟩ := ih.e v hsz.2 dv dv'
      cases h2
      refine ⟨rfl, ?_⟩
      simp only [Typed.toR]
      rw [eq_of_heq e1, eq_of_heq e2]
    | abiEncode hr _ _ _ => cases Typed.ident_builtin hr da
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | @abiEncode g m args σs k hr hk da h =>
    cases d' with
    | extCall dc' _ _ _ => cases Typed.ident_builtin hr dc'
    | transfer da' _ _ => cases Typed.ident_builtin hr da'
    | send da' _ _ => cases Typed.ident_builtin hr da'
    | abiEncode _ hk' da' _ =>
      cases (eq_of_beq hn)
      rw [hk] at hk'; cases hk'
      have hsz : sizeOf args < sizeOf (Syn.call (.member (.ident g) n) (.positional args)) := by
        simp only [Syn.call.sizeOf_spec, Syn.member.sizeOf_spec, Syn.positional.sizeOf_spec]; omega
      obtain ⟨h1, e1⟩ := ih.a args hsz da da'
      cases h1
      exact ⟨rfl, by simp only [Typed.toR]; rw [eq_of_heq e1]⟩
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | _ => first
    | exact (no_const hce ‹_›).elim
    | (exfalso; apply no_binOp hbo; assumption)

/-- **Conversions to an elementary type** (`T(x)`). -/
theorem uniqE_callElem {Γ : Ctx} {el : Elem} {hel : el ≠ .addressPayable} {A : Syn .callArgs}
    (ih : Uniq Γ (sizeOf (Syn.call (.elemType el hel) A))) : UniqE Γ (.call (.elemType el hel) A) := by
  intro τ τ' d d'
  have hce : (Syn.call (.elemType el hel) A).const = Option.none := rfl
  have hbo : (Syn.call (.elemType el hel) A).binOp? = Option.none := rfl
  cases d with
  | @convElem x _ _ σ τ1 dx hτ h =>
    cases d' with
    | convElem dx' hτ' _ =>
      have hsz : sizeOf x < sizeOf (Syn.call (.elemType el hel) (.positional (.cons x .nil))) := by
        simp only [Syn.call.sizeOf_spec, Syn.positional.sizeOf_spec, Syn.cons.sizeOf_spec]; omega
      obtain ⟨h1, e1⟩ := ih.e x hsz dx dx'
      cases h1
      subst hτ hτ'
      exact ⟨rfl, by simp only [Typed.toR]; rw [eq_of_heq e1]⟩
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | _ => first
    | exact (no_const hce ‹_›).elim
    | (exfalso; apply no_binOp hbo; assumption)

/-- **External calls with value** (`c.f{value: v}(args)`). -/
theorem uniqE_callOpts {Γ : Ctx} {f : Syn .expr} {o : Syn .namedArg} {os : Syn (.list .namedArg)}
    {A : Syn .callArgs} (ih : Uniq Γ (sizeOf (Syn.call (.callOptions f o os) A))) :
    UniqE Γ (.call (.callOptions f o os) A) := by
  intro τ τ' d d'
  have hce : (Syn.call (.callOptions f o os) A).const = Option.none := rfl
  have hbo : (Syn.call (.callOptions f o os) A).binOp? = Option.none := rfl
  cases d with
  | @extCallValue c v fn args dn dd ps rs σs σ dc dv hv da hf hs hm =>
    have hsz : sizeOf c < sizeOf (Syn.call (.callOptions (.member c fn) (.namedArg "value" v) .nil) (.positional args)) ∧
        sizeOf v < sizeOf (Syn.call (.callOptions (.member c fn) (.namedArg "value" v) .nil) (.positional args)) ∧
        sizeOf args < sizeOf (Syn.call (.callOptions (.member c fn) (.namedArg "value" v) .nil) (.positional args)) := by
      simp only [Syn.call.sizeOf_spec, Syn.callOptions.sizeOf_spec, Syn.member.sizeOf_spec,
        Syn.namedArg.sizeOf_spec, Syn.positional.sizeOf_spec]; omega
    cases d' with
    | extCallValue dc' dv' _ da' hf' hs' _ =>
      obtain ⟨h1, e1⟩ := ih.e c hsz.1 dc dc'
      cases h1
      obtain ⟨h2, e2⟩ := ih.e v hsz.2.1 dv dv'
      cases h2
      obtain ⟨h3, e3⟩ := ih.a args hsz.2.2 da da'
      cases h3
      rw [hf] at hf'; cases hf'
      rw [hs] at hs'; cases hs'
      refine ⟨rfl, ?_⟩
      simp only [Typed.toR]
      rw [eq_of_heq e1, eq_of_heq e2, eq_of_heq e3]
    | _ => first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hbo; assumption)
  | _ => first
    | exact (no_const hce ‹_›).elim
    | (exfalso; apply no_binOp hbo; assumption)

/-- **Lvalues.** -/
theorem uniqL_of {Γ : Ctx} {e : Syn .expr} (ih : Uniq Γ (sizeOf e)) : UniqL Γ e := by
  intro τ τ' l l'
  cases l with
  | loc hr ht =>
    cases l' with
    | loc hr' ht' => rw [hr] at hr'; cases hr'; rw [ht] at ht'; cases ht'; exact ⟨rfl, HEq.rfl⟩
    | state hr' _ _ => rw [hr] at hr'; cases hr'
  | state hr hv _ =>
    cases l' with
    | loc hr' _ => rw [hr] at hr'; cases hr'
    | state hr' hv' _ => rw [hr] at hr'; cases hr'; rw [hv] at hv'; cases hv'; exact ⟨rfl, HEq.rfl⟩
  | @paren x σ l1 =>
    cases l' with
    | paren l2 =>
      have hs : sizeOf x < sizeOf (Syn.tuple (.some x) .nil) := by
        simp only [Syn.tuple.sizeOf_spec, Syn.some.sizeOf_spec]; omega
      obtain ⟨h1, e1⟩ := ih.l x hs l1 l2
      cases h1
      exact ⟨rfl, by simp only [LVal.toR]; exact e1⟩
  | @indexArray a i dl τe σ n da hl di h hb =>
    have hs : sizeOf a < sizeOf (Syn.index a (.some i)) ∧ sizeOf i < sizeOf (Syn.index a (.some i)) := by
      simp only [Syn.index.sizeOf_spec, Syn.some.sizeOf_spec]; omega
    cases l' with
    | indexArray da' _ di' _ _ =>
      obtain ⟨h1, e1⟩ := ih.e a hs.1 da da'
      cases h1
      obtain ⟨h2, e2⟩ := ih.e i hs.2 di di'
      cases h2
      refine ⟨rfl, ?_⟩
      simp only [LVal.toR]
      rw [eq_of_heq e1, eq_of_heq e2]
    | indexMapping da' _ _ => cases (ih.e a hs.1 da da').1
    | indexBytes da' _ _ _ => cases (ih.e a hs.1 da da').1
  | @indexMapping a i τk τv σ da di h =>
    have hs : sizeOf a < sizeOf (Syn.index a (.some i)) ∧ sizeOf i < sizeOf (Syn.index a (.some i)) := by
      simp only [Syn.index.sizeOf_spec, Syn.some.sizeOf_spec]; omega
    cases l' with
    | indexArray da' _ _ _ _ => cases (ih.e a hs.1 da da').1
    | indexMapping da' di' _ =>
      obtain ⟨h1, e1⟩ := ih.e a hs.1 da da'
      cases h1
      obtain ⟨h2, e2⟩ := ih.e i hs.2 di di'
      cases h2
      refine ⟨rfl, ?_⟩
      simp only [LVal.toR]
      rw [eq_of_heq e1, eq_of_heq e2]
    | indexBytes da' _ _ _ => cases (ih.e a hs.1 da da').1
  | @indexBytes a i dl σ da hl di h =>
    have hs : sizeOf a < sizeOf (Syn.index a (.some i)) ∧ sizeOf i < sizeOf (Syn.index a (.some i)) := by
      simp only [Syn.index.sizeOf_spec, Syn.some.sizeOf_spec]; omega
    cases l' with
    | indexArray da' _ _ _ _ => cases (ih.e a hs.1 da da').1
    | indexMapping da' _ _ => cases (ih.e a hs.1 da da').1
    | indexBytes da' _ di' _ =>
      obtain ⟨h1, e1⟩ := ih.e a hs.1 da da'
      cases h1
      obtain ⟨h2, e2⟩ := ih.e i hs.2 di di'
      cases h2
      refine ⟨rfl, ?_⟩
      simp only [LVal.toR]
      rw [eq_of_heq e1, eq_of_heq e2]
  | @member a x dl dn i τ da hl h =>
    cases l' with
    | member da' _ h' =>
      have hs : sizeOf a < sizeOf (Syn.member a x) := by simp only [Syn.member.sizeOf_spec]; omega
      obtain ⟨h1, e1⟩ := ih.e a hs da da'
      cases h1
      rw [h] at h'; cases h'
      exact ⟨rfl, by simp only [LVal.toR]; rw [eq_of_heq e1]⟩

/-- **Argument lists.** -/
theorem uniqA_of {Γ : Ctx} {es : Syn (.list .expr)} (ih : Uniq Γ (sizeOf es)) : UniqA Γ es := by
  intro τs τs' d d'
  cases d with
  | nil => cases d'; exact ⟨rfl, HEq.rfl⟩
  | @cons e es τ τs d1 ds =>
    cases d' with
    | cons d2 ds' =>
      have hs : sizeOf e < sizeOf (Syn.cons e es) ∧ sizeOf es < sizeOf (Syn.cons e es) := by
        simp only [Syn.cons.sizeOf_spec]; omega
      obtain ⟨h1, e1⟩ := ih.e e hs.1 d1 d2
      cases h1
      obtain ⟨h2, e2⟩ := ih.a es hs.2 ds ds'
      cases h2
      refine ⟨rfl, ?_⟩
      simp only [TypedArgs.toR]
      rw [eq_of_heq e1, eq_of_heq e2]

/-- **Tuple slots.** -/
theorem uniqS_of {Γ : Ctx} {sl : Syn (.list (.opt .expr))} (ih : Uniq Γ (sizeOf sl)) : UniqS Γ sl := by
  intro τs τs' d d'
  cases d with
  | nil => cases d'; exact ⟨rfl, HEq.rfl, HEq.rfl⟩
  | @cons e es τ τs d1 ds =>
    cases d' with
    | cons d2 ds' =>
      have hs : sizeOf e < sizeOf (Syn.cons (.some e) es) ∧ sizeOf es < sizeOf (Syn.cons (.some e) es) := by
        simp only [Syn.cons.sizeOf_spec, Syn.some.sizeOf_spec]; omega
      obtain ⟨h1, e1⟩ := ih.e e hs.1 d1 d2
      cases h1
      obtain ⟨h2, e2, e3⟩ := ih.s es hs.2 ds ds'
      cases h2
      refine ⟨rfl, ?_, ?_⟩
      · simp only [TypedSlots.toR]
        rw [eq_of_heq e1, eq_of_heq e2]
      · simp only [TypedArgs.ofSlots]
        rw [eq_of_heq e1, eq_of_heq e3]

/-- An expression no rule types. -/
theorem uniqE_empty {Γ : Ctx} {e : Syn .expr} (h : ∀ τ, Typed Γ e τ → False) : UniqE Γ e :=
  fun d _ => (h _ d).elim

/-- **Every expression's derivations agree**, given the hypothesis below its size. -/
theorem uniqE_of {Γ : Ctx} {e : Syn .expr} (ih : Uniq Γ (sizeOf e)) : UniqE Γ e := by
  cases hce : e.const with
  | some q => exact fun d d' => Typed.const_unique d d' hce
  | none =>
  cases hb : e.binOp? with
  | some p =>
    obtain ⟨k, a, b⟩ := p
    exact uniqE_bin hb hce ih
  | none =>
  cases e with
  | cond c a b => exact uniqE_cond ih
  | ident x => exact uniqE_ident ih
  | lit l => exact uniqE_lit hce
  | tuple o sl => exact uniqE_tuple hce ih
  | unaryPrefix op x => exact uniqE_prefix hce ih
  | unarySuffix op x => exact uniqE_suffix ih
  | payableConv A => exact uniqE_payable ih
  | index a o => exact uniqE_index ih
  | assign op a b => exact uniqE_assign ih
  | member a x => exact uniqE_member ih
  | call f A =>
    cases f with
    | ident n => exact uniqE_callIdent ih
    | member c n => exact uniqE_callMember ih
    | elemType el h => exact uniqE_callElem ih
    | callOptions f o os => exact uniqE_callOpts ih
    | _ =>
      apply uniqE_empty
      intro τ d
      cases d <;> first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hb; assumption)
  | _ =>
    first
    | (cases hb; done)
    | (rename_i op _ _; cases op <;> cases hb; done)
    | (apply uniqE_empty
       intro τ d
       cases d <;> first
      | exact (no_const hce ‹_›).elim
      | (exfalso; apply no_binOp hb; assumption))

/-- **Uniqueness below every size.** -/
theorem uniq_all (Γ : Ctx) : ∀ n, Uniq Γ n
  | 0 => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 =>
    have ih := uniq_all Γ n
    ⟨fun _ h => uniqE_of (ih.mono (by omega)), fun _ h => uniqL_of (ih.mono (by omega)),
      fun _ h => uniqA_of (ih.mono (by omega)), fun _ h => uniqS_of (ih.mono (by omega))⟩

/-- **Typing derivations agree** (Q1): any two derivations of one
expression have one type and elaborate to one resolved term, so a unit's
meaning does not depend on the derivation an elaboration carries. -/
theorem Typed.unique {Γ : Ctx} {e : Syn .expr} {τ τ' : STy} (d : Typed Γ e τ) (d' : Typed Γ e τ') :
    τ = τ' ∧ HEq d.toR d'.toR :=
  (uniq_all Γ (sizeOf e + 1)).e e (by omega) d d'

/-- Lvalue derivations agree. -/
theorem LVal.unique {Γ : Ctx} {e : Syn .expr} {τ τ' : STy} (l : LVal Γ e τ) (l' : LVal Γ e τ') :
    τ = τ' ∧ HEq l.toR l'.toR :=
  (uniq_all Γ (sizeOf e + 1)).l e (by omega) l l'

/-- Argument-list derivations agree. -/
theorem TypedArgs.unique {Γ : Ctx} {es : Syn (.list .expr)} {τs τs' : List STy} (d : TypedArgs Γ es τs)
    (d' : TypedArgs Γ es τs') : τs = τs' ∧ HEq d.toR d'.toR :=
  (uniq_all Γ (sizeOf es + 1)).a es (by omega) d d'

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
