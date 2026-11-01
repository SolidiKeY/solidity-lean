import Solidity.Frontend.Static.InferComplete
import Solidity.Language.FixedPoint.Literals

/-!
# Standalone constants at their mobile types (G13, backfill item 5)

S01 types a constant expression by its exact rational (`STy.rational`) and,
where an expression needs a type of its own (tuple components, conditional
branches, shift operands), takes `STy.mobile`: an integral constant's
smallest integer type, while a fractional constant keeps its rational type,
which no variable has.  solc gives a fractional constant its mobile
fixed-point type (`RationalNumberType::mobileType`), truncating it there.

Backfill item 5 adopts solc's rule: a standalone fractional constant takes
`Fx.mobileFx?`'s type with the value truncated toward zero
(`Fx.mobileConst?`, `Solidity/Language/FixedPoint/Literals.lean`), also as
an ABI argument (`Fx.abiConst?`; solc 0.8.38 refuses that one, 6090).

- `STy.standalone`: the type an expression stands alone at: S01's mobile
  type, and for a fractional constant with a mobile fixed-point type, that
  type (`FxTy.toFixTy`; S01's `FixTy` has `FxTy`'s fields).
- `StandaloneTyped`, `AbiArgTyped`: the relations, over S01's `HasType`
  (`AbiArgTyped` is only the constant-type restriction on ABI arguments).
- `standaloneTys`: the checker, over G13's inference; `standalone_iff`,
  `abiArg_iff`: it decides them (by `hasType_iff`).
- `standalone_value`: a constant standing at `.fixed f` is fractional and
  `Fx.mobileConst?` gives its value at a type with `f`'s fields;
  `standalone_toFixedExplicit`: S01's own explicit conversion
  (`Q.toFixedExplicit?`) to `f` is that value, for S01's unreduced
  rational; `standalone_abi`: and its ABI word is `Fx.abiConst?`'s.
- `STy.standalone` does not recurse into tuples: a tuple's components keep
  S01's `STy.mobile`.

S01's own rules still use `STy.mobile`; reading `STy.standalone` there (and
in S02's meaning) is a handoff to lane-semantics.
-/

namespace Solidity.Frontend.Static

open Solidity.Source
open Solidity.Language.FixedPoint

/-- S01's rational as a Lean `Rat`. -/
def _root_.Solidity.Source.Q.toRat (q : Q) : Rat := mkRat q.num q.den

/-- The reference semantics' fixed-point type as S01's. -/
def _root_.Solidity.Language.FixedPoint.FxTy.toFixTy (t : FxTy) : FixTy :=
  ⟨t.signed, t.bits, t.digits, by
    have h := t.valid
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    omega⟩

/-- **The type an expression stands alone at**: S01's mobile type, except
that a fractional constant takes its mobile fixed-point type (if any). -/
def _root_.Solidity.Source.STy.standalone : STy → STy
  | .rational q =>
    if q.isInt then (STy.rational q).mobile
    else match Fx.mobileFx? q.toRat with
      | Option.some m => .fixed m.toFixTy
      | Option.none => .rational q
  | τ => τ.mobile

/-- **Standalone typing**: `e` has type `σ` (S01) and stands alone at
`σ.standalone`. -/
def StandaloneTyped (Γ : Ctx) (e : Syn .expr) (τ : STy) : Prop :=
  ∃ σ, HasType Γ e σ ∧ σ.standalone = τ

/-- Whether a type is a constant's own type, which no value has (numeric
constants, `STy.isConstTy`, and string literals). -/
def _root_.Solidity.Source.STy.isConstOnly : STy → Bool
  | .rational _ | .hexConst _ _ | .stringLit _ => true
  | _ => false

/-- **The constant-type restriction on ABI arguments**: the standalone type
is not a constant-only type (a fractional constant without a mobile type,
or an integral one beyond 256 bits, has none).  solc's other restrictions
on `abi.encode` arguments (mappings, internal function types, storage
references, tuples) are not part of this relation. -/
def AbiArgTyped (Γ : Ctx) (e : Syn .expr) (τ : STy) : Prop :=
  StandaloneTyped Γ e τ ∧ τ.isConstOnly = false

/-- **The checker**: G13's inferred types, standing alone. -/
def standaloneTys (Γ : Ctx) (e : Syn .expr) : List STy := (inferTys Γ e).map STy.standalone

theorem standalone_iff {Γ : Ctx} {e : Syn .expr} {τ : STy} :
    StandaloneTyped Γ e τ ↔ τ ∈ standaloneTys Γ e := by
  unfold StandaloneTyped standaloneTys
  rw [List.mem_map]
  constructor
  · intro ⟨σ, hσ, he⟩
    exact ⟨σ, hasType_iff.mp hσ, he⟩
  · intro ⟨σ, hσ, he⟩
    exact ⟨σ, hasType_iff.mpr hσ, he⟩

/-- The ABI argument types of `e`. -/
def abiArgTys (Γ : Ctx) (e : Syn .expr) : List STy :=
  (standaloneTys Γ e).filter fun τ => !τ.isConstOnly

theorem abiArg_iff {Γ : Ctx} {e : Syn .expr} {τ : STy} :
    AbiArgTyped Γ e τ ↔ τ ∈ abiArgTys Γ e := by
  unfold AbiArgTyped abiArgTys
  rw [List.mem_filter, standalone_iff]
  simp only [Bool.not_eq_true']

/-- **The value of a standalone fractional constant**: at `.fixed f`, the
reference semantics' `Fx.mobileConst?` gives a value at a type with `f`'s
fields, the constant truncated toward zero there (`Fx.mobileConst?_trunc`).
This unfolds `STy.standalone`; `standalone_toFixedExplicit` relates the
value to S01's. -/
theorem standalone_value {q : Q} {f : FixTy} (h : (STy.rational q).standalone = .fixed f) :
    q.isInt = false ∧ ∃ m : FxTy, m.toFixTy = f ∧ Fx.mobileFx? q.toRat = Option.some m ∧
      ∃ hr, Fx.mobileConst? q.toRat =
        Option.some ⟨m, ⟨Fx.literalTrunc m q.toRat.num q.toRat.den, hr⟩⟩ := by
  have hd : (STy.rational q).standalone = if q.isInt then (STy.rational q).mobile
      else match Fx.mobileFx? q.toRat with
        | Option.some m => .fixed m.toFixTy
        | Option.none => .rational q := rfl
  rw [hd] at h
  cases hi : q.isInt with
  | true =>
    rw [hi, if_pos rfl] at h
    have hm : (STy.rational q).mobile = match q.mobileInt? with
        | Option.some t => .int t
        | Option.none => .rational q := rfl
    rw [hm] at h
    split at h <;> cases h
  | false =>
    rw [hi] at h
    simp only [Bool.false_eq_true, if_false] at h
    refine ⟨rfl, ?_⟩
    split at h
    · rename_i m hm
      exact ⟨m, STy.fixed.inj h, hm, Fx.mobileFx?_inRange hm, Fx.mobileConst?_eq hm⟩
    · exact nomatch h

theorem toFixTy_scale (m : FxTy) : m.toFixTy.scale = m.scale := by
  simp only [FixTy.scale, FxTy.scale, FxTy.toFixTy, Int.natCast_pow]
  rfl

theorem toFixTy_lo (m : FxTy) : m.toFixTy.lo = m.lo := by
  simp only [FixTy.lo, FxTy.lo, FxTy.toFixTy, Int.natCast_pow]
  rfl

theorem toFixTy_hi (m : FxTy) : m.toFixTy.hi = m.hi := by
  have h1 : 1 ≤ 2 ^ (m.bits - 1) := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ m.bits := Nat.one_le_two_pow
  simp only [FixTy.hi, FxTy.hi, FxTy.toFixTy]
  cases m.signed
  · simp only [Bool.false_eq_true, if_false, Int.natCast_sub h2, Int.natCast_pow]
    rfl
  · simp only [if_true, Int.natCast_sub h1, Int.natCast_pow]
    rfl

/-- **S01's explicit value agrees**: at the standalone type, S01's own
explicit conversion of the constant (`Q.toFixedExplicit?`, truncation at
`N` digits) is the reference semantics' standalone value
(`Fx.mobileConst?`), for S01's unreduced rational and its normal form
alike. -/
theorem standalone_toFixedExplicit {q : Q} {m : FxTy} (hm : Fx.mobileFx? q.toRat = Option.some m) :
    q.toFixedExplicit? m.toFixTy = Option.some (Fx.literalTrunc m q.toRat.num q.toRat.den) := by
  have hq : q.den ≠ 0 := Nat.pos_iff_ne_zero.mp q.den_pos
  have he : q.toRat.num * (q.den : Int) = q.num * (q.toRat.den : Int) := by
    have h := Rat.mkRat_self q.toRat
    have h2 : mkRat q.toRat.num q.toRat.den = mkRat q.num q.den := h
    exact (Rat.mkRat_eq_iff q.toRat.den_nz hq).mp h2
  have hc : Fx.literalTrunc m q.toRat.num q.toRat.den = Fx.literalTrunc m q.num q.den :=
    Fx.literalTrunc_congr q.toRat.den_nz hq he
  have hr : m.inRange (Fx.literalTrunc m q.toRat.num q.toRat.den) = true := Fx.mobileFx?_inRange hm
  rw [hc] at hr ⊢
  simp only [FxTy.inRange, Bool.and_eq_true, decide_eq_true_eq] at hr
  unfold Q.toFixedExplicit?
  rw [toFixTy_scale, toFixTy_lo, toFixTy_hi]
  have hv : (q.num * m.scale).tdiv q.den = Fx.literalTrunc m q.num q.den := rfl
  rw [hv]
  simp only [hr, and_self, if_true]

/-- **End to end**: a constant standing alone at `.fixed f` has S01's
explicit value at `f`, and as an ABI argument the word encoding of that
value at the mobile type `m` (`m.toFixTy = f`). -/
theorem standalone_abi {q : Q} {f : FixTy} (h : (STy.rational q).standalone = .fixed f) :
    ∃ m : FxTy, m.toFixTy = f ∧ ∃ hr,
      q.toFixedExplicit? f = Option.some (Fx.literalTrunc m q.toRat.num q.toRat.den) ∧
      Fx.abiConst? q.toRat = Option.some (Fx.abiEncode (⟨Fx.literalTrunc m q.toRat.num q.toRat.den, hr⟩ : Fx m)) := by
  obtain ⟨_, m, hf, hm, _, _⟩ := standalone_value h
  subst hf
  exact ⟨m, rfl, Fx.mobileFx?_inRange hm, standalone_toFixedExplicit hm, Fx.abiConst?_eq hm⟩

end Solidity.Frontend.Static
