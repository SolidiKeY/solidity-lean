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
- `StandaloneTyped`, `AbiArgTyped`: the relations, over S01's `HasType`.
- `standaloneTys`: the checker, over G13's inference; `standalone_iff`,
  `abiArg_iff`: it decides them (by `hasType_iff`).
- `standalone_value`: a fractional constant standing at `.fixed f` has the
  value `Fx.mobileConst?` gives, at a type with `f`'s fields.

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

/-- Whether a type is a constant's own type, which no value has. -/
def _root_.Solidity.Source.STy.isConstTy : STy → Bool
  | .rational _ | .stringLit _ => true
  | _ => false

/-- **ABI argument typing**: a standalone type that values have (a
fractional constant without a mobile type, or an integral one beyond 256
bits, has none). -/
def AbiArgTyped (Γ : Ctx) (e : Syn .expr) (τ : STy) : Prop :=
  StandaloneTyped Γ e τ ∧ τ.isConstTy = false

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
  (standaloneTys Γ e).filter fun τ => !τ.isConstTy

theorem abiArg_iff {Γ : Ctx} {e : Syn .expr} {τ : STy} :
    AbiArgTyped Γ e τ ↔ τ ∈ abiArgTys Γ e := by
  unfold AbiArgTyped abiArgTys
  rw [List.mem_filter, standalone_iff]
  simp only [Bool.not_eq_true']

/-- **The value of a standalone fractional constant**: at `.fixed f`, the
reference semantics' `Fx.mobileConst?` gives a value at a type with `f`'s
fields, the constant truncated toward zero there (`Fx.mobileConst?_trunc`). -/
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

end Solidity.Frontend.Static
