import Solidity.Correctness.Lowering.Total.ArgumentInference.Scalar
import Solidity.Correctness.Lowering.Total.Decode.Tables
import Solidity.Correctness.Lowering.Total.CalleeInference.Args

/-!
# The decoder's spelling of scalar arguments

The unchanged expression spelling of every decoder version (`Decode.Tables.expr`,
`Decode.Tables.exprs`) lands raw scalar arguments in the families of
`ArgumentInference.Scalar`. `RawBool` and `RawScalar` are the raw shapes:
`.num n`, `.bool b`, a `.name x` resolving to a local slot (with its slot type),
and `.unop .not`, `.binop .and/.or/.eqB/.neB` and `.ternary` over Boolean ones,
nested arbitrarily. Their spelling succeeds and is a `BoolArg`/`ScalarArg`
(`RawBool.expr`, `RawScalar.expr`); an ordered raw list spells to an argument
list whose positions are `ScalarArgs` with the same types in the same order
(`RawScalars.exprs`); and a raw call is spelled `f(args)` (`expr_call`). The
environment table is never consulted. Other raw constructs (arithmetic, fields,
indices, nested calls) are not covered.
-/
namespace Solidity.Correctness.Lowering.Total.ArgumentInference

open Decode CalleeInference
open Source (STy Syn NumLit)

variable {Γ : Source.Ctx} (T : Tables)

/-- Raw Boolean arguments over Boolean locals, nested arbitrarily. -/
inductive RawBool (Γ : Source.Ctx) : RawExpr → Prop
  | bool (b : Bool) : RawBool Γ (.bool b)
  | name {x : String} {i : Nat} : Γ.resolve x = some (.loc i) → Γ.tys[i]? = some .bool →
      RawBool Γ (.name x)
  | not {a : RawExpr} : RawBool Γ a → RawBool Γ (.unop .not a)
  | and {a b : RawExpr} : RawBool Γ a → RawBool Γ b → RawBool Γ (.binop .and a b)
  | or {a b : RawExpr} : RawBool Γ a → RawBool Γ b → RawBool Γ (.binop .or a b)
  | eqB {a b : RawExpr} : RawBool Γ a → RawBool Γ b → RawBool Γ (.binop .eqB a b)
  | neB {a b : RawExpr} : RawBool Γ a → RawBool Γ b → RawBool Γ (.binop .neB a b)
  | ternary {c a b : RawExpr} : RawBool Γ c → RawBool Γ a → RawBool Γ b →
      RawBool Γ (.ternary c a b)

/-- Raw scalar arguments with the type their spelling infers to: a number at its
decimal constant, a local at its slot type, a Boolean argument at `bool`. -/
inductive RawScalar (Γ : Source.Ctx) : RawExpr → STy → Prop
  | num (n : Nat) : RawScalar Γ (.num n) (.rational (NumLit.dec n 0 0).value)
  | name {x : String} {i : Nat} {τ : STy} : Γ.resolve x = some (.loc i) → Γ.tys[i]? = some τ →
      RawScalar Γ (.name x) τ
  | bool {r : RawExpr} : RawBool Γ r → RawScalar Γ r .bool

/-- Ordered raw scalar arguments with their types. -/
inductive RawScalars (Γ : Source.Ctx) : List RawExpr → List STy → Prop
  | nil : RawScalars Γ [] []
  | cons {r : RawExpr} {σ : STy} {rs : List RawExpr} {σs : List STy} :
      RawScalar Γ r σ → RawScalars Γ rs σs → RawScalars Γ (r :: rs) (σ :: σs)

variable {T}

/-- A raw Boolean argument spells to a Boolean argument. -/
theorem RawBool.expr {r : RawExpr} (h : RawBool Γ r) : ∃ e, T.expr r = some e ∧ BoolArg Γ e := by
  induction h with
  | bool b => exact ⟨_, by simp [Tables.expr], .lit b⟩
  | name hr ht => exact ⟨_, by simp [Tables.expr], .loc hr ht⟩
  | not _ ih =>
    obtain ⟨e, he, hb⟩ := ih
    exact ⟨_, by simp [Tables.expr, he], .not hb⟩
  | and _ _ iha ihb =>
    obtain ⟨a, ha, hA⟩ := iha; obtain ⟨b, hb, hB⟩ := ihb
    exact ⟨_, by simp [Tables.expr, binop, ha, hb], .and hA hB⟩
  | or _ _ iha ihb =>
    obtain ⟨a, ha, hA⟩ := iha; obtain ⟨b, hb, hB⟩ := ihb
    exact ⟨_, by simp [Tables.expr, binop, ha, hb], .or hA hB⟩
  | eqB _ _ iha ihb =>
    obtain ⟨a, ha, hA⟩ := iha; obtain ⟨b, hb, hB⟩ := ihb
    exact ⟨_, by simp [Tables.expr, binop, ha, hb], .eq .eq hA hB⟩
  | neB _ _ iha ihb =>
    obtain ⟨a, ha, hA⟩ := iha; obtain ⟨b, hb, hB⟩ := ihb
    exact ⟨_, by simp [Tables.expr, binop, ha, hb], .eq .ne hA hB⟩
  | ternary _ _ _ ihc iha ihb =>
    obtain ⟨c, hc, hC⟩ := ihc; obtain ⟨a, ha, hA⟩ := iha; obtain ⟨b, hb, hB⟩ := ihb
    exact ⟨_, by simp [Tables.expr, hc, ha, hb], .cond hC hA hB⟩

/-- A raw scalar argument spells to a scalar argument of the same type. -/
theorem RawScalar.expr {r : RawExpr} {τ : STy} (h : RawScalar Γ r τ) :
    ∃ e, T.expr r = some e ∧ ScalarArg Γ e τ := by
  cases h with
  | num n => exact ⟨_, by simp [Tables.expr, Decode.num], .num n 0 0⟩
  | name hr ht => exact ⟨_, by simp [Tables.expr], .loc hr ht⟩
  | bool hb => obtain ⟨e, he, hB⟩ := hb.expr (T := T); exact ⟨e, he, .bool hB⟩

/-- **An ordered raw list** spells to an argument list whose positions are the
spelled arguments, with the same types in the same order. -/
theorem RawScalars.exprs {rs : List RawExpr} {σs : List STy} (h : RawScalars Γ rs σs) :
    ∃ args, T.exprs rs = some args ∧ ScalarArgs Γ (argExprs args) σs := by
  induction h with
  | nil => exact ⟨.nil, by simp [Tables.exprs], by simp [argExprs]; exact .nil⟩
  | cons hr _ ih =>
    obtain ⟨e, he, hE⟩ := hr.expr (T := T); obtain ⟨args, ha, hA⟩ := ih
    exact ⟨.cons e args, by simp [Tables.exprs, he, ha], by simp [argExprs]; exact .cons hE hA⟩

/-- A raw call is spelled `f(args)` over the spelled arguments. -/
theorem expr_call {f : String} {rs : List RawExpr} {args : Syn (.list .expr)}
    (h : T.exprs rs = some args) : T.expr (.call f rs) = some (.call (.ident f) (.positional args)) := by
  simp [Tables.expr, h]

end Solidity.Correctness.Lowering.Total.ArgumentInference
