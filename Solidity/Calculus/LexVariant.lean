import Solidity.Calculus.Lower

/-!
# Typed snapshots for lexicographic loop variants

The pure constructors in this module can be used below the rule table.
Snapshots evaluate every component as a parallel update, including components
after an already decreasing one. Comparisons read only captured uint locals.
The semantic agreement lemmas live in `LexVariantSound` to avoid a rule-table
import cycle. These helpers alone make no claim of strict loop termination.
-/
namespace Solidity.LoopLex

variable {C : Contract} {Γ Δ : Ctx}

/-- A prefix of fresh uint locals, with its arity retained in the context. -/
def SavedCtx : Nat → Ctx → Ctx
  | 0, Γ => Γ
  | n + 1, Γ => .val .uint :: SavedCtx n Γ

def savedExt (Γ : Ctx) : (n : Nat) → Ext Γ (SavedCtx n Γ)
  | 0 => .refl
  | n + 1 => .push (savedExt Γ n)

/-- All right-hand sides read the original state; the first metric is the
innermost local after the update. No bounded-word tuple packing is used. -/
def snapshot (k : Nat) : {n : Nat} → LoopMetrics C Γ n → Upd C Γ (SavedCtx n Γ)
  | 0, .nil => .nil
  | _ + 1, .cons head tail =>
      (snapshot (k + 1) tail).decl (.fresh "variant" k) (.val head.lower)

/-- Typed references to captured metrics, in source order. -/
inductive Refs (Γ : Ctx) : Nat → Type where
  | nil : Refs Γ 0
  | cons {n : Nat} (head : Idx Γ (.val .uint)) (tail : Refs Γ n) : Refs Γ (n + 1)

def Refs.wk (h : Thin Γ Δ) : {n : Nat} → Refs Γ n → Refs Δ n
  | 0, .nil => .nil
  | _ + 1, .cons head tail => .cons (head.wk h) (tail.wk h)

def freshRefs (Γ : Ctx) : (n : Nat) → Refs (SavedCtx n Γ) n
  | 0 => .nil
  | n + 1 => .cons .here ((freshRefs Γ n).wk (.drop .refl))

/-- A comparison is strict lexicographic order over the captured values.
Only locals occur here: definedness is checked by the preceding snapshots. -/
def lexFml : {n : Nat} → Refs Γ n → Refs Γ n → Fml C Γ
  | 0, .nil, .nil => .not .tt
  | _ + 1, .cons a as, .cons b bs =>
      .not (.and
        (.not (.eq (.app2 (.binop .lt rfl) (.pvV a) (.pvV b)) (.app0 (.lit true))))
        (.not (.and (.eq (.pvV a) (.pvV b)) (lexFml as bs))))

/-- Compare a new snapshot with an equally sized old one beneath it. -/
def snapshotsDecrease (n : Nat) : Fml C (SavedCtx n (SavedCtx n Γ)) :=
  lexFml (freshRefs (SavedCtx n Γ) n)
    ((freshRefs Γ n).wk (.ofExt (savedExt (SavedCtx n Γ) n)))

end Solidity.LoopLex
