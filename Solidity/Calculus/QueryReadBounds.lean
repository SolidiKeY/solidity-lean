import Solidity.Calculus.QueryReduction
import Solidity.Calculus.ReadTrace

/-!
# Source-derived finite occurrence bounds

The arithmetic interface needs a finite prefix of occurrence values.
These bounds come from the existing typed query syntax, not an assumed
number of mapping keys. Branches and partial expressions may select fewer
reads. The bound covers every value choice and every starting index.
-/

namespace Solidity.Decide

open ReadRealization

variable {C : Contract}

def ReadExpr.readBound : {s : Srt} → {t : LTm C s} → ReadExpr t → Nat
  | _, _, .var _ | _, _, .lit _ | _, _, .env _ | _, _, .root _ _ | _, _, .err | _, _, .zlit _ => 0
  | _, _, .field _ q | _, _, .unop _ _ q | _, _, .toInt q | _, _, .net q => q.readBound
  | _, _, .index q k | _, _, .binop _ _ q k | _, _, .seq q k | _, _, .orElse q k
  | _, _, .zbin _ _ q k | _, _, .zcmp _ _ q k =>
    q.readBound + k.readBound
  | _, _, .word q => q.readBound + 1
  | _, _, .kite a b t e => a.readBound + (b.readBound + (t.readBound + e.readBound))

/-- Every query generated from a supported term fits its structural bound. -/
theorem ReadExpr.query_within (g : State C []) (ν : AEnv) {s : Srt} {t : LTm C s}
    (h : ReadExpr t) : (h.query g ν).Within h.readBound := by
  induction h with
  | var _ | lit _ | env _ | root _ _ | err | zlit _ => exact Query.within_pure _ 0
  | field _ _ ih | unop _ _ _ ih | toInt _ ih | net _ ih =>
    exact Query.within_bind _ _ ih (fun _ => Query.within_pure _ 0)
  | index _ _ ihq ihk | binop _ _ _ _ ihq ihk | zbin _ _ _ _ ihq ihk | zcmp _ _ _ _ ihq ihk =>
    exact Query.within_bind _ _ ihq (fun _ => Query.within_bind _ _ ihk
      (fun _ => Query.within_pure _ 0))
  | word _ ih =>
    apply Query.within_bind _ _ ih
    intro q
    cases q with
    | none => exact Query.within_pure _ 1
    | some r => exact Query.within_read _ _ 0 (fun _ => Query.within_pure _ 0)
  | seq hd ha ihd iha =>
    apply Query.within_bind _ _ ihd
    intro d
    cases d with
    | none => exact Query.within_pure _ ha.readBound
    | some _ => exact iha
  | orElse ha hb iha ihb =>
    apply Query.within_bind _ _ iha
    intro a
    cases a with
    | none => exact ihb
    | some _ => exact Query.within_pure _ hb.readBound
  | kite ha hb ht he iha ihb iht ihe =>
    apply Query.within_bind _ _ iha
    intro a
    apply Query.within_bind _ _ ihb
    intro b
    cases a <;> cases b
    all_goals first | exact Query.within_pure _ _ | skip
    dsimp only
    split
    · exact Query.within_mono iht (by omega)
    · exact Query.within_mono ihe (by omega)

def ReadFormula.readBound : {φ : LFml C} → ReadFormula φ → Nat
  | _, .tt => 0
  | _, .eq a b => a.readBound + b.readBound
  | _, .not φ => φ.readBound
  | _, .and φ ψ | _, .imp φ ψ => φ.readBound + ψ.readBound

theorem ReadFormula.query_within (g : State C []) (ν : AEnv) {φ : LFml C}
    (h : ReadFormula φ) : (h.query g ν).Within h.readBound := by
  induction h with
  | tt => exact Query.within_pure _ 0
  | eq a b => exact Query.within_bind _ _ (a.query_within g ν) (fun _ =>
      Query.within_bind _ _ (b.query_within g ν) (fun _ => Query.within_pure _ 0))
  | not φ ih => exact Query.within_bind _ _ ih (fun _ => Query.within_pure _ 0)
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ =>
    exact Query.within_bind _ _ ihφ (fun _ => Query.within_bind _ _ ihψ
      (fun _ => Query.within_pure _ 0))

def ReadSentence.readBound : {φ : LFml C} → ReadSentence φ → Nat
  | _, .body φ => φ.readBound
  | _, .all _ _ φ => φ.readBound

theorem ReadSentence.query_within (g : State C []) {φ : LFml C}
    (h : ReadSentence φ) (ν : AEnv) (args : List Semantics.CallValue) :
    (h.query g ν args).Within h.readBound := by
  induction h generalizing ν args with
  | body φ => exact φ.query_within g ν
  | all k p φ ih => exact ih _ _

end Solidity.Decide
