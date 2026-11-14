import Solidity.Calculus.LeafDerive

/-!
Premise selection is an untrusted optimization: any selection is sound when
its stronger residual closes. Refusal always returns to the original closer.
Neither a negative candidate result nor failed lowering refutes the input.
-/
namespace Solidity.Automation.Leaf
open Decide
variable {C : Contract}

/-- Reflect a selected residual, retaining the existing closer's bounds. -/
def trimmed (drop : LFml C → Bool) (ψ : Fml C []) : Option Bool :=
  (ψ.toLS true SymS.init).map fun l =>
    l.boundsOk && (l.dropPrem drop).decideLift

theorem trimmed_valid {drop : LFml C → Bool} {ψ : Fml C []}
    (h : trimmed drop ψ = some true) : Fml.Valid ψ := by
  simp only [trimmed, Option.map_eq_some_iff, Bool.and_eq_true] at h
  obtain ⟨l, hl, _, hc⟩ := h
  exact Fml.Valid.of_toLS hl (fun g ν =>
    LFml.dropPrem_holds drop g l ν (LFml.decideLift_valid hc g ν))

/-- Only a successful candidate replaces the verified fallback. -/
def prefer (candidate : Option Bool) (fallback : Unit → Option Bool) : Option Bool :=
  match candidate with
  | some true => some true
  | _ => fallback ()

theorem prefer_accepts {candidate : Option Bool} {fallback : Unit → Option Bool}
    (h : fallback () = some true) : prefer candidate fallback = some true := by
  cases candidate with
  | none => exact h
  | some b => cases b <;> simp only [prefer, h]

theorem prefer_refusal {candidate : Option Bool} {fallback : Unit → Option Bool}
    (h : candidate ≠ some true) : prefer candidate fallback = fallback () := by
  cases candidate with
  | none => rfl
  | some b => cases b <;> simp_all only [prefer, ne_eq, not_true_eq_false]

/-- Generalized trimmed leaf checking, with the original clean-tail path intact. -/
def check (drop : LFml C → Bool) (ψ : Fml C []) : Option Bool :=
  prefer (trimmed drop ψ) (fun _ => Seq.checkCore ψ)

theorem check_accepts {drop : LFml C → Bool} {ψ : Fml C []}
    (h : Seq.checkCore ψ = some true) : check drop ψ = some true :=
  prefer_accepts h

theorem check_valid {drop : LFml C → Bool} {ψ : Fml C []}
    (h : check drop ψ = some true) : Fml.Valid ψ := by
  unfold check prefer at h
  split at h
  · exact trimmed_valid (by assumption)
  · exact Seq.checkCore_valid h

/-- Premise-free conclusions avoid reading irrelevant state histories. -/
def dropAll (_ : LFml C) : Bool := true

/-- The original closed-spec policy, usable without the frontend. -/
def dropTrue (P : LFml C) : Bool :=
  match P with
  | @LFml.eq _ .bool a b => a.isTT && b.isTT
  | _ => false

end Solidity.Automation.Leaf
