import Solidity.Frontend.Admission.ProgramObservations

/-! Policy facts constrained by actual intrinsic typing. These do not prove
feature extraction, full-profile admission or operational adequacy. -/
namespace Solidity.Frontend.Admission.TypedObservationPolicy
open Source

theorem builtin_allowed : ∀ (B : DeclName → DeclName → Bool) (b : Builtin)
    (ts : List STy) (t : STy), b.callTy B ts = some t →
      (ObservationSite.builtin b).allowed = true := by
  intro B b ts t h
  cases b <;> first | decide | (simp only [Solidity.Source.Builtin.callTy] at h; cases h)

theorem magic_allowed : ∀ (b : Builtin) (m : String) (t : STy),
    b.memberTy m = some t → (ObservationSite.magic b m).allowed = true := by
  intro b m t h
  cases b <;> simp only [Solidity.Source.Builtin.memberTy] at h
  all_goals repeat' split at h
  all_goals first | contradiction | decide

/-- Structural expression-visitor obligation; proved by `expression_allowed`
in `TypedExpressionPolicy.lean`. -/
abbrev ExpressionPolicy : Prop := ∀ {E : Env} {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ),
  (observations e).all ObservationSite.allowed = true

/-- Carried-Program policy proposition, proved in TypedStatementPolicy. It
shows observation guard redundancy, not full feature/profile adequacy. -/
abbrev WholeProgramPolicy : Prop := ∀ {E : Env} (P : Program E),
  (programObservations P).all ObservationSite.allowed = true

/-- info: 'Solidity.Frontend.Admission.TypedObservationPolicy.builtin_allowed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms builtin_allowed
/-- info: 'Solidity.Frontend.Admission.TypedObservationPolicy.magic_allowed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms magic_allowed
end Solidity.Frontend.Admission.TypedObservationPolicy
