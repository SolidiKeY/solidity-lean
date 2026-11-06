import Solidity.Source.FailureRequestAdmission
import Solidity.Source.Horizon

/-! Nonconstant-plan, arbitrary-cursor exact admission equations for the
EXISTING requestValueScope. No new runtime operation or body-outcome oracle. -/
namespace Solidity.Source.FailureExecution
open EM
variable {E : Env} {Γ : RCtx} {α : Type}

theorem request_value_underfunded_at (points : Roadmap.Evm.FailurePoints)
    (request : Roadmap.Request) (body : Nat → EM E Γ α)
    (locals : Locals E.layout Γ) (state : St E)
    (quiet : state.resource.quiescent = true) (balance : Nat) (cut : Option Nat)
    (fate : points.tx state.resource.nextRequest = .runs balance cut)
    (invalid : balance < request.value.val) :
    (requestValueScope points request body).run (locals,state) =
      (.ok none,(locals,{state with resource :=
        (state.resource.enterRequest
          (admitRequestAt points state.resource.nextRequest request.value) quiet).2})) := by
  simp only [requestValueScope, run_bind, run_st, requestScope,
    quiet, dif_pos, Cursor.enterRequest, admitRequestAt, if_true,
    admitRequestFate, fate, if_pos invalid]
  rfl

/-- Admission is a literal unchanged full plan when its current running fate
is affordable. No constant-plan or horizon-zero restriction is required. -/
theorem admission_at_funded (points : Roadmap.Evm.FailurePoints) (index : Nat)
    (request : Roadmap.Request) (balance : Nat) (cut : Option Nat)
    (fate : points.tx index = .runs balance cut) (valid : request.value.val ≤ balance) :
    admitRequestAt points index request.value = points := by
  cases points with
  | mk tx frame =>
    change tx index = .runs balance cut at fate
    dsimp only [admitRequestAt]
    congr 1
    funext i
    by_cases same : i = index
    · subst i
      simp only [if_true, fate, admitRequestFate, if_neg (Nat.not_lt.mpr valid)]
    · simp only [if_neg same]

theorem request_value_admitted_at (points : Roadmap.Evm.FailurePoints)
    (request : Roadmap.Request) (body : Nat → EM E Γ α)
    (locals : Locals E.layout Γ) (state : St E)
    (balance : Nat) (cut : Option Nat)
    (fate : points.tx state.resource.nextRequest = .runs balance cut)
    (valid : request.value.val ≤ balance) :
    (requestValueScope points request body).run (locals,state) =
      (requestScope points body).run (locals,state) := by
  simp only [requestValueScope, run_bind, run_st,
    admission_at_funded points state.resource.nextRequest request balance cut fate valid]

theorem request_value_rejected_counters (points : Roadmap.Evm.FailurePoints)
    (request : Roadmap.Request) (body : Nat → EM E Γ α)
    (locals : Locals E.layout Γ) (state : St E)
    (quiet : state.resource.quiescent = true) (balance : Nat) (cut : Option Nat)
    (fate : points.tx state.resource.nextRequest = .runs balance cut)
    (invalid : balance < request.value.val) :
    let final := ((requestValueScope points request body).run (locals,state)).2.2.resource
    final.nextRequest = state.resource.nextRequest+1 ∧
      (⟨final.nextFrame,final.frames⟩ : Σ count, List (FrameBudget count)) =
        ⟨state.resource.nextFrame,state.resource.frames⟩ := by
  rw [request_value_underfunded_at points request body locals state quiet balance cut fate invalid]
  exact ⟨rfl,rfl⟩

end Solidity.Source.FailureExecution
