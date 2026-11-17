import Solidity.Correctness.Sim.Lang
import Solidity.Source.Session

/-! A small-step presentation of the Source session semantics
(`Solidity.Source.sourceLangEvents`, `sessionAtEvents`) as a
`Solidity.Correctness.Sim.Machine` per program and environment, with run
coverage at every bound and realization of every reachable observation.

The first step chooses the horizon `n` and runs the deployment at it; each
later step issues one environment action (a credit, a request or its end) and
runs its transaction to its first completion within `n`. A state keeps the
history (its session state's events), the session state, the number of
actions issued and the pending frame (horizon, action budget, last outcome);
`observe` is the prefix so far. This mentions neither a lowering nor the
intrinsic session. -/
namespace Solidity.Correctness.Lowering.Sim.Session

open Solidity.Source
open Solidity.Roadmap (Event Outcome SessionEnv Prefix)

variable {E : Solidity.Source.Env}

/-- A session machine state: before deployment, running with a pending frame
(horizon `n`, remaining action budget `k`, actions issued `i`, session state
`s` whose events are the history, last outcome), or ended with its prefix. -/
inductive SourceState (E : Solidity.Source.Env) where
  | start
  | run (n k i : Nat) (s : St E) (last : Outcome)
  | done (p : Prefix Event Outcome)

namespace SourceState

/-- The prefix so far. -/
def observe : SourceState E → Prefix Event Outcome
  | start => ⟨[], none⟩
  | run _ _ _ s _ => ⟨s.events, none⟩
  | done p => p

/-- The prefix the session reaches from this state at its horizon. -/
def result (P : SrcProg E) (env : SessionEnv) : SourceState E → Prefix Event Outcome
  | start => ⟨[], none⟩
  | run n k i s last => sessionGoEvents P env n k i s last
  | done p => p

end SourceState

open SourceState

/-- Deploy at horizon `n`, as `sessionFromEvents` reads the deployment. -/
def deployStep (P : SrcProg E) (env : SessionEnv) (n : Nat) : SourceState E :=
  match firstDone (runAt (deployRun P env (P.fixed.createAddress env.deployer env.deployNonce))
      (St.init E)) n with
  | some (_, (.ok o, s)) => .run n n 0 s o
  | some (_, (.error _, s)) => .done ⟨s.events, none⟩
  | none => .done ⟨(runAt (deployRun P env (P.fixed.createAddress env.deployer env.deployNonce))
      (St.init E) n).2.events, none⟩

/-- Issue action `i` with `k` actions left after it, as one unfolding of
`sessionGoEvents`. -/
def actStep (P : SrcProg E) (env : SessionEnv) (n k i : Nat) (s : St E) (last : Outcome) :
    SourceState E :=
  match env.requests s.events i with
  | none => .done ⟨s.events, some last⟩
  | some (.credit t v) =>
    let s' := (runAt (fun _ => do
      if (← instanceAt (P.glob env) t).isSome then credit t v) s 0).2
    .run n k (i + 1) { s' with events := s.events ++ [.credit t v] } last
  | some (.request q) =>
    if requestFunded P.fixed env.balance s.events q then
      match firstDone (runAt (fun f => runTx (P.glob env) f q) s) n with
      | some (_, (.ok o, s')) =>
        .run n k (i + 1) { s' with events := s.events ++ s'.events.drop s.events.length } o
      | some (_, (.error _, s')) => .done ⟨s'.events, none⟩
      | none => .done ⟨(runAt (fun f => runTx (P.glob env) f q) s n).2.events, none⟩
    else .run n k (i + 1) s last

/-- One machine step: choose a horizon and deploy, or issue the next action. -/
inductive SourceStep (P : SrcProg E) (env : SessionEnv) : SourceState E → SourceState E → Prop
  | deploy (n : Nat) : SourceStep P env .start (deployStep P env n)
  | act (n k i : Nat) (s : St E) (last : Outcome) :
    SourceStep P env (.run n (k + 1) i s last) (actStep P env n k i s last)

/-- The small-step presentation of `(sourceLangEvents E).sem P env`. -/
def sourceMachine (P : SrcProg E) (env : SessionEnv) : Solidity.Correctness.Sim.Machine where
  State := SourceState E
  initial := .start
  step := SourceStep P env
  observe := SourceState.observe

theorem deployStep_result (P : SrcProg E) (env : SessionEnv) (n : Nat) :
    (deployStep P env n).result P env = sessionAtEvents P env n := by
  unfold deployStep sessionAtEvents sessionFromEvents
  split <;> (rename_i h; simp only [h]; rfl)

theorem actStep_result (P : SrcProg E) (env : SessionEnv) (n k i : Nat) (s : St E)
    (last : Outcome) :
    (actStep P env n k i s last).result P env = sessionGoEvents P env n (k + 1) i s last := by
  unfold actStep
  simp only [sessionGoEvents]
  split
  · rename_i h; simp only [h]; rfl
  · rename_i h; simp only [h]; rfl
  · rename_i h; simp only [h]
    split
    · split <;> (rename_i h'; simp only [h']; rfl)
    · rfl

/-- An action keeps the horizon and spends one unit of budget, or ends. -/
theorem actStep_shape (P : SrcProg E) (env : SessionEnv) (n k i : Nat) (s : St E)
    (last : Outcome) :
    (∃ i' s' last', actStep P env n k i s last = .run n k i' s' last') ∨
      ∃ p, actStep P env n k i s last = .done p := by
  unfold actStep
  split
  · exact .inr ⟨_, rfl⟩
  · exact .inl ⟨_, _, _, rfl⟩
  · split
    · split
      · exact .inl ⟨_, _, _, rfl⟩
      · exact .inr ⟨_, rfl⟩
      · exact .inr ⟨_, rfl⟩
    · exact .inl ⟨_, _, _, rfl⟩

/-- From a running state, the remaining actions reach a state observing the
prefix the session reaches. -/
theorem run_reaches (P : SrcProg E) (env : SessionEnv) (n : Nat) :
    ∀ k i (s : St E) last, ∃ t, Solidity.Correctness.Sim.Star (SourceStep P env)
      (.run n k i s last) t ∧ t.observe = sessionGoEvents P env n k i s last
  | 0, _, _, _ => ⟨_, .refl _, rfl⟩
  | k + 1, i, s, last => by
    have edge := SourceStep.act (P := P) (env := env) n k i s last
    rcases actStep_shape P env n k i s last with ⟨i', s', last', h⟩ | ⟨p, h⟩
    · obtain ⟨t, path, obs⟩ := run_reaches P env n k i' s' last'
      refine ⟨t, (Solidity.Correctness.Sim.Star.single (h ▸ edge)).trans path, ?_⟩
      rw [obs, ← actStep_result P env n k i s last, h]; rfl
    · refine ⟨_, Solidity.Correctness.Sim.Star.single (h ▸ edge), ?_⟩
      rw [← actStep_result P env n k i s last, h]; rfl

/-- **Coverage at every bound**: the machine reaches the session's prefix at
bound `r`, for every program, environment and bound (allowed or not). -/
theorem sourceMachine_reaches (P : SrcProg E) (env : SessionEnv) (r : Nat) :
    ∃ s, (sourceMachine P env).Reachable s ∧
      (sourceMachine P env).observe s = (sourceLangEvents E).sem P env r := by
  have edge := SourceStep.deploy (P := P) (env := env) r
  have hres := deployStep_result P env r
  show ∃ s, Solidity.Correctness.Sim.Star (SourceStep P env) .start s ∧ s.observe = _
  rcases hd : deployStep P env r with _ | ⟨n, k, i, s, last⟩ | p <;> rw [hd] at edge hres
  · exact ⟨_, .refl _, hres⟩
  · obtain ⟨t, path, obs⟩ := run_reaches P env n k i s last
    exact ⟨t, (Solidity.Correctness.Sim.Star.single edge).trans path, obs.trans hres⟩
  · exact ⟨_, .single edge, hres⟩

/-- `Covers` for the source behaviour of `P`, whatever selection of bounds. -/
theorem sourceMachine_covers (P : SrcProg E)
    (selected : SessionEnv → Nat → Prop) :
    Solidity.Correctness.Sim.Covers
      (Solidity.Roadmap.G49Final.Behaviour.ofLang (sourceLangEvents E) P)
      (sourceMachine P) selected :=
  fun e r _ _ => sourceMachine_reaches P e r

/-- Every state observes at most the prefix it reaches. -/
theorem observe_le_result (P : SrcProg E) (env : SessionEnv) :
    ∀ s : SourceState E, s.observe.Le (s.result P env)
  | .start => Prefix.Le.refl _
  | .run n k i s last => ⟨sessionGoEvents_extends P env n k i s last, .inl rfl⟩
  | .done _ => Prefix.Le.refl _

/-- Every reachable state past the start reaches the session's prefix at its
chosen bound. -/
theorem reachable_result (P : SrcProg E) (env : SessionEnv) {s : SourceState E}
    (h : (sourceMachine P env).Reachable s) :
    s = .start ∨ ∃ r, s.result P env = sessionAtEvents P env r := by
  induction h with
  | refl => exact .inl rfl
  | tail _ edge ih =>
    cases edge with
    | deploy n => exact .inr ⟨n, deployStep_result P env n⟩
    | act n k i s last =>
      rcases ih with h | ⟨r, hr⟩
      · cases h
      · exact .inr ⟨r, (actStep_result P env n k i s last).trans hr⟩

/-- **Realization**: every reachable state's observation is below the
session's prefix at an admissible bound, which also meets the language's
Forward and Guard. -/
theorem sourceMachine_realized (P : SrcProg E) (env : SessionEnv) {s : SourceState E}
    (h : (sourceMachine P env).Reachable s) :
    ∃ r, (sourceLangEvents E).Admissible r ∧ (sourceLangEvents E).Forward P env r ∧
      (sourceLangEvents E).Guard P env r ∧
      ((sourceMachine P env).observe s).Le ((sourceLangEvents E).sem P env r) := by
  rcases reachable_result P env h with rfl | ⟨r, hr⟩
  · exact ⟨(0 : Nat), trivial, trivial, trivial, List.nil_prefix, .inl rfl⟩
  · refine ⟨r, trivial, trivial, trivial, ?_⟩
    show s.observe.Le (sessionAtEvents P env r)
    rw [← hr]
    exact observe_le_result P env s

end Solidity.Correctness.Lowering.Sim.Session
