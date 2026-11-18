import Solidity.Correctness.Lowering.Sim.Session.Forward.Frames
import Solidity.Correctness.Lowering.Sim.Session.Forward.Within
import Solidity.Correctness.Lowering.Sim.Match

/-! # The forward session diagram

From matched frames (`MatchedFrames`, `Forward/Frames.lean`) in every environment:

* `forward`: a `Sim.Diagram` from the Source session machine at `envAbs e` to
  the intrinsic session machine of the lowered world, with `MatchedFrames.Matches` as
  its `matchState`. A Source frame that does not complete is a stutter.
* The languages are `sourceLang` and `targetLang` of `Session/Backward.lean`,
  whose `Behaviour.ofLang` are `Shrink.Lowering.sourceBehaviour` and
  `targetBehaviour` by `rfl`, and the target machine is its `targetMachine` at
  the lowered world, so the record below pairs with `backwardResources` in
  `Sim.lang_passCorrect`.
* `forwardResources`: the `Sim.ForwardResources` record. Its transport is
  `Shrink.Lowering.transport D` (the horizon `D.fuel n`, no resource failure);
  `ready` reads the target's `Forward` (no resource failure, the hash bound)
  and `Guard` off the Source behaviour's `Forward`; `bound` needs
  `n < D.fuel n`, which `Sim.diagram` meets (`forwardResources_diagram`).

## What is not proved

`MatchedFrames` is a hypothesis. It is not derived from `Sim.diagram.Simulates` and
`Sim.diagram.Total` here, and with the frozen statements it cannot be:

* an entry of the lowered code is `topBlock` of a call statement, which runs
  the `partial` elaborator `elabStmtsP`; the kernel sees an opaque constant,
  and `Shrink.Lowering.Compilation` carries no `ElaborationReceipt` for it, so
  no `Production` run is known to be the body an entry frame executes;
* the Source session deploys at `P.fixed.createAddress` and reads
  `P.fixed.ledger`, the target at `F.createAddress` and `F.ledger`, and
  `Shrink.Lowering.SessionLift` quantifies `F` independently of `P`;
* a funded request to an address without an instance shows `revert []` in the
  Source session (`Source.runTx`) and `success []` in the intrinsic session
  (`IntrinsicSession.request`), in every environment that issues one.

The last makes `MatchedFrames D F P c e` unsatisfiable for such an `e` once the
Source deployment completes there (read off the two semantics, not proved
here). So for a program whose deployment completes in some environment, the
family `∀ e, MatchedFrames D F P c e` that `forwardResources` takes has no
inhabitant as the two session semantics stand: `forwardResources`,
`forwardResources_diagram` and `MatchedFrames.session_le` are then vacuous.
They fix the shape of the forward half (types, transport, horizon bound) and
are no evidence that any program refines. `forward` at one environment is not
affected by other environments.

Follow-up: `go_within` (`Forward/Within.lean`) repeats `go_realized`
(`Session/Target.lean`) with one more conjunct; `go_realized` should become
its corollary there. -/
namespace Solidity.Correctness.Lowering.Sim.Session

open Solidity.Roadmap (Event Outcome SessionEnv Fixed Prefix Lang)
open Solidity.Roadmap.G49Final (Behaviour)
open Solidity.Correctness.Sim (Star Diagram ForwardResources)
open Solidity.Semantics.IntrinsicSession (wire lastOutcome spec runOf)
open Solidity.Goals.Shrink.Lowering (Compilation loweredCode loweredWorld envAbs transport
  sourceBehaviour targetBehaviour)

variable [FreshNames] {E : Solidity.Source.Env} {D : Solidity.Goals.Shrink.Lowering.Diagram}
  {F : Fixed} {P : Solidity.Source.SrcProg E} {c : Compilation} {e : SessionEnv}

/-- The deployment is matched, and issues no action. -/
theorem MatchedFrames.deploy_matched (fr : MatchedFrames D F P c e) (n : Nat) :
    ∃ t, Star (targetMachine F (loweredWorld c) e).step (targetMachine F (loweredWorld c) e).initial t ∧
      fr.Matches (deployStep P e n) t ∧ t.issued = 0 := by
  have d := fr.deploy n
  cases hs : deployStep P e n with
  | start => exact ⟨_, .refl _, rfl, rfl⟩
  | done p =>
    rw [hs] at d
    subst d
    exact ⟨_, .refl _, rfl, rfl⟩
  | run n' k i s o =>
    rw [hs] at d
    obtain ⟨stops, events, inv, last⟩ := d
    obtain ⟨-, -, rfl⟩ := deployStep_run hs
    refine ⟨⟨(targetDeploy F c e).events, (targetDeploy F c e).world, 0, .action⟩, .single ?_,
      ⟨events, rfl, rfl, inv, last⟩, rfl⟩
    show next (loweredCode c).main (loweredCode c).roles (loweredCode c).ctor (loweredCode c).entry
      F wire _ e (State.start (loweredCode c).roles e .fresh) = _
    simp only [State.start, next, stops, Bool.false_eq_true, if_false]

/-- An action from a matched boundary is matched, issuing at most one action. -/
theorem MatchedFrames.act_matched (fr : MatchedFrames D F P c e) (n k i : Nat) (s : Solidity.Source.St E)
    (last : Outcome) (t : State (loweredCode c).contracts) (m : fr.Matches (.run n (k + 1) i s last) t) :
    ∃ t', Star (targetMachine F (loweredWorld c) e).step t t' ∧ fr.Matches (actStep P e n k i s last) t' ∧
      t'.issued ≤ i + 1 := by
  obtain ⟨h, w, j, pend⟩ := t
  obtain ⟨rfl, rfl, rfl, inv, hlast⟩ := m
  cases req : e.requests s.events j with
  | none =>
    refine ⟨⟨s.events, w, j, .idle⟩, .single ?_, ?_, Nat.le_succ _⟩
    · show next (loweredCode c).main (loweredCode c).roles (loweredCode c).ctor (loweredCode c).entry F wire _ e _ = _
      simp only [next, req]
    · have hs : actStep P e n k j s last = .done ⟨s.events, some last⟩ := by
        simp only [actStep, req]
      rw [hs]
      show State.observe _ = _
      simp only [State.observe, if_true, hlast]
  | some a =>
    have d := fr.act n k j s last w a inv hlast req
    cases hs : actStep P e n k j s last with
    | start => rcases actStep_shape P e n k j s last with ⟨_, _, _, h⟩ | ⟨_, h⟩ <;> rw [hs] at h <;> cases h
    | done p =>
      rw [hs] at d
      subst d
      exact ⟨_, .refl _, rfl, Nat.le_succ _⟩
    | run n' k' i' s' last' =>
      rw [hs] at d
      obtain ⟨stops, events, inv', last'⟩ := d
      obtain ⟨-, -, rfl⟩ := actStep_run hs
      refine ⟨⟨s.events ++ (targetStep F c e s.events j w a).events,
        (targetStep F c e s.events j w a).world, j + 1, .action⟩, .single ?_,
        ⟨events.symm, rfl, rfl, inv', last'⟩, Nat.le_refl _⟩
      show next (loweredCode c).main (loweredCode c).roles (loweredCode c).ctor (loweredCode c).entry F wire _ e _ = _
      simp only [next, req, stops, Bool.false_eq_true, if_false]

/-- **The forward session diagram** from matched frames. -/
noncomputable def forward (fr : MatchedFrames D F P c e) :
    Diagram (sourceMachine P (envAbs e)) (targetMachine F (loweredWorld c) e) where
  matchState := fr.Matches
  initial := rfl
  step s s' t edge m := by
    cases edge with
    | deploy n =>
      cases m
      obtain ⟨t', path, m', -⟩ := fr.deploy_matched n
      exact ⟨t', path, m'⟩
    | act n k i s last =>
      obtain ⟨t', path, m', -⟩ := fr.act_matched n k i s last t m
      exact ⟨t', path, m'⟩
  events s t m := by
    show (SourceState.observe s).events <+: (State.observe t).events
    rw [m.observe]
    exact List.prefix_refl _
  final s t _ m _ := m.observe

/-- From a matched boundary, the remaining actions reach matched states that
observe the session's prefix, within the action budget. -/
theorem MatchedFrames.go_matched (fr : MatchedFrames D F P c e) (n : Nat) :
    ∀ k i (s : Solidity.Source.St E) last (t : State (loweredCode c).contracts),
      fr.Matches (.run n k i s last) t →
      ∃ s' t', Star (targetMachine F (loweredWorld c) e).step t t' ∧ fr.Matches s' t' ∧
        s'.observe = Solidity.Source.sessionGoEvents P e n k i s last ∧ t'.issued ≤ i + k
  | 0, i, s, last, t, m => ⟨_, t, .refl _, m, rfl, Nat.le_of_eq m.2.1⟩
  | k + 1, i, s, last, t, m => by
    obtain ⟨t₁, path₁, m₁, small₁⟩ := fr.act_matched n k i s last t m
    have res := actStep_result P e n k i s last
    rcases actStep_shape P e n k i s last with ⟨i', s', last', h⟩ | ⟨p, h⟩ <;> rw [h] at m₁ res
    · obtain ⟨-, -, rfl⟩ := actStep_run h
      obtain ⟨s₂, t₂, path₂, m₂, obs, small₂⟩ := fr.go_matched n k (i + 1) s' last' t₁ m₁
      exact ⟨s₂, t₂, path₁.trans path₂, m₂, obs.trans res, by omega⟩
    · exact ⟨_, t₁, path₁, m₁, res, by omega⟩

/-- **The session at horizon `n` is matched within it**: a matched reachable
target state observes the Source prefix at `n` having issued at most `n` actions. -/
theorem MatchedFrames.session_matched (fr : MatchedFrames D F P c e) (n : Nat) :
    ∃ t, (targetMachine F (loweredWorld c) e).Reachable t ∧ t.observe = Solidity.Source.sessionAtEvents P e n ∧
      t.issued ≤ n := by
  obtain ⟨t₁, path₁, m₁, zero⟩ := fr.deploy_matched n
  have res := deployStep_result P e n
  cases hs : deployStep P e n with
  | start => rw [hs] at m₁ res; exact ⟨t₁, path₁, m₁.observe.trans res, by omega⟩
  | done p => rw [hs] at m₁ res; exact ⟨t₁, path₁, m₁.observe.trans res, by omega⟩
  | run n' k i s o =>
    rw [hs] at m₁ res
    obtain ⟨rfl, rfl, rfl⟩ := deployStep_run hs
    obtain ⟨s₂, t₂, path₂, m₂, obs, small⟩ := fr.go_matched _ _ 0 s o t₁ m₁
    exact ⟨t₂, path₁.trans path₂, m₂.observe.trans (obs.trans res), by omega⟩

/-! ## The languages and the resource record -/

/-- **Forward at the transported bound**: the Source session at horizon `n` is
below the lowered run at horizon `D.fuel n`. -/
theorem MatchedFrames.session_le (fr : MatchedFrames D F P c e) (grows : ∀ n, n < D.fuel n) (n : Nat) :
    (Solidity.Source.sessionAtEvents P e n).Le (runOf F (loweredWorld c) e (transport D n)).pfx := by
  obtain ⟨t, reach, obs, small⟩ := fr.session_matched n
  rw [← obs]
  exact within_fresh (m := D.fuel n) reach (Nat.lt_of_le_of_lt small (grows n))

/-- **The forward resource record**, of the type `Sim.lang_passCorrect`
consumes: coverage is the Source machine's, readiness is the target's read off
the Source `Forward`, and matched states stay below the transported run.
A template, not evidence: `fr` has no inhabitant for a program whose
deployment completes in some environment (module comment, "What is not
proved"). -/
noncomputable def forwardResources (fr : ∀ e, MatchedFrames D F P c e) (grows : ∀ n, n < D.fuel n) :
    ForwardResources (Behaviour.ofLang (sourceLang D F E (loweredWorld c)) P)
      (Behaviour.ofLang (targetLang F) (loweredWorld c)) (sourceMachine P) (targetMachine F (loweredWorld c))
      envAbs (fun e => forward (fr e)) where
  need _ n := transport D n
  coverage := fun e r _ _ => sourceMachine_reaches P e r
  ready _ _ _ ready := ⟨ready.2.1.2.1.1, ready.2.1.2.1, ready.2.1.2.2⟩
  bound e r s t _ _ _ observes _ m := by
    have same : t.observe = Solidity.Source.sessionAtEvents P e r :=
      (MatchedFrames.Matches.observe m).trans observes
    show (State.observe t).Le _
    rw [same]
    exact (fr e).session_le grows r

/-- The record for the lowering diagram, whose transport `2 * n + 2` grows.
As vacuous as `forwardResources` while `fr` cannot be met. -/
noncomputable def forwardResources_diagram (fr : ∀ e, MatchedFrames diagram F P c e) :=
  forwardResources fr fun n => by show n < 2 * n + 2; omega

end Solidity.Correctness.Lowering.Sim.Session
