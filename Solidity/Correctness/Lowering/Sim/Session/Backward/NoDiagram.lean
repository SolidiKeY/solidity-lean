import Solidity.Correctness.Lowering.Sim.Session.Backward

/-! No reverse diagram into the Source session machine, for a session whose
deployment completes: why `Backward.lean` takes the reverse diagram family as
a hypothesis.

`sourceMachine` chooses its horizon at its first step and spends one unit of
action budget per later step, so past the start it reaches finitely many
states and its history is bounded (`past_start_bounded`). A
`Sim.Diagram T (sourceMachine P env)` matches every step of `T` from one
matched source state on, with `T`'s history a prefix of the source's. So no
such diagram exists for a machine `T` whose every reachable state steps to a
longer history (`no_reverse_diagram`); this reads neither the lowering nor a
relation between the two sides.

The frozen target machine is such a `T` in an environment that issues a credit
at every boundary, provided the deployment's frame completes there
(`target_grows`, `no_reverse_diagram_credits`). So for every Source program
and every session start whose deployment completes in such an environment, the
premise `∀ e, Diagram (T e) (S (envAbs e))` of `Sim.lang_passCorrect` is false
for the two frozen session machines. Nothing is shown for a start whose
deployment stops the session in every environment (a frame that exhausts or
diverges): its target machine rests at an empty history. -/
namespace Solidity.Correctness.Lowering.Sim.Session

open Solidity.Roadmap (Event Outcome SessionEnv Fixed Bytes Action)
open Solidity.Semantics.IntrinsicSession
open Solidity.ContractWorld (World Entry Role)
open Solidity.Correctness.Sim (Machine Star star_simulation)

section Source

variable {E : Source.Env} (P : Source.SrcProg E) (env : SessionEnv)

/-- An ended source state has no successor. -/
theorem done_stuck {p : Solidity.Roadmap.Prefix Event Outcome} {s' : SourceState E}
    (path : Path (SourceStep P env) (.done p) s') : s' = .done p :=
  path.stuck fun _ edge => by cases edge

/-- From a running state the source machine's history is bounded. -/
theorem run_bounded (n : Nat) : ∀ k i (s : Source.St E) last, ∃ L, ∀ s',
    Path (SourceStep P env) (.run n k i s last) s' → s'.observe.events.length ≤ L
  | 0, _, s, _ => ⟨s.events.length, fun s' path => by
      rw [path.stuck fun _ edge => by cases edge]; exact Nat.le_refl _⟩
  | k + 1, i, s, last => by
    rcases actStep_shape P env n k i s last with ⟨i', s₁, last', h⟩ | ⟨p, h⟩
    · obtain ⟨L, bound⟩ := run_bounded n k i' s₁ last'
      refine ⟨max s.events.length L, fun s' path => ?_⟩
      cases path with
      | refl => exact Nat.le_max_left _ _
      | head edge rest =>
        cases edge
        rw [h] at rest
        exact Nat.le_trans (bound _ rest) (Nat.le_max_right _ _)
    · refine ⟨max s.events.length p.events.length, fun s' path => ?_⟩
      cases path with
      | refl => exact Nat.le_max_left _ _
      | head edge rest =>
        cases edge
        rw [h] at rest
        rw [done_stuck P env rest]
        exact Nat.le_max_right _ _

/-- **Past its start the source machine's history is bounded**: the horizon
and the action budget are fixed by the first step. -/
theorem past_start_bounded {s : SourceState E} (past : s ≠ .start) :
    ∃ L, ∀ s', Star (SourceStep P env) s s' → s'.observe.events.length ≤ L := by
  cases s with
  | start => exact absurd rfl past
  | run n k i s last =>
    obtain ⟨L, bound⟩ := run_bounded P env n k i s last
    exact ⟨L, fun s' path => bound s' (Path.ofStar path)⟩
  | done p =>
    exact ⟨p.events.length, fun s' path => by
      rw [done_stuck P env (Path.ofStar path)]; exact Nat.le_refl _⟩

/-- **No reverse diagram** from a machine whose every reachable state steps to
a longer history into the Source session machine. -/
theorem no_reverse_diagram {T : Machine}
    (grows : ∀ t, T.Reachable t →
      ∃ t', T.step t t' ∧ (T.observe t).events.length < (T.observe t').events.length)
    (D : Solidity.Correctness.Sim.Diagram T (sourceMachine P env)) : False := by
  obtain ⟨t₁, edge, longer⟩ := grows T.initial (.refl _)
  obtain ⟨s₁, _, matched⟩ := D.step _ _ _ edge D.initial
  have past : s₁ ≠ .start := by
    rintro rfl
    have := (D.events _ _ matched).length_le
    exact Nat.not_lt_zero _ (Nat.lt_of_lt_of_le longer this)
  obtain ⟨L, bound⟩ := past_start_bounded P env past
  have far : ∀ m t, T.Reachable t → ∃ t', Star T.step t t' ∧ m ≤ (T.observe t').events.length := by
    intro m
    induction m with
    | zero => exact fun t _ => ⟨t, .refl t, Nat.zero_le _⟩
    | succ m ih =>
      intro t reach
      obtain ⟨t', path, le⟩ := ih t reach
      obtain ⟨t'', edge, lt⟩ := grows t' (Star.trans reach path)
      exact ⟨t'', .tail path edge, Nat.lt_of_le_of_lt le lt⟩
  obtain ⟨t, path, le⟩ := far (L + 1) t₁ (.single edge)
  obtain ⟨s, run, related⟩ := star_simulation D.matchState D.step path matched
  exact Nat.not_succ_le_self L
    (Nat.le_trans le (Nat.le_trans (D.events _ _ related).length_le (bound s run)))

end Source

section Target

variable {contracts : List Contract} {main : Nat} {roles : Fin contracts.length → Role}
  {ctor : (k : Fin contracts.length) → Bytes → Option (Prog contracts[k] [] [])}
  {entry : (k : Fin contracts.length) → Bytes → Option (Entry contracts[k] Bytes)}
  {F : Fixed} {wire : Wire} {r : Bound} {e : SessionEnv}

/-- A deployment that completes shows its one event. -/
theorem deploy_events (completes : (deploy main roles ctor F wire r e).stops = false) :
    (deploy main roles ctor F wire r e).events.length = 1 := by
  revert completes
  unfold deploy
  dsimp only
  repeat' split
  all_goals first | (intro; rfl) | (intro h; cases h)

/-- **The session machine never rests** in an environment that issues a credit
at every boundary, once its deployment completes: every reachable state steps
to a longer history. -/
theorem target_grows (w : SessionWorld contracts)
    (deploys : (deploy main roles ctor F wire { horizon := 0 } e).stops = false)
    (credits : ∀ h n, ∃ t v, e.requests h n = some (.credit t v)) :
    ∀ t, (machine₀ main roles ctor entry F wire w e).Reachable t →
      ∃ t', (machine₀ main roles ctor entry F wire w e).step t t' ∧
        ((machine₀ main roles ctor entry F wire w e).observe t).events.length <
          ((machine₀ main roles ctor entry F wire w e).observe t').events.length := by
  have active : ∀ t, (machine₀ main roles ctor entry F wire w e).Reachable t →
      t.pending = .action ∨ (t.pending = .deploy ∧ t.history = []) := by
    intro t reach
    induction reach with
    | refl => cases w <;> simp [machine, State.start]
    | @tail s t _ edge ih =>
      rcases s with ⟨h, v, n, pend⟩
      rcases ih with act | ⟨dep, _⟩
      · cases act
        obtain ⟨a, x, next_a⟩ := credits h n
        simp only [machine, next, next_a, step, credit, Bool.false_eq_true, if_false,
          Option.some.injEq] at edge
        subst edge
        exact .inl rfl
      · cases dep
        simp only [machine, next, deploys, Bool.false_eq_true, if_false, Option.some.injEq] at edge
        subst edge
        exact .inl rfl
  intro t reach
  rcases t with ⟨h, v, n, pend⟩
  rcases active _ reach with act | ⟨dep, empty⟩
  · cases act
    obtain ⟨a, x, next_a⟩ := credits h n
    refine ⟨⟨h ++ [.credit a x], (credit v a x).world, n + 1, .action⟩, ?_, ?_⟩
    · simp only [machine, next, next_a, step, credit, Bool.false_eq_true, if_false]
    · simp [machine, State.observe]
  · cases dep
    cases empty
    refine ⟨⟨(deploy main roles ctor F wire { horizon := 0 } e).events,
      (deploy main roles ctor F wire { horizon := 0 } e).world, 0, .action⟩, ?_, ?_⟩
    · simp only [machine, next, deploys, Bool.false_eq_true, if_false]
    · simp [machine, State.observe, deploy_events deploys]

/-- **The frozen machines have no reverse diagram** in an environment that
issues a credit at every boundary, once the deployment completes. -/
theorem no_reverse_diagram_credits {E : Source.Env} (P : Source.SrcProg E) (F : Fixed)
    (x : Start) (e : SessionEnv)
    (deploys : (deploy x.code.main x.code.roles x.code.ctor F
      Solidity.Semantics.IntrinsicSession.wire { horizon := 0 } e).stops = false)
    (credits : ∀ h n, ∃ t v, e.requests h n = some (.credit t v))
    (D : Solidity.Correctness.Sim.Diagram (targetMachine F x e) (sourceMachine P e)) : False :=
  no_reverse_diagram P e (target_grows x.world deploys credits) D

end Target

end Solidity.Correctness.Lowering.Sim.Session
