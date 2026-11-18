import Solidity.Correctness.Lowering.Sim.Session.Target

/-! The target session machine within a horizon (plan step
`ls2s-session-diagrams`, lane forward): a reachable state that has issued `i`
actions observes a prefix of the run at every horizon above `i`. This is
`realizes` of `Session/Target.lean` with the horizon it leaves existential,
which the forward resource bound needs. -/
namespace Solidity.Correctness.Lowering.Sim.Session

open Solidity.Roadmap Solidity.Correctness.Sim Solidity.Semantics.IntrinsicSession
open Solidity.ContractWorld (World Entry Role)

variable {contracts : List Contract} {main : Nat} {roles : Fin contracts.length → Role}
  {ctor : (k : Fin contracts.length) → Bytes → Option (Prog contracts[k] [] [])}
  {entry : (k : Fin contracts.length) → Bytes → Option (Entry contracts[k] Bytes)}
  {F : Fixed} {wire : Wire} {r : Bound} {e : SessionEnv}

/-- From a boundary, a reachable state observes the run's prefix at a horizon
of at most one more than the actions issued since. -/
theorem go_within {s₀ s : State contracts}
    (p : Path (fun s t => next main roles ctor entry F wire r e s = some t) s₀ s) :
    s₀.pending = .action →
      ∃ k, s₀.issued + k ≤ s.issued + 1 ∧
        s.observe = (go entry F wire r e s₀.history s₀.issued s₀.world k).pfx := by
  induction p with
  | refl s =>
    intro act
    rcases s with ⟨h, w, n, pend⟩
    cases act
    exact ⟨0, Nat.le_succ _, rfl⟩
  | @head s₀ t u edge rest ih =>
    intro act
    rcases s₀ with ⟨h, w, n, pend⟩
    cases act
    cases next_a : e.requests h n with
    | none =>
      simp only [next, next_a, Option.some.injEq] at edge
      subst edge
      rw [rest.stuck fun _ => by simp only [next, reduceCtorEq, not_false_eq_true]]
      exact ⟨1, Nat.le_refl _, by rw [go_idle next_a]; rfl⟩
    | some a =>
      cases stops : (step entry F wire r e h n w a).stops with
      | true =>
        simp only [next, next_a, stops, if_true, Option.some.injEq] at edge
        subst edge
        rw [rest.stuck fun _ => by simp only [next, reduceCtorEq, not_false_eq_true]]
        exact ⟨1, Nat.le_refl _, by rw [go_stops next_a stops]; rfl⟩
      | false =>
        simp only [next, next_a, stops, Bool.false_eq_true, if_false, Option.some.injEq] at edge
        subst edge
        obtain ⟨k, le, obs⟩ := ih rfl
        exact ⟨k + 1, by simpa only [Nat.add_assoc, Nat.add_comm 1 k] using le,
          by rw [go_step next_a stops, obs]; rfl⟩

/-- **Realization within a horizon**: a reachable state of the machine of a
fresh session that has issued fewer than `m` actions observes a prefix of the
run at horizon `m` with the same failures. -/
theorem within_fresh {s : State contracts} {m : Nat}
    (reach : (machine main roles ctor entry F wire .fresh e r).Reachable s) (le : s.issued < m) :
    (s.observe).Le (run main roles ctor entry F wire .fresh e (atHorizon r m)).pfx := by
  cases Path.ofStar reach with
  | refl => exact ⟨List.nil_prefix, .inl rfl⟩
  | head edge rest =>
    cases stops : (deploy main roles ctor F wire r e).stops with
    | true =>
      simp only [machine, State.start, next, stops, if_true, Option.some.injEq] at edge
      subst edge
      rw [rest.stuck fun _ => by simp only [machine, next, reduceCtorEq, not_false_eq_true]]
      exact ⟨List.nil_prefix, .inl rfl⟩
    | false =>
      simp only [machine, State.start, next, stops, Bool.false_eq_true, if_false,
        Option.some.injEq] at edge
      subst edge
      obtain ⟨k, small, obs⟩ := go_within rest rfl
      have done : (deploy main roles ctor F wire (atHorizon r m) e).stops = false := by
        rw [deploy_bound (r := atHorizon r m) (r' := r) rfl]; exact stops
      rw [obs, run_fresh done, deploy_bound (r := atHorizon r m) (r' := r) rfl]
      dsimp only
      rw [go_at]
      exact (go_mono k m _ _ _ (by simp only [Nat.zero_add] at small; omega)).1

end Solidity.Correctness.Lowering.Sim.Session
