import Solidity.Correctness.Lowering.Sim.Session.Target.Machine

/-! Run coverage and realization of the session machine (plan step
`ls1n-intrinsic-machine`, LS0 instance, target side), stated at the level of
`IntrinsicSession.run` so they transfer to the session spec's semantics by
unfolding.

* `covers`: for every world, environment and bound, a reachable state of the
  machine with the bound's failures observes exactly the run's prefix;
  `covers_noFail` reads it in the one machine without failures.
* `realizes`: every reachable state observes a `Prefix.Le`-prefix of the run at
  some bound with the same failures; `realizes_noFail`: in the machine without
  failures, at some admissible bound without resource failure.

A single machine per world and environment cannot do both for failing bounds:
a failed frame shows a revert the run without failures need not show. -/
namespace Solidity.Correctness.Lowering.Sim.Session

open Solidity.Roadmap Solidity.Correctness.Sim Solidity.Semantics.IntrinsicSession
open Solidity.ContractWorld (World Entry Role)

variable {contracts : List Contract} {main : Nat} {roles : Fin contracts.length → Role}
  {ctor : (k : Fin contracts.length) → Bytes → Option (Prog contracts[k] [] [])}
  {entry : (k : Fin contracts.length) → Bytes → Option (Entry contracts[k] Bytes)}
  {F : Fixed} {wire : Wire} {r : Bound} {e : SessionEnv}

/-- From a boundary, the machine reaches the run's prefix at every horizon. -/
theorem go_covered : ∀ (k : Nat) (h : List Event) (n : Nat) (w : World (catalog contracts)),
    ∃ s, Star (fun s t => next main roles ctor entry F wire r e s = some t) ⟨h, w, n, .action⟩ s ∧
      s.observe = (go entry F wire r e h n w k).pfx
  | 0, h, n, w => ⟨_, .refl _, rfl⟩
  | k + 1, h, n, w => by
    cases next_a : e.requests h n with
    | none => exact ⟨⟨h, w, n, .idle⟩, .single (by simp only [next, next_a]), by rw [go_idle next_a]; rfl⟩
    | some a =>
      cases stops : (step entry F wire r e h n w a).stops with
      | true =>
        exact ⟨⟨h, w, n, .stopped⟩, .single (by simp only [next, next_a, stops, if_true]),
          by rw [go_stops next_a stops]; rfl⟩
      | false =>
        obtain ⟨s, path, obs⟩ := go_covered k (h ++ (step entry F wire r e h n w a).events) (n + 1)
          (step entry F wire r e h n w a).world
        refine ⟨s, (Star.single ?_).trans path, by rw [go_step next_a stops, obs]; rfl⟩
        simp only [next, next_a, stops, Bool.false_eq_true, if_false]

/-- From a boundary, every reachable state observes the run's prefix at some
horizon. -/
theorem go_realized {s₀ s : State contracts}
    (p : Path (fun s t => next main roles ctor entry F wire r e s = some t) s₀ s) :
    s₀.pending = .action →
      ∃ k, s.observe = (go entry F wire r e s₀.history s₀.issued s₀.world k).pfx := by
  induction p with
  | refl s =>
    intro act
    rcases s with ⟨h, w, n, pend⟩
    cases act
    exact ⟨0, rfl⟩
  | @head s₀ t u edge rest ih =>
    intro act
    rcases s₀ with ⟨h, w, n, pend⟩
    cases act
    have stuck : ∀ h w n, ∀ v, ¬ next main roles ctor entry F wire r e ⟨h, w, n, .stopped⟩ = some v :=
      fun _ _ _ _ => by simp only [next, reduceCtorEq, not_false_eq_true]
    cases next_a : e.requests h n with
    | none =>
      simp only [next, next_a, Option.some.injEq] at edge
      subst edge
      rw [rest.stuck fun _ => by simp only [next, reduceCtorEq, not_false_eq_true]]
      exact ⟨1, by rw [go_idle next_a]; rfl⟩
    | some a =>
      cases stops : (step entry F wire r e h n w a).stops with
      | true =>
        simp only [next, next_a, stops, if_true, Option.some.injEq] at edge
        subst edge
        rw [rest.stuck (stuck _ _ _)]
        exact ⟨1, by rw [go_stops next_a stops]; rfl⟩
      | false =>
        simp only [next, next_a, stops, Bool.false_eq_true, if_false, Option.some.injEq] at edge
        subst edge
        obtain ⟨k, obs⟩ := ih rfl
        exact ⟨k + 1, by rw [go_step next_a stops, obs]; rfl⟩

/-- The bound `r` with horizon `k`. -/
def atHorizon (r : Bound) (k : Nat) : Bound := { r with horizon := k }

theorem go_at (r : Bound) (k k' : Nat) (h : List Event) (n : Nat) (w : World (catalog contracts)) :
    go entry F wire (atHorizon r k) e h n w k' = go entry F wire r e h n w k' :=
  go_bound (r := atHorizon r k) (r' := r) rfl k' h n w

/-- **Coverage**: at every bound the machine with its failures reaches the
run's prefix. -/
theorem covers (w : SessionWorld contracts) (e : SessionEnv) (r : Bound) :
    ∃ s, (machine main roles ctor entry F wire w e r).Reachable s ∧
      (machine main roles ctor entry F wire w e r).observe s =
        (run main roles ctor entry F wire w e r).pfx := by
  cases w with
  | boundary w => exact go_covered r.horizon [] 0 w
  | fresh =>
    cases stops : (deploy main roles ctor F wire r e).stops with
    | true =>
      exact ⟨⟨[], initial roles e, 0, .stopped⟩,
        .single (by simp only [machine, State.start, next, stops, if_true]),
        by rw [run_fresh_stops stops]; rfl⟩
    | false =>
      obtain ⟨s, path, obs⟩ := go_covered (main := main) (roles := roles) (ctor := ctor) r.horizon
        (deploy main roles ctor F wire r e).events 0 (deploy main roles ctor F wire r e).world
      refine ⟨s, (Star.single ?_).trans path, by rw [run_fresh stops]; exact obs⟩
      simp only [machine, State.start, next, stops, Bool.false_eq_true, if_false]

/-- **Realization**: every reachable state observes a prefix of the run at some
bound with the same failures. -/
theorem realizes (w : SessionWorld contracts) (e : SessionEnv) (r : Bound)
    {s : State contracts} (reach : (machine main roles ctor entry F wire w e r).Reachable s) :
    ∃ r', r'.deployFails = r.deployFails ∧ r'.fails = r.fails ∧
      (s.observe).Le (run main roles ctor entry F wire w e r').pfx := by
  have p := Path.ofStar reach
  cases w with
  | boundary w =>
    obtain ⟨k, obs⟩ := go_realized p rfl
    exact ⟨atHorizon r k, rfl, rfl, by rw [obs, run_boundary, go_at]; exact Prefix.Le.refl _⟩
  | fresh =>
    cases p with
    | refl => exact ⟨r, rfl, rfl, ⟨List.nil_prefix, .inl rfl⟩⟩
    | head edge rest =>
      cases stops : (deploy main roles ctor F wire r e).stops with
      | true =>
        simp only [machine, State.start, next, stops, if_true, Option.some.injEq] at edge
        subst edge
        rw [rest.stuck fun _ => by simp only [machine, next, reduceCtorEq, not_false_eq_true]]
        exact ⟨r, rfl, rfl, ⟨List.nil_prefix, .inl rfl⟩⟩
      | false =>
        simp only [machine, State.start, next, stops, Bool.false_eq_true, if_false,
          Option.some.injEq] at edge
        subst edge
        obtain ⟨k, obs⟩ := go_realized rest rfl
        have done : (deploy main roles ctor F wire (atHorizon r k) e).stops = false := by
          rw [deploy_bound (r := atHorizon r k) (r' := r) rfl]; exact stops
        refine ⟨atHorizon r k, rfl, rfl, ?_⟩
        rw [obs, run_fresh done, deploy_bound (r := atHorizon r k) (r' := r) rfl]
        dsimp only
        rw [go_at]
        exact Prefix.Le.refl _

/-- The machine without resource failure. -/
noncomputable abbrev machine₀ (main : Nat) (roles : Fin contracts.length → Role)
    (ctor : (k : Fin contracts.length) → Bytes → Option (Prog contracts[k] [] []))
    (entry : (k : Fin contracts.length) → Bytes → Option (Entry contracts[k] Bytes))
    (F : Fixed) (wire : Wire) (w : SessionWorld contracts) (e : SessionEnv) : Machine :=
  machine main roles ctor entry F wire w e { horizon := 0 }

/-- Coverage of every bound without resource failure in the one machine
without failures. -/
theorem covers_noFail (w : SessionWorld contracts) (e : SessionEnv) {r : Bound} (good : r.NoFail) :
    ∃ s, (machine₀ main roles ctor entry F wire w e).Reachable s ∧
      (machine₀ main roles ctor entry F wire w e).observe s =
        (run main roles ctor entry F wire w e r).pfx := by
  rw [machine₀, machine_congr main roles ctor entry F wire w e (r' := r) ⟨good.1.symm, funext fun n => (good.2 n).symm⟩]
  exact covers w e r

/-- **Realization without resource failure**: every reachable state of the
machine without failures observes a prefix of the run at an admissible bound
without resource failure. -/
theorem realizes_noFail (w : SessionWorld contracts) (e : SessionEnv) {s : State contracts}
    (reach : (machine₀ main roles ctor entry F wire w e).Reachable s) :
    ∃ r', (r'.Admissible ∧ r'.NoFail) ∧ (s.observe).Le (run main roles ctor entry F wire w e r').pfx :=
  let ⟨r', df, fs, le⟩ := realizes w e _ reach
  ⟨r', ⟨trivial, df, fun n => congrFun fs n⟩, le⟩

end Solidity.Correctness.Lowering.Sim.Session
