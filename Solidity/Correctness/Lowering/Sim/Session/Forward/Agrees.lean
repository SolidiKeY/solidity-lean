import Solidity.Correctness.Lowering.Sim.Session.Forward

/-! Storage and event agreement from matched frames (plan step
`ls2s-session-diagrams`, lane forward): `Shrink.Lowering.Agrees`, clause (e) of
the session lift, for the lowered world of a compilation whose frames are
matched in every environment. A target state at a boundary holds the world the
run lists at the index of its issued actions (`worlds_fresh`); a reachable
Source boundary has issued at most its horizon (`reachable_budget`). -/
namespace Solidity.Correctness.Lowering.Sim.Session

open Solidity.Roadmap Solidity.Correctness.Sim Solidity.Semantics.IntrinsicSession
open Solidity.ContractWorld (World Entry Role)
open Solidity.Goals.Shrink.Lowering (Compilation loweredWorld envAbs transport Agrees)

section Worlds

variable {contracts : List Contract} {main : Nat} {roles : Fin contracts.length → Role}
  {ctor : (k : Fin contracts.length) → Bytes → Option (Prog contracts[k] [] [])}
  {entry : (k : Fin contracts.length) → Bytes → Option (Entry contracts[k] Bytes)}
  {F : Fixed} {wire : Wire} {r : Bound} {e : SessionEnv}

/-- From a boundary to a boundary `j` actions later: the later world is the
`j`th the run lists after the first, at every horizon of at least `j`. -/
theorem go_worlds {s₀ s : State contracts}
    (p : Path (fun s t => next main roles ctor entry F wire r e s = some t) s₀ s) :
    s₀.pending = .action → s.pending = .action →
      ∃ j, s.issued = s₀.issued + j ∧ ∀ k, j ≤ k →
        (s₀.world :: (go entry F wire r e s₀.history s₀.issued s₀.world k).worlds)[j]? =
          some s.world := by
  induction p with
  | refl s => exact fun _ _ => ⟨0, rfl, fun _ _ => rfl⟩
  | @head s₀ t u edge rest ih =>
    intro act act'
    rcases s₀ with ⟨h, w, n, pend⟩
    cases act
    cases next_a : e.requests h n with
    | none =>
      simp only [next, next_a, Option.some.injEq] at edge
      subst edge
      rw [rest.stuck fun _ => by simp only [next, reduceCtorEq, not_false_eq_true]] at act'
      cases act'
    | some a =>
      cases stops : (step entry F wire r e h n w a).stops with
      | true =>
        simp only [next, next_a, stops, if_true, Option.some.injEq] at edge
        subst edge
        rw [rest.stuck fun _ => by simp only [next, reduceCtorEq, not_false_eq_true]] at act'
        cases act'
      | false =>
        simp only [next, next_a, stops, Bool.false_eq_true, if_false, Option.some.injEq] at edge
        subst edge
        obtain ⟨j, issued, at_j⟩ := ih rfl act'
        refine ⟨j + 1, by rw [issued]; show n + 1 + j = n + (j + 1); omega, fun k le => ?_⟩
        obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [go_step next_a stops, List.getElem?_cons_succ]
        exact at_j k (by omega)

/-- **The boundary worlds of a fresh session**: a reachable boundary state that
has issued at most `m` actions holds the world the run at horizon `m` lists at
that index. -/
theorem worlds_fresh {s : State contracts} {m : Nat}
    (reach : (machine main roles ctor entry F wire .fresh e r).Reachable s)
    (act : s.pending = .action) (le : s.issued ≤ m) :
    (run main roles ctor entry F wire .fresh e (atHorizon r m)).worlds[s.issued]? = some s.world := by
  cases Path.ofStar reach with
  | refl => cases act
  | head edge rest =>
    cases stops : (deploy main roles ctor F wire r e).stops with
    | true =>
      simp only [machine, State.start, next, stops, if_true, Option.some.injEq] at edge
      subst edge
      rw [rest.stuck fun _ => by simp only [machine, next, reduceCtorEq, not_false_eq_true]] at act
      cases act
    | false =>
      simp only [machine, State.start, next, stops, Bool.false_eq_true, if_false,
        Option.some.injEq] at edge
      subst edge
      obtain ⟨j, issued, at_j⟩ := go_worlds rest rfl act
      have done : (deploy main roles ctor F wire (atHorizon r m) e).stops = false := by
        rw [deploy_bound (r := atHorizon r m) (r' := r) rfl]; exact stops
      rw [run_fresh done, deploy_bound (r := atHorizon r m) (r' := r) rfl]
      dsimp only [Run.after]
      rw [go_at, issued, Nat.zero_add]
      exact at_j m (by rw [issued, Nat.zero_add] at le; exact le)

end Worlds

variable [FreshNames] {E : Solidity.Source.Env} {D : Solidity.Goals.Shrink.Lowering.Diagram}
  {F : Fixed} {P : Solidity.Source.SrcProg E} {c : Compilation}

omit [FreshNames] in
/-- A reachable Source boundary has issued its horizon less its budget. -/
theorem reachable_budget {e : SessionEnv} {t : SourceState E}
    (reach : (sourceMachine P e).Reachable t) :
    ∀ n k i s last, t = .run n k i s last → i + k = n := by
  induction reach with
  | refl => intro _ _ _ _ _ h; cases h
  | tail _ edge ih =>
    intro n k i s last h
    cases edge with
    | deploy n₀ =>
      obtain ⟨rfl, rfl, rfl⟩ := deployStep_run h
      exact Nat.zero_add _
    | act n₀ k₀ i₀ s₀ last₀ =>
      obtain ⟨rfl, rfl, rfl⟩ := actStep_run h
      have := ih _ _ _ _ _ rfl
      omega

/-- **Agreement at every boundary** (`Shrink.Lowering.Agrees`) from matched
frames: the Source history leads the lowered run's, and the boundary world the
run lists holds a storage `D.globRel` relates to the Source state. -/
theorem agrees (fr : ∀ e, MatchedFrames D F P c e) (grows : ∀ n, n < D.fuel n) :
    Agrees D F P (loweredWorld c) := by
  intro e n k i s last _ _ reach
  obtain ⟨t, treach, m, -⟩ := (forward (fr e)).run reach
  obtain ⟨history, issued, act, inv, -⟩ : (fr e).Matches (.run n k i s last) t := m
  have small : t.issued < D.fuel n := by
    have := reachable_budget reach n k i s last rfl
    have := grows n
    omega
  refine ⟨?_, fun w at_i a deployed => ?_⟩
  · rw [← history]
    exact (within_fresh (m := D.fuel n) treach small).1
  · have held := worlds_fresh (m := D.fuel n) treach act (Nat.le_of_lt small)
    rw [issued] at held
    obtain rfl : t.world = w := Option.some.inj (held.symm.trans at_i)
    exact (fr e).glob s t.world inv a deployed

end Solidity.Correctness.Lowering.Sim.Session
