import Solidity.Backend.Passes.TailMachine

/-! Finite loop witnesses transport stack suffixes through the existing
noncomputable loop semantics. Divergence of arbitrary untyped code is not
assumed to transport; typed compiler certificates handle that case. -/
namespace Solidity.Backend.Passes
open Solidity.Evm

private def TurnMatches (tail : List Word) : Machine ⊕ Evm.Out → Machine ⊕ Evm.Out → Prop
  | .inl m, actual => actual = .inl (appendTail m tail)
  | .inr (.ok m k), actual => actual = .inr (.ok (appendTail m tail) k)
  | .inr .revert, actual => actual = .inr .revert
  | .inr .fault, _ => True

private theorem turn_tail {rc rb : Machine → Evm.Out}
    (hc : TailStable rc) (hb : TailStable rb) (m : Machine) (tail : List Word) :
    TurnMatches tail (loopTurn rc rb m) (loopTurn rc rb (appendTail m tail)) := by
  cases hr : rc m with
  | fault => simp only [loopTurn, hr, TurnMatches]
  | revert =>
    have ht := hc m tail (by rw [hr]; intro h; cases h)
    simp only [hr, appendOut] at ht
    simp only [loopTurn, hr, ht, TurnMatches]
  | ok mid skip =>
    cases skip with
    | succ k => simp only [loopTurn, hr, TurnMatches]
    | zero =>
      have ht := hc m tail (by rw [hr]; intro h; cases h)
      simp only [hr, appendOut] at ht
      cases hs : mid.stack with
      | nil => simp only [loopTurn, hr, hs, TurnMatches]
      | cons w st =>
        cases w with
        | slot s => simp only [loopTurn, hr, hs, TurnMatches]
        | val v =>
          by_cases hz : v.val = 0
          · rw [loopTurn, hr, loopTurn, ht]
            simp only [appendTail, hs, List.cons_append, hz, ite_true, TurnMatches]
          · cases hrb : rb {mid with stack := st} with
            | fault =>
              simp only [loopTurn, hr, hs, hz, ite_false, hrb, TurnMatches]
            | revert =>
              have hbt := hb {mid with stack := st} tail (by rw [hrb]; intro h; cases h)
              simp only [hrb, appendOut, appendTail] at hbt
              rw [loopTurn, hr, loopTurn, ht]
              simp only [appendTail, hs, List.cons_append, hz, ite_false, hrb, hbt, TurnMatches]
            | ok mid' skip' =>
              cases skip' with
              | succ k =>
                simp only [loopTurn, hr, hs, hz, ite_false, hrb, TurnMatches]
              | zero =>
                have hbt := hb {mid with stack := st} tail (by rw [hrb]; intro h; cases h)
                simp only [hrb, appendOut, appendTail] at hbt
                rw [loopTurn, hr, loopTurn, ht]
                simp only [appendTail, hs, List.cons_append, hz, ite_false, hrb, hbt, TurnMatches]

private theorem iter_tail {rc rb : Machine → Evm.Out}
    (hc : TailStable rc) (hb : TailStable rb) (n : Nat) (m : Machine) (tail : List Word) :
    TurnMatches tail (loopIterN rc rb n m) (loopIterN rc rb n (appendTail m tail)) := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    have ht := turn_tail hc hb m tail
    cases hs : loopTurn rc rb m with
    | inl mid =>
      simp only [hs, TurnMatches] at ht
      simp only [loopIterN, hs, ht]
      exact ih mid
    | inr out =>
      cases out with
      | fault => simp only [loopIterN, hs, TurnMatches]
      | revert =>
        simp only [hs, TurnMatches] at ht
        simp only [loopIterN, hs, ht, TurnMatches]
      | ok mid k =>
        simp only [hs, TurnMatches] at ht
        simp only [loopIterN, hs, ht, TurnMatches]

theorem loop_tail {rc rb : Machine → Evm.Out}
    (hc : TailStable rc) (hb : TailStable rb) : TailStable (loopRun rc rb) := by
  classical
  intro m tail hn
  by_cases he : ∃ r n, loopIterN rc rb n m = .inr r
  · obtain ⟨r, n, hr⟩ := he
    have hd := loopRun_of_iterN hr
    have ht := iter_tail hc hb n m tail
    rw [hr] at ht
    rw [hd] at hn ⊢
    cases r with
    | fault => exact (hn rfl).elim
    | revert => exact loopRun_of_iterN ht
    | ok mid k => exact loopRun_of_iterN ht
  · simp only [loopRun, he] at hn
    exact (hn rfl).elim

/-- Nested induction covers every target instruction, including loops.
No code classifier or desired output equality is a theorem premise. -/
theorem instr_tail (i : Instr) : TailStable i.step := by
  apply Instr.rec (motive_1 := fun i => TailStable i.step)
    (motive_2 := fun c => ∀ k, TailStable (exec c k)) (t := i)
  case loop =>
    intro c b hc hb
    exact loop_tail (hc 0) (hb 0)
  case nil => exact exec_nil_tail
  case cons =>
    intro i c hi hc
    exact exec_cons_tail i c hi hc
  all_goals first
    | exact primitive_tail _ (by intro c b h; cases h)
    | (intro n; exact primitive_tail _ (by intro c b h; cases h))

theorem exec_tail (c : List Instr) : ∀ k, TailStable (exec c k) := by
  induction c with
  | nil => exact exec_nil_tail
  | cons i c ih => exact exec_cons_tail i c (instr_tail i) ih

/-- Every nonfault result of actual code transports an untouched suffix. -/
theorem run_tail (c : List Instr) : TailStable (run c) := exec_tail c 0

end Solidity.Backend.Passes
