import Solidity.Evm.Machine

/-!
# Stack suffix transport for actual target execution

These are properties of the existing Machine/Instr/exec, not another
evaluator. Faults of arbitrary untyped target code need not transport:
POP on [] faults, while POP on a saved word succeeds. Successful/reverting
runs do transport. The compiler adapter separately handles typed divergence.
-/
namespace Solidity.Backend.Passes
open Solidity.Evm

def appendTail (m : Machine) (tail : List Word) : Machine :=
  {m with stack := m.stack ++ tail}

def appendOut (tail : List Word) : Evm.Out → Evm.Out
  | .ok m k => .ok (appendTail m tail) k
  | .revert => .revert
  | .fault => .fault

def TailStable (f : Machine → Evm.Out) : Prop :=
  ∀ (m : Machine) (tail : List Word), f m ≠ .fault →
    f (appendTail m tail) = appendOut tail (f m)

private theorem get_append {xs : List Word} {i : Nat} {w : Word}
    (h : xs[i]? = some w) (tail : List Word) :
    (xs ++ tail)[i]? = some w := by
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp h
  exact (List.getElem?_append_left hi).trans h

/-- Primitive case of the nested instruction induction. Loops are handled
by their actual finite execution witnesses, not excluded from emitted code. -/
theorem primitive_tail (i : Instr) (hl : ∀ c b, i ≠ .loop c b) :
    TailStable i.step := by
  cases i with
  | loop c b => exact (hl c b rfl).elim
  | dup n =>
    intro m tail h
    cases n with
    | zero =>
      cases hg : m.stack[0]? <;>
        simp only [Instr.step, Nat.zero_sub, hg] at h <;> exact (h rfl).elim
    | succ n =>
      cases hg : m.stack[n]? with
      | none =>
        simp only [Instr.step, Nat.add_sub_cancel, hg] at h
        exact (h rfl).elim
      | some w =>
        have he := get_append hg tail
        simp only [Instr.step, Nat.add_sub_cancel, hg, appendTail, he, appendOut, Machine.next]
        rfl
  | swap n =>
    intro m tail h
    cases n with
    | zero =>
      cases hs : m.stack <;> simp only [Instr.step, hs] at h <;> exact (h rfl).elim
    | succ n =>
      cases hs : m.stack with
      | nil =>
        simp only [Instr.step, hs] at h
        exact (h rfl).elim
      | cons a st =>
        cases hg : st[n]? with
        | none =>
          simp only [Instr.step, hs, hg] at h
          exact (h rfl).elim
        | some w =>
          have he := get_append hg tail
          obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hg
          simp only [Instr.step, hs, hg, appendTail, List.cons_append, he,
            appendOut, Machine.next, List.set_append_left n a hi]
  | _ =>
    intro m tail h
    simp only [Instr.step] at h ⊢
    repeat' first
      | (simp_all only [appendTail, appendOut, Machine.next,
          List.cons_append, if_pos, if_neg, ne_eq, reduceCtorEq,
          not_false_eq_true, not_true_eq_false]; done)
      | split at h

theorem exec_nil_tail (k : Nat) : TailStable (exec [] k) := by
  intro m tail _
  rfl

theorem exec_cons_tail (i : Instr) (c : List Instr)
    (hi : TailStable i.step) (hc : ∀ k, TailStable (exec c k)) :
    ∀ k, TailStable (exec (i :: c) k) := by
  intro k m tail hn
  cases k with
  | succ k => exact hc k m tail hn
  | zero =>
    cases hs : i.step m with
    | fault =>
      simp only [exec_cons_zero, hs, Out.fault_bind] at hn
      exact (hn rfl).elim
    | revert =>
      have ht := hi m tail (by rw [hs]; intro h; cases h)
      simp only [hs, appendOut] at ht
      simp only [exec_cons_zero, hs, ht, Out.revert_bind, appendOut]
    | ok mid skip =>
      have ht := hi m tail (by rw [hs]; intro h; cases h)
      simp only [hs, appendOut] at ht
      simp only [exec_cons_zero, hs, Out.ok_bind] at hn
      simpa only [exec_cons_zero, hs, ht, Out.ok_bind] using hc skip mid tail hn

end Solidity.Backend.Passes
