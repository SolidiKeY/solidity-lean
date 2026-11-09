import Solidity.Semantics.Run

/-!
# Scratch (itree-inspection, Experiment C(i)): the loop by `partial_fixpoint`

`TLoop.run` is `Classical.choose` over `iterN` with a compiled twin
(`runImpl'`).  Here the loop is Lean's `partial_fixpoint` in `Option`
(`none` = no iteration is done), and `TLoop.run` is recovered from it.
Not for merge: `docs/audits/itree-inspection.md`.
-/

namespace Solidity.Scratch.ITree

open Solidity

namespace Loop

variable {α : Type} (body : α → TRes α) (c : α → TRes Bool)

/-- The loop as a least fixpoint: `none` when it never ends. -/
def runPF (σ : α) : Option (TRes α) :=
  match TLoop.step body c σ with
  | .inl τ => runPF τ
  | .inr r => some r
partial_fixpoint

/-- The loop's outcome, `diverge` when it never ends. -/
def run (σ : α) : TRes α := (runPF body c σ).getD (.error .diverge)

variable {body c}

theorem runPF_of_iterN {n : Nat} {σ : α} {r : TRes α}
    (h : TLoop.iterN body c n σ = .inr r) : runPF body c σ = some r := by
  induction n generalizing σ with
  | zero => cases h
  | succ n ih =>
    rw [runPF]
    simp only [TLoop.iterN] at h
    split at h <;> rename_i hs <;> rw [hs]
    · exact ih h
    · cases h; rfl

theorem iterN_of_runPF {σ : α} {r : TRes α} (h : runPF body c σ = some r) :
    ∃ n, TLoop.iterN body c n σ = .inr r := by
  refine runPF.fixpoint_induct body c
    (fun f => ∀ σ r, f σ = some r → ∃ n, TLoop.iterN body c n σ = .inr r) ?adm ?step σ r h
  case adm =>
    exact Lean.Order.admissible_pi_apply _ (fun σ => Lean.Order.admissible_pi _
      (fun r => Lean.Order.Option.admissible_eq_some _ r))
  case step =>
    intro f ih σ r h
    simp only at h
    split at h <;> rename_i hs
    · obtain ⟨n, hn⟩ := ih _ _ h
      exact ⟨n + 1, by simp only [TLoop.iterN, hs]; exact hn⟩
    · cases h; exact ⟨1, by simp only [TLoop.iterN, hs]⟩

/-- **`TLoop.run` is the least fixpoint's reading.** -/
theorem run_eq (σ : α) : run body c σ = TLoop.run body c σ := by
  unfold run
  cases h : runPF body c σ with
  | none =>
    unfold TLoop.run
    rw [dif_neg]; · rfl
    rintro ⟨r, n, hn⟩; rw [runPF_of_iterN hn] at h; cases h
  | some r =>
    obtain ⟨n, hn⟩ := iterN_of_runPF h
    exact (TLoop.run_of_iterN hn).symm

/-- The unfolding equation, for free. -/
theorem run_unfold (σ : α) :
    run body c σ = match TLoop.step body c σ with
      | .inl τ => run body c τ
      | .inr r => r := by
  unfold run; rw [runPF]; split <;> rfl

end Loop

end Solidity.Scratch.ITree

namespace Solidity.Scratch.ITree.LoopTest
open Solidity
def bodyT : Nat → TRes Nat := fun n => .ok (n + 1)
def condT : Nat → TRes Bool := fun n => .ok (decide (n < 3))
-- Neither `decide` nor `rfl` reduces it (the fixpoint is `Classical`, as
-- `TLoop.run` is); the unfolding equation does, step by step:
example : Loop.run bodyT condT 0 = .ok 3 := by
  iterate 4 (rw [Loop.run_unfold]; simp only [TLoop.step, bodyT, condT, Nat.reduceLT, Nat.reduceAdd, decide_true, decide_false]; try rfl)
#eval Loop.run bodyT condT 0
end Solidity.Scratch.ITree.LoopTest
