import Solidity.Tools.Counterexample

/-!
# Kernel facts for failed postcondition slots

Guards the editor regression in which a reported failing index is mistaken for
an arbitrary clause. A slot is tied to the exact typed postcondition and state
used by `postFails`, with a proof that its clause does not hold. This additive
foundation neither identifies source spans nor connects a displayed candidate
to the original verification obligation; those producer obligations remain.
It does not turn an unknown outcome, panic, or tested candidate into a proof.
-/

namespace Solidity

variable {C : Contract} {Γ : Ctx}

/-- A reported index names a member of the exact typed postcondition split,
and that clause is false in the same typed state. No source location is inferred. -/
def Fml.FailedPostSlot (n : Nat) (post : Fml C Γ) (σ : State C Γ) (i : Nat) : Prop :=
  ∃ clause : Fml C Γ,
    (i, clause) ∈ (List.range n).zip (Fml.conjN n post) ∧ ¬ holds σ clause

/-- Every index selected by the existing `ff` filter has a kernel-sound clause
identity; the finite evaluator's unknown cases cannot establish this fact. -/
theorem Fml.failedPostSlot_of_mem (dom : TDom) (n : Nat)
    (post : Fml C Γ) (σ : State C Γ) (i : Nat)
    (h : i ∈ ((List.range n).zip (Fml.conjN n post)).filterMap
      (fun (j, clause) => if clause.eval3 dom σ = .ff then some j else none)) :
    Fml.FailedPostSlot n post σ i := by
  rcases List.mem_filterMap.mp h with ⟨⟨j, clause⟩, hslot, hselected⟩
  grind [Fml.FailedPostSlot, Fml.eval3_ff]

/-- A successful typed run and the exact existing `postFails` result tie every
reported index to a false clause in that run's final state. This says nothing
about source spans or entry premises of the enclosing verification obligation. -/
theorem Fml.failedPostSlot_of_modal_postFails {Γ₁ Γ₀ : Ctx}
    (dom : TDom) (n : Nat) (σ : State C Γ) (m : Modality)
    (program : Prog C Γ Γ₁) (frames : Frames C Γ₁ Γ₀)
    (post : Fml C Γ₀) (finalState : State C Γ₀) (indices : List Nat) (i : Nat)
    (hrun : Prog.runFramesF loopFuel σ program frames = .ok finalState)
    (hresult : Fml.postFails dom n σ (.modal m program frames post) = some (none, indices))
    (hindex : i ∈ indices) : Fml.FailedPostSlot n post finalState i := by
  simp only [Fml.postFails, hrun] at hresult
  cases hresult
  exact Fml.failedPostSlot_of_mem dom n post finalState i hindex

end Solidity
