import Solidity.Semantics.Run

/-! Isolated typed sequencing cases. This fixture is not production integration. -/
namespace H62.RevertFixture
open Solidity

variable {C : Contract} {Γ Δ Ξ : Ctx}

theorem first_error {σ : State C Γ} {s : Stmt C Γ Δ} {P : Prog C Δ Ξ}
    {e : THalt} (h : s.run σ = .error e) :
    (Prog.cons s P).run σ = .error e := by
  show TRun.seq s.runR P.runR σ = _
  simp only [TRun.seq, Solidity.Stmt.run] at h ⊢
  rw [h]

theorem first_revert {σ : State C Γ} {s : Stmt C Γ Δ} {P : Prog C Δ Ξ}
    (h : s.run σ = .error .revert) : (Prog.cons s P).run σ = .error .revert :=
  first_error h

theorem tail_error {σ : State C Γ} {s : Stmt C Γ Δ} {P : Prog C Δ Ξ}
    {o : Out C σ.H Δ} {e : THalt} (hs : s.run σ = .ok o)
    (ht : P.run o.st = .error e) : (Prog.cons s P).run σ = .error e := by
  rw [Prog.run_cons_ok hs, ht]
  rfl

/-- For every supplied state, intrinsic revert satisfies the premise. -/
theorem revert_witness (σ : State C Γ) (P : Prog C Γ Ξ) :
    (Prog.cons .revert P).run σ = .error .revert := by
  apply first_revert
  rfl

#print axioms revert_witness
#print axioms first_error
#print axioms first_revert
#print axioms tail_error
end H62.RevertFixture
