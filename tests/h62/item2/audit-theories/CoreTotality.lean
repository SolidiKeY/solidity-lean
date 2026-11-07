import Solidity.Evm.Correct

/-!
Success corollary for the unchanged checked core compiler. Its source-success,
non-payment, fragment, simulation and array-growth-bound hypotheses are separately discharged
for a concrete bool program below; none is added to a frozen statement.
The core machine has no byte-data, gas-accounting or fork observation. These
boundaries are recorded rather than encoded as fictitious premises.
-/
namespace H62.AuditTheories.CompilerAudit
open Solidity Solidity.Evm

/-- A supported non-paying successful source run must compile to a successful
machine run. This strengthens the success observation of compile_exact. -/
theorem core_success {C : Contract} {Γ Δ : Ctx} {L b : Nat}
    {F : Frag Γ} {F' : Frag Δ} {P : Solidity.Prog C Γ Δ}
    {σ : State C Γ} {m : Machine} {o : Solidity.Out C σ.H Δ}
    (hP : inFragP F P = some F') (hm : Sim C L b F σ m)
    (hL : L + Evm.Prog.pushes P ≤ Lmax) (hpay : Evm.Prog.pays P = false)
    (source_ok : Solidity.Prog.run σ P = .ok o) :
    ∃ m', Evm.run (compileProg b P) m = .ok m' 0 ∧ m'.stack = m.stack ∧
      Sim C (L + Evm.Prog.pushes P) b F' o.st m' := by
  rcases Evm.compile_exact hP hm hL hpay with success | failure | divergence
  · obtain ⟨o', m', ho, hr, hs, hsim⟩ := success
    rw [source_ok] at ho
    cases ho
    exact ⟨m', hr, hs, hsim⟩
  · rcases failure.1 with hrevert | ⟨_, hpanic⟩
    · rw [source_ok] at hrevert
      cases hrevert
    · rw [source_ok] at hpanic
      cases hpanic
  · rw [source_ok] at divergence
    cases divergence.1

/-- `bool flag = value;` as an intrinsic scoped program. -/
def boolProgram (C : Contract) (value : Bool) : Solidity.Prog C [] [.val .bool] :=
  .cons (.declLocal .bool (.user "flag") (some (.simple (.bool value)))) .nil

/-- Its complete checked fragment certificate exists for each value. -/
theorem bool_fragment (C : Contract) (value : Bool) :
    inFragP (Frag.init []) (boolProgram C value) = some (Frag.init [.val .bool]) := by
  cases value <;> rfl

/-- Its supported compiler never pays, so payment refusal cannot hide failure. -/
theorem bool_no_payment (C : Contract) (value : Bool) :
    Evm.Prog.pays (boolProgram C value) = false := by
  cases value <;> rfl

/-- Concrete input machine, independent of any compiler success assumption. -/
def initialMachine : Machine := Machine.init

/-- Its code really writes the encoded bool into the local's observable cell. -/
theorem bool_target_success (C : Contract) (value : Bool) :
    ∃ m', Evm.run (compileProg 0 (boolProgram C value)) initialMachine = .ok m' 0 ∧
      m'.mem 0 = (if value then w[1] else w[0]) ∧ m'.stack = [] := by
  cases value <;> exact ⟨_, rfl, rfl, rfl⟩

/-- Actual source success and the bool value, without a source-success premise. -/
theorem bool_source_success (C : Contract) (value : Bool) (σ : State C []) :
    ∃ o : Solidity.Out C σ.H [.val .bool], Solidity.Prog.run σ (boolProgram C value) = .ok o ∧
      o.st.env.1 = value := by
  cases value <;> exact ⟨_, rfl, rfl⟩

/-- Every simulation/growth-bound/source/non-payment premise is simultaneous on a
fresh input. This is a genuine witness for core_success, not a list of isolated
inhabitance facts. -/
theorem bool_core_joint_input (C : Contract) (value : Bool) :
    Sim C 1 0 (Frag.init []) (freshT C 0 W_pos ⟨0, W_pos⟩) initialMachine ∧
      1 + Evm.Prog.pushes (boolProgram C value) ≤ Lmax ∧
      inFragP (Frag.init []) (boolProgram C value) = some (Frag.init [.val .bool]) ∧
      Evm.Prog.pays (boolProgram C value) = false ∧
      ∃ o, Solidity.Prog.run (freshT C 0 W_pos ⟨0, W_pos⟩) (boolProgram C value) = .ok o := by
  refine ⟨Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl, ?_,
    bool_fragment C value, bool_no_payment C value, ?_⟩
  · change (1 : Nat) ≤ Lmax
    decide
  · obtain ⟨o, ho, _⟩ := bool_source_success C value _
    exact ⟨o, ho⟩

#print axioms bool_source_success
#print axioms bool_core_joint_input
#print axioms core_success
#print axioms bool_fragment
#print axioms bool_no_payment
#print axioms bool_target_success
end H62.AuditTheories.CompilerAudit
