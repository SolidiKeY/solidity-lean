import Solidity.Backend.Passes.SourceTerminalFailure

/-! Exact INTERNAL divergence transport. Target fault is reflected only
under the original typed Input/payment-free certificate, never by a raw
fault-tail rule. Revert/panic remain separate terminal alternatives. -/
namespace Solidity.Backend.Passes
open Solidity.Evm Solidity.Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ Ω : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ} {R : Prog C Ξ Ω}

theorem compilation_fault_iff (a : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m) (hp : Evm.Prog.pays P = false) :
    run a.code m = .fault ↔ P.run σ = .error .diverge := by
  constructor
  · intro ht
    rcases compilation_exact a hi hp with
      ⟨_, _, _, hm, _, _⟩ | ⟨_, hm⟩ | ⟨hs, _⟩
    · rw [ht] at hm
      cases hm
    · rw [ht] at hm
      cases hm
    · exact hs
  · intro hs
    rcases compilation_exact a hi hp with
      ⟨_, _, hs', _, _, _⟩ | ⟨hs' | ⟨_, hs'⟩, _⟩ | ⟨_, ht⟩
    · rw [hs] at hs'
      cases hs'
    · rw [hs] at hs'
      cases hs'
    · rw [hs] at hs'
      cases hs'
    · exact ht

/-- Fault at any saved tail reflects divergence under the unchanged typed
Input. No corresponding statement is made about arbitrary raw target faults. -/
theorem compilation_fault_tail_iff (a : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m) (hp : Evm.Prog.pays P = false) (tail : List Word) :
    run a.code {m with stack := tail} = .fault ↔ P.run σ = .error .diverge :=
  compilation_fault_iff a (compilation_input_stack a hi tail) hp

theorem compilation_mapped_fault_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m)
    (ad : MappedBoundaryLink a d L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false) :
    run (a.code ++ d.code) m = .fault ↔
      P.run σ = .error .diverge ∨ ∃ o, P.run σ = .ok o ∧ Q.run o.st = .error .diverge := by
  constructor
  · intro ht
    rcases compilation_exact a hi hp with
      ⟨o, mid, hs, hm, _, hrep⟩ | ⟨_, hm⟩ | ⟨hs, _⟩
    · obtain ⟨mb, ha⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp hrep
      rw [run_append_ok hm] at ht
      exact .inr ⟨o, hs, (compilation_fault_iff d (ad o mid mb hs hm ha) hq).mp ht⟩
    · have hh := run_append_revert (c₂ := d.code) hm
      rw [ht] at hh
      cases hh
    · exact .inl hs
  · rintro (hs | ⟨o, hs, hq'⟩)
    · exact run_append_fault ((compilation_fault_iff a hi hp).mpr hs)
    · obtain ⟨mid, hm, _, hrep⟩ := compilation_success a hi hp hs
      obtain ⟨mb, ha⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp hrep
      rw [run_append_ok hm]
      exact (compilation_fault_iff d (ad o mid mb hs hm ha) hq).mpr hq'

theorem compilation_triple_fault_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m)
    (ad : MappedBoundaryLink a d L frame base σ m)
    (de : ReachedMappedLink a d e L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false) :
    run (a.code ++ (d.code ++ e.code)) m = .fault ↔
      P.run σ = .error .diverge ∨ ∃ o, P.run σ = .ok o ∧
        (Q.run o.st = .error .diverge ∨ ∃ u, Q.run o.st = .ok u ∧ R.run u.st = .error .diverge) := by
  constructor
  · intro ht
    rcases compilation_exact a hi hp with
      ⟨o, mid, hs, hm, _, hrep⟩ | ⟨_, hm⟩ | ⟨hs, _⟩
    · obtain ⟨mb, ha⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp hrep
      rw [run_append_ok hm] at ht
      exact .inr ⟨o, hs, (compilation_mapped_fault_iff d e
        (ad o mid mb hs hm ha) (de o mid mb hs hm ha) hq hr).mp ht⟩
    · have hh := run_append_revert (c₂ := d.code ++ e.code) hm
      rw [ht] at hh
      cases hh
    · exact .inl hs
  · rintro (hs | ⟨o, hs, hrest⟩)
    · exact run_append_fault ((compilation_fault_iff a hi hp).mpr hs)
    · obtain ⟨mid, hm, _, hrep⟩ := compilation_success a hi hp hs
      obtain ⟨mb, ha⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp hrep
      rw [run_append_ok hm]
      exact (compilation_mapped_fault_iff d e
        (ad o mid mb hs hm ha) (de o mid mb hs hm ha) hq hr).mpr hrest

/-- Independent source sequencing exposes the same reached alternatives. -/
theorem joined_diverge_iff (σ : State C Γ) :
    (P.join Q).run σ = .error .diverge ↔
      P.run σ = .error .diverge ∨ ∃ o, P.run σ = .ok o ∧ Q.run o.st = .error .diverge :=
  joined_halt_iff σ .diverge

/-- Actual joined intrinsic program, not a second invocation of target run. -/
theorem compilation_mapped_join_fault_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m) (ad : MappedBoundaryLink a d L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false) :
    run (a.code ++ d.code) m = .fault ↔ (P.join Q).run σ = .error .diverge :=
  (compilation_mapped_fault_iff a d hi ad hp hq).trans (joined_diverge_iff σ).symm

/-- Both target associations reflect the actual joined intrinsic program. -/
theorem compilation_triple_join_fault_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m)
    (ad : MappedBoundaryLink a d L frame base σ m)
    (de : ReachedMappedLink a d e L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false) :
    (run (a.code ++ (d.code ++ e.code)) m = .fault ↔
      (P.join (Q.join R)).run σ = .error .diverge) ∧
    (run ((a.code ++ d.code) ++ e.code) m = .fault ↔
      ((P.join Q).join R).run σ = .error .diverge) := by
  have hj : (P.join (Q.join R)).run σ = .error .diverge ↔
      P.run σ = .error .diverge ∨ ∃ o, P.run σ = .ok o ∧
        (Q.run o.st = .error .diverge ∨ ∃ u, Q.run o.st = .ok u ∧ R.run u.st = .error .diverge) := by
    rw [joined_diverge_iff]
    simp only [joined_diverge_iff]
  have h := (compilation_triple_fault_iff a d e hi ad de hp hq hr).trans hj.symm
  exact ⟨h, by simpa only [List.append_assoc, typed_sequencing_assoc] using h⟩

end Solidity.Backend.Passes
