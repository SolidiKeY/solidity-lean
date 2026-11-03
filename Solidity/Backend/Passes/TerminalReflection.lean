import Solidity.Backend.Passes.DivergenceWitness
import Solidity.Backend.Passes.TripleControls

/-! The remaining internal terminal direction: successful composed target
runs reflect actual source successes and correlated physical maps. This is
not a public Lang/Cert or resource-prefix certificate. -/
namespace Solidity.Backend.Passes
open Solidity.Evm Solidity.Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ Ω : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ} {R : Prog C Ξ Ω}

theorem compilation_mapped_reflect_success
    (a : Compilation b F P) (d : Compilation b a.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m final : Machine}
    (hi : a.Input L frame base σ m) (ad : MappedBoundaryLink a d L frame base σ m)
    (ht : run (a.code ++ d.code) m = .ok final 0) :
    ∃ (o : Solidity.Out C σ.H Δ) (u : Solidity.Out C o.st.H Ξ)
      (mid : Machine) (mb nb : Nat → Fin W),
      P.run σ = .ok o ∧ Q.run o.st = .ok u ∧
      run a.code m = .ok mid 0 ∧ run d.code mid = .ok final 0 ∧ final.stack = m.stack ∧
      MappedOutput a (L + Evm.Prog.pushes P) frame base σ m o.st mid mb ∧
      MappedOutput d ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
        frame mb o.st mid u.st final nb := by
  rcases a.correct hi with
    ⟨o, mid, hs, hm, sm, ha⟩ | ⟨_, hm⟩ | ⟨_, hm, _⟩ | ⟨_, hm | ⟨_, hm⟩⟩
  · obtain ⟨mb, ma⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp ha
    rw [run_append_ok hm] at ht
    obtain ⟨u, hu, sf, hd⟩ := compilation_reflect_success d (ad o mid mb hs hm ma) ht
    obtain ⟨nb, md⟩ := (mapped_output_iff d _ _ _ _ _ _ _).mp hd
    exact ⟨o, u, mid, mb, nb, hs, hu, hm, ht, sf.trans sm, ma, md⟩
  · have bad := run_append_revert (c₂ := d.code) hm
    rw [ht] at bad
    cases bad
  · have bad := run_append_revert (c₂ := d.code) hm
    rw [ht] at bad
    cases bad
  · have bad := run_append_fault (c₂ := d.code) hm
    rw [ht] at bad
    cases bad
  · have bad := run_append_revert (c₂ := d.code) hm
    rw [ht] at bad
    cases bad

theorem compilation_triple_reflect_success
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m final : Machine}
    (hi : a.Input L frame base σ m)
    (ad : MappedBoundaryLink a d L frame base σ m)
    (de : ReachedMappedLink a d e L frame base σ m)
    (ht : run (a.code ++ (d.code ++ e.code)) m = .ok final 0) :
    ∃ (o : Solidity.Out C σ.H Δ) (u : Solidity.Out C o.st.H Ξ) (v : Solidity.Out C u.st.H Ω)
      (mid next : Machine) (mb nb ob : Nat → Fin W),
      P.run σ = .ok o ∧ Q.run o.st = .ok u ∧ R.run u.st = .ok v ∧
      run a.code m = .ok mid 0 ∧ run d.code mid = .ok next 0 ∧ run e.code next = .ok final 0 ∧
      final.stack = m.stack ∧
      MappedOutput a (L + Evm.Prog.pushes P) frame base σ m o.st mid mb ∧
      MappedOutput d ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
        frame mb o.st mid u.st next nb ∧
      MappedOutput e (((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q) + Evm.Prog.pushes R)
        frame nb u.st next v.st final ob := by
  rcases a.correct hi with
    ⟨o, mid, hs, hm, sm, ha⟩ | ⟨_, hm⟩ | ⟨_, hm, _⟩ | ⟨_, hm | ⟨_, hm⟩⟩
  · obtain ⟨mb, ma⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp ha
    rw [run_append_ok hm] at ht
    obtain ⟨u, v, next, nb, ob, hu, hv, hn, hf, sf, md, me⟩ :=
      compilation_mapped_reflect_success d e (ad o mid mb hs hm ma) (de o mid mb hs hm ma) ht
    exact ⟨o, u, v, mid, next, mb, nb, ob, hs, hu, hv, hm, hn, hf, sf.trans sm, ma, md, me⟩
  · have bad := run_append_revert (c₂ := d.code ++ e.code) hm
    rw [ht] at bad
    cases bad
  · have bad := run_append_revert (c₂ := d.code ++ e.code) hm
    rw [ht] at bad
    cases bad
  · have bad := run_append_fault (c₂ := d.code ++ e.code) hm
    rw [ht] at bad
    cases bad
  · have bad := run_append_revert (c₂ := d.code ++ e.code) hm
    rw [ht] at bad
    cases bad

/-- Inhabited target-to-source reflection for actual allocating/capture/
reference-observation stages, with every caller tail. No source success
is supplied to the reflection theorem as a premise. -/
theorem terminal_reflection_inhabited (tail : List Word) :
    ∃ o, (ReachabilityControls.populatedBuilder.join
      (TripleControls.captureProg.join TripleControls.observeProg)).run
        (State.init Controls.Fixture.C) = .ok o := by
  open Controls.Fixture AllocatingControls TripleControls in
    obtain ⟨mb, nb, ob, mid, next, final, hall⟩ := shared_resources
    have ad : MappedBoundaryLink (.memory allocationStage) (.memory captureStage)
        1 7 initialBase (State.init C) {initialMachine with stack := tail} :=
      memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel)
    have de : ReachedMappedLink (.memory allocationStage) (.memory captureStage) (.memory observeStage)
        1 7 initialBase (State.init C) {initialMachine with stack := tail} := by
      intro o m b _ _ _
      exact memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel)
    obtain ⟨o, u, v, _, _, _, _, _, hs, hu, hv, _⟩ :=
      compilation_triple_reflect_success (.memory allocationStage) (.memory captureStage) (.memory observeStage)
        (compilation_input_stack (.memory allocationStage) prefix_input7 tail)
        ad de (hall tail).2.2.2.2.1
    exact ⟨_, (triple_source_success _ hs hu hv).2⟩

end Solidity.Backend.Passes
