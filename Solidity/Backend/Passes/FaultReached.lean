import Solidity.Backend.Passes.DivergenceWitness

/-! Exact physical successful-prefix witnesses before INTERNAL coarse
divergence. Revert and guarded panic remain separate. No output state/map is
invented for failure, and no ABI bytes or public resource prefix is modeled. -/
namespace Solidity.Backend.Passes
open Solidity.Evm Solidity.Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ Ω : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ} {R : Prog C Ξ Ω}

theorem compilation_mapped_fault_reached_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m) (ad : MappedBoundaryLink a d L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false) :
    run (a.code ++ d.code) m = .fault ↔
      (P.run σ = .error .diverge ∧ run a.code m = .fault) ∨
      ∃ (o : Solidity.Out C σ.H Δ) (mid : Machine) (mb : Nat → Fin W),
        P.run σ = .ok o ∧ run a.code m = .ok mid 0 ∧
        MappedOutput a (L + Evm.Prog.pushes P) frame base σ m o.st mid mb ∧
        d.Input (L + Evm.Prog.pushes P) frame mb o.st mid ∧
        Q.run o.st = .error .diverge ∧ run d.code mid = .fault := by
  constructor
  · intro ht
    rcases compilation_exact a hi hp with
      ⟨o, mid, hs, hm, _, ha⟩ | ⟨_, hm⟩ | ⟨hs, hm⟩
    · obtain ⟨mb, ma⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp ha
      have hd := ad o mid mb hs hm ma
      rw [run_append_ok hm] at ht
      exact .inr ⟨o, mid, mb, hs, hm, ma, hd,
        (compilation_fault_iff d hd hq).mp ht, ht⟩
    · have bad := run_append_revert (c₂ := d.code) hm
      rw [ht] at bad
      cases bad
    · exact .inl ⟨hs, hm⟩
  · rintro (⟨_, hm⟩ | ⟨o, mid, mb, _, hm, _, _, _, hd⟩)
    · exact run_append_fault hm
    · rw [run_append_ok hm]
      exact hd

theorem compilation_triple_fault_reached_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m)
    (ad : MappedBoundaryLink a d L frame base σ m)
    (de : ReachedMappedLink a d e L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false) :
    run (a.code ++ (d.code ++ e.code)) m = .fault ↔
      (P.run σ = .error .diverge ∧ run a.code m = .fault) ∨
      ∃ (o : Solidity.Out C σ.H Δ) (mid : Machine) (mb : Nat → Fin W),
        P.run σ = .ok o ∧ run a.code m = .ok mid 0 ∧
        MappedOutput a (L + Evm.Prog.pushes P) frame base σ m o.st mid mb ∧
        d.Input (L + Evm.Prog.pushes P) frame mb o.st mid ∧
        ((Q.run o.st = .error .diverge ∧ run d.code mid = .fault) ∨
          ∃ (u : Solidity.Out C o.st.H Ξ) (next : Machine) (nb : Nat → Fin W),
            Q.run o.st = .ok u ∧ run d.code mid = .ok next 0 ∧
            MappedOutput d ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
              frame mb o.st mid u.st next nb ∧
            e.Input ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q) frame nb u.st next ∧
            R.run u.st = .error .diverge ∧ run e.code next = .fault) := by
  constructor
  · intro ht
    rcases compilation_exact a hi hp with
      ⟨o, mid, hs, hm, _, ha⟩ | ⟨_, hm⟩ | ⟨hs, hm⟩
    · obtain ⟨mb, ma⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp ha
      have hd := ad o mid mb hs hm ma
      rw [run_append_ok hm] at ht
      exact .inr ⟨o, mid, mb, hs, hm, ma, hd,
        (compilation_mapped_fault_reached_iff d e hd (de o mid mb hs hm ma) hq hr).mp ht⟩
    · have bad := run_append_revert (c₂ := d.code ++ e.code) hm
      rw [ht] at bad
      cases bad
    · exact .inl ⟨hs, hm⟩
  · rintro (⟨_, hm⟩ | ⟨o, mid, mb, _, hm, _, _, ⟨_, hd⟩ | ⟨u, next, nb, _, hn, _, _, _, he⟩⟩)
    · exact run_append_fault hm
    · rw [run_append_ok hm]
      exact run_append_fault hd
    · rw [run_append_ok hm, run_append_ok hn]
      exact he

/-- The same exact physical witness law for left-associated code. -/
theorem compilation_triple_fault_reached_left_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m)
    (ad : MappedBoundaryLink a d L frame base σ m)
    (de : ReachedMappedLink a d e L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false) :
    run ((a.code ++ d.code) ++ e.code) m = .fault ↔
      (P.run σ = .error .diverge ∧ run a.code m = .fault) ∨
      ∃ (o : Solidity.Out C σ.H Δ) (mid : Machine) (mb : Nat → Fin W),
        P.run σ = .ok o ∧ run a.code m = .ok mid 0 ∧
        MappedOutput a (L + Evm.Prog.pushes P) frame base σ m o.st mid mb ∧
        d.Input (L + Evm.Prog.pushes P) frame mb o.st mid ∧
        ((Q.run o.st = .error .diverge ∧ run d.code mid = .fault) ∨
          ∃ (u : Solidity.Out C o.st.H Ξ) (next : Machine) (nb : Nat → Fin W),
            Q.run o.st = .ok u ∧ run d.code mid = .ok next 0 ∧
            MappedOutput d ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
              frame mb o.st mid u.st next nb ∧
            e.Input ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q) frame nb u.st next ∧
            R.run u.st = .error .diverge ∧ run e.code next = .fault) := by
  simpa only [List.append_assoc] using compilation_triple_fault_reached_iff a d e hi ad de hp hq hr

end Solidity.Backend.Passes
