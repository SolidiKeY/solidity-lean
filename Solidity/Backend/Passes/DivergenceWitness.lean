import Solidity.Backend.Passes.Divergence

/-! Named physical witnesses for the successful prefixes of a diverging
composition. No map or post-state is requested after divergence itself. -/
namespace Solidity.Backend.Passes
open Solidity.Evm Solidity.Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ Ω : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ} {R : Prog C Ξ Ω}

theorem compilation_mapped_fault_witness_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m) (ad : MappedBoundaryLink a d L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false) :
    run (a.code ++ d.code) m = .fault ↔
      P.run σ = .error .diverge ∨
      ∃ (o : Solidity.Out C σ.H Δ) (mid : Machine) (mb : Nat → Fin W),
        P.run σ = .ok o ∧ run a.code m = .ok mid 0 ∧
        MappedOutput a (L + Evm.Prog.pushes P) frame base σ m o.st mid mb ∧
        Q.run o.st = .error .diverge := by
  constructor
  · intro ht
    rcases (compilation_mapped_fault_iff a d hi ad hp hq).mp ht with hs | ⟨o, hs, hd⟩
    · exact .inl hs
    · obtain ⟨mid, hm, _, hr⟩ := compilation_success a hi hp hs
      obtain ⟨mb, ha⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp hr
      exact .inr ⟨o, mid, mb, hs, hm, ha, hd⟩
  · rintro (hs | ⟨o, mid, mb, hs, _, _, hd⟩)
    · exact (compilation_mapped_fault_iff a d hi ad hp hq).mpr (.inl hs)
    · exact (compilation_mapped_fault_iff a d hi ad hp hq).mpr (.inr ⟨o, hs, hd⟩)

theorem compilation_triple_fault_witness_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m)
    (ad : MappedBoundaryLink a d L frame base σ m)
    (de : ReachedMappedLink a d e L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false) :
    run (a.code ++ (d.code ++ e.code)) m = .fault ↔
      P.run σ = .error .diverge ∨
      ∃ (o : Solidity.Out C σ.H Δ) (mid : Machine) (mb : Nat → Fin W),
        P.run σ = .ok o ∧ run a.code m = .ok mid 0 ∧
        MappedOutput a (L + Evm.Prog.pushes P) frame base σ m o.st mid mb ∧
        (Q.run o.st = .error .diverge ∨
          ∃ (u : Solidity.Out C o.st.H Ξ) (next : Machine) (nb : Nat → Fin W),
            Q.run o.st = .ok u ∧ run d.code mid = .ok next 0 ∧
            MappedOutput d ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
              frame mb o.st mid u.st next nb ∧ R.run u.st = .error .diverge) := by
  constructor
  · intro ht
    rcases (compilation_triple_fault_iff a d e hi ad de hp hq hr).mp ht with
      hs | ⟨o, hs, hd | ⟨u, hu, he⟩⟩
    · exact .inl hs
    · obtain ⟨mid, hm, _, hrep⟩ := compilation_success a hi hp hs
      obtain ⟨mb, ha⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp hrep
      exact .inr ⟨o, mid, mb, hs, hm, ha, .inl hd⟩
    · obtain ⟨mid, hm, _, hrep⟩ := compilation_success a hi hp hs
      obtain ⟨mb, ha⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp hrep
      obtain ⟨next, hn, _, hrep'⟩ := compilation_success d (ad o mid mb hs hm ha) hq hu
      obtain ⟨nb, hd⟩ := (mapped_output_iff d _ _ _ _ _ _ _).mp hrep'
      exact .inr ⟨o, mid, mb, hs, hm, ha, .inr ⟨u, next, nb, hu, hn, hd, he⟩⟩
  · rintro (hs | ⟨o, mid, mb, hs, _, _, hd | ⟨u, next, nb, hu, _, _, he⟩⟩)
    · exact (compilation_triple_fault_iff a d e hi ad de hp hq hr).mpr (.inl hs)
    · exact (compilation_triple_fault_iff a d e hi ad de hp hq hr).mpr (.inr ⟨o, hs, .inl hd⟩)
    · exact (compilation_triple_fault_iff a d e hi ad de hp hq hr).mpr
        (.inr ⟨o, hs, .inr ⟨u, hu, he⟩⟩)

/-- Both code associations expose exactly the same reached physical witnesses. -/
theorem triple_fault_associations (a : Compilation b F P) (d : Compilation b a.frag Q)
    (e : Compilation b d.frag R) (m : Machine) :
    run ((a.code ++ d.code) ++ e.code) m = .fault ↔
      run (a.code ++ (d.code ++ e.code)) m = .fault := by
  rw [List.append_assoc]

end Solidity.Backend.Passes
