import Solidity.Backend.Passes.TripleSequence

/-! Exact physical successful-prefix witnesses before INTERNAL coarse
revert. Panic retains the original asserts guard. No output state/map is
invented for failure, and no ABI bytes or public resource prefix is modeled. -/
namespace Solidity.Backend.Passes
open Solidity.Evm Solidity.Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ Ω : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ} {R : Prog C Ξ Ω}

theorem compilation_mapped_revert_witness_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m) (ad : MappedBoundaryLink a d L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false) :
    run (a.code ++ d.code) m = .revert ↔
      (TerminalFailure P σ ∧ run a.code m = .revert) ∨
      ∃ (o : Solidity.Out C σ.H Δ) (mid : Machine) (mb : Nat → Fin W),
        P.run σ = .ok o ∧ run a.code m = .ok mid 0 ∧
        MappedOutput a (L + Evm.Prog.pushes P) frame base σ m o.st mid mb ∧
        d.Input (L + Evm.Prog.pushes P) frame mb o.st mid ∧
        TerminalFailure Q o.st ∧ run d.code mid = .revert := by
  constructor
  · intro ht
    rcases compilation_exact a hi hp with
      ⟨o, mid, hs, hm, _, ha⟩ | ⟨hs, hm⟩ | ⟨_, hm⟩
    · obtain ⟨mb, ma⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp ha
      have hd := ad o mid mb hs hm ma
      rw [run_append_ok hm] at ht
      exact .inr ⟨o, mid, mb, hs, hm, ma, hd,
        (compilation_revert_iff d hd hq).mp ht, ht⟩
    · exact .inl ⟨hs, hm⟩
    · have bad := run_append_fault (c₂ := d.code) hm
      rw [ht] at bad
      cases bad
  · rintro (⟨_, hm⟩ | ⟨o, mid, mb, _, hm, _, _, _, hd⟩)
    · exact run_append_revert hm
    · rw [run_append_ok hm]
      exact hd

theorem compilation_triple_revert_witness_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m)
    (ad : MappedBoundaryLink a d L frame base σ m)
    (de : ReachedMappedLink a d e L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false) :
    run (a.code ++ (d.code ++ e.code)) m = .revert ↔
      (TerminalFailure P σ ∧ run a.code m = .revert) ∨
      ∃ (o : Solidity.Out C σ.H Δ) (mid : Machine) (mb : Nat → Fin W),
        P.run σ = .ok o ∧ run a.code m = .ok mid 0 ∧
        MappedOutput a (L + Evm.Prog.pushes P) frame base σ m o.st mid mb ∧
        d.Input (L + Evm.Prog.pushes P) frame mb o.st mid ∧
        ((TerminalFailure Q o.st ∧ run d.code mid = .revert) ∨
          ∃ (u : Solidity.Out C o.st.H Ξ) (next : Machine) (nb : Nat → Fin W),
            Q.run o.st = .ok u ∧ run d.code mid = .ok next 0 ∧
            MappedOutput d ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
              frame mb o.st mid u.st next nb ∧
            e.Input ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q) frame nb u.st next ∧
            TerminalFailure R u.st ∧ run e.code next = .revert) := by
  constructor
  · intro ht
    rcases compilation_exact a hi hp with
      ⟨o, mid, hs, hm, _, ha⟩ | ⟨hs, hm⟩ | ⟨_, hm⟩
    · obtain ⟨mb, ma⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp ha
      have hd := ad o mid mb hs hm ma
      rw [run_append_ok hm] at ht
      exact .inr ⟨o, mid, mb, hs, hm, ma, hd,
        (compilation_mapped_revert_witness_iff d e hd (de o mid mb hs hm ma) hq hr).mp ht⟩
    · exact .inl ⟨hs, hm⟩
    · have bad := run_append_fault (c₂ := d.code ++ e.code) hm
      rw [ht] at bad
      cases bad
  · rintro (⟨_, hm⟩ | ⟨o, mid, mb, _, hm, _, _, ⟨_, hd⟩ | ⟨u, next, nb, _, hn, _, _, _, he⟩⟩)
    · exact run_append_revert hm
    · rw [run_append_ok hm]
      exact run_append_revert hd
    · rw [run_append_ok hm, run_append_ok hn]
      exact he

/-- The same exact physical witness law for left-associated code. -/
theorem compilation_triple_revert_witness_left_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m)
    (ad : MappedBoundaryLink a d L frame base σ m)
    (de : ReachedMappedLink a d e L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false) :
    run ((a.code ++ d.code) ++ e.code) m = .revert ↔
      (TerminalFailure P σ ∧ run a.code m = .revert) ∨
      ∃ (o : Solidity.Out C σ.H Δ) (mid : Machine) (mb : Nat → Fin W),
        P.run σ = .ok o ∧ run a.code m = .ok mid 0 ∧
        MappedOutput a (L + Evm.Prog.pushes P) frame base σ m o.st mid mb ∧
        d.Input (L + Evm.Prog.pushes P) frame mb o.st mid ∧
        ((TerminalFailure Q o.st ∧ run d.code mid = .revert) ∨
          ∃ (u : Solidity.Out C o.st.H Ξ) (next : Machine) (nb : Nat → Fin W),
            Q.run o.st = .ok u ∧ run d.code mid = .ok next 0 ∧
            MappedOutput d ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
              frame mb o.st mid u.st next nb ∧
            e.Input ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q) frame nb u.st next ∧
            TerminalFailure R u.st ∧ run e.code next = .revert) := by
  simpa only [List.append_assoc] using compilation_triple_revert_witness_iff a d e hi ad de hp hq hr

/-- Intrinsic program equality and actual target associativity apply also
to the witnessed revert boundary, with no replacement source evaluator. -/
theorem revert_associations
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    (σ : State C Γ) (m : Machine) :
    ((P.join Q).join R).run σ = (P.join (Q.join R)).run σ ∧
    (run ((a.code ++ d.code) ++ e.code) m = .revert ↔
      run (a.code ++ (d.code ++ e.code)) m = .revert) := by
  exact ⟨(compilation_sequence_associative a d e σ m).1,
    by rw [List.append_assoc]⟩

end Solidity.Backend.Passes
