import Solidity.Backend.Passes.RevertWitness

/-! Further independent internal composition: the actual joined intrinsic
program's coarse failure, using its existing no-panic-without-assert theorem.
No public failure bytes or session semantics are supplied. -/
namespace Solidity.Backend.Passes
open Solidity.Evm Solidity.Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ Ω : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ} {R : Prog C Ξ Ω}

theorem joined_halt_iff (σ : State C Γ) (halt : THalt) :
    (P.join Q).run σ = .error halt ↔
      P.run σ = .error halt ∨ ∃ o, P.run σ = .ok o ∧ Q.run o.st = .error halt := by
  rw [DeferredSource.join_run]
  constructor
  · intro h
    cases hs : P.run σ with
    | error err =>
      have he : err = halt := Except.error.inj (by simpa only [TRun.seq, hs] using h)
      cases he
      exact .inl rfl
    | ok o =>
      refine .inr ⟨o, rfl, ?_⟩
      cases hq : Q.run o.st with
      | error err =>
        have he : err = halt := Except.error.inj (by simpa only [TRun.seq, hs, hq, Except.map] using h)
        cases he
        rfl
      | ok u => simp only [TRun.seq, hs, hq, Except.map, reduceCtorEq] at h
  · rintro (hs | ⟨o, hs, hq⟩)
    · simp only [TRun.seq, hs]
    · simp only [TRun.seq, hs, hq, Except.map]

/-- The asserts guard is DERIVED from independent source semantics when
panic actually occurs; it is not deleted from TerminalFailure. -/
theorem terminal_failure_errors_iff (σ : State C Γ) :
    TerminalFailure P σ ↔ P.run σ = .error .revert ∨ P.run σ = .error .panic := by
  constructor
  · rintro (hs | ⟨_, hs⟩)
    · exact .inl hs
    · exact .inr hs
  · rintro (hs | hs)
    · exact .inl hs
    · refine .inr ⟨?_, hs⟩
      cases hp : P.asserts with
      | false => exact ((Prog.run_ne_panic hp σ) hs).elim
      | true => rfl

theorem joined_terminal_failure_iff (σ : State C Γ) :
    TerminalFailure (P.join Q) σ ↔ TerminalFailure P σ ∨
      ∃ o, P.run σ = .ok o ∧ TerminalFailure Q o.st := by
  rw [terminal_failure_errors_iff]
  constructor
  · rintro (hs | hs)
    · rcases (joined_halt_iff σ .revert).mp hs with hp | ⟨o, hp, hq⟩
      · exact .inl (.inl hp)
      · exact .inr ⟨o, hp, .inl hq⟩
    · rcases (joined_halt_iff σ .panic).mp hs with hp | ⟨o, hp, hq⟩
      · exact .inl ((terminal_failure_errors_iff σ).mpr (.inr hp))
      · exact .inr ⟨o, hp, (terminal_failure_errors_iff o.st).mpr (.inr hq)⟩
  · rintro (hp | ⟨o, hp, hq⟩)
    · rcases (terminal_failure_errors_iff σ).mp hp with h | h
      · exact .inl ((joined_halt_iff σ .revert).mpr (.inl h))
      · exact .inr ((joined_halt_iff σ .panic).mpr (.inl h))
    · rcases (terminal_failure_errors_iff o.st).mp hq with h | h
      · exact .inl ((joined_halt_iff σ .revert).mpr (.inr ⟨o, hp, h⟩))
      · exact .inr ((joined_halt_iff σ .panic).mpr (.inr ⟨o, hp, h⟩))

/-- The exact actual joined source program, not just reached-case syntax. -/
theorem compilation_mapped_join_revert_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m) (ad : MappedBoundaryLink a d L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false) :
    run (a.code ++ d.code) m = .revert ↔ TerminalFailure (P.join Q) σ :=
  (compilation_mapped_revert_iff a d hi ad hp hq).trans (joined_terminal_failure_iff σ).symm

theorem compilation_triple_join_revert_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m)
    (ad : MappedBoundaryLink a d L frame base σ m)
    (de : ReachedMappedLink a d e L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false) :
    (run (a.code ++ (d.code ++ e.code)) m = .revert ↔ TerminalFailure (P.join (Q.join R)) σ) ∧
    (run ((a.code ++ d.code) ++ e.code) m = .revert ↔ TerminalFailure ((P.join Q).join R) σ) := by
  have hj : TerminalFailure (P.join (Q.join R)) σ ↔
      TerminalFailure P σ ∨ ∃ o, P.run σ = .ok o ∧
        (TerminalFailure Q o.st ∨ ∃ u, Q.run o.st = .ok u ∧ TerminalFailure R u.st) := by
    rw [joined_terminal_failure_iff]
    simp only [joined_terminal_failure_iff]
  have h := (compilation_triple_revert_iff a d e hi ad de hp hq hr).trans hj.symm
  exact ⟨h, by simpa only [List.append_assoc, typed_sequencing_assoc] using h⟩

end Solidity.Backend.Passes
