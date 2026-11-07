import Solidity.Evm.Compiler
import Solidity.Backend.Payments.CoreExact

/-!
# G43: the checked compiler entry agrees exactly

`Compiler.Compilation.Agrees` (`Solidity/Evm/Compiler.lean`) keeps two
payment disjuncts: a typed run that succeeds while the machine reverts, and
a divergence the machine meets with a payment revert, both under
`Prog.pays P`. `AgreesExact` is `Agrees` without them, and `correct_exact`
proves it for every `Compilation` under the same `Input`: the core path by
`Payments.compile_paid`, every memory path by its certificate, none of which
produces a payment outcome.

`compile_success` is the separate compiler-success theorem G43 needs
(OBL-SUCCESS): for every compilation result and every input it accepts, a
typed run that succeeds is matched by a machine run that succeeds, in the
state `Rep` relates. On the core path the payment agreement is `Input`'s
`Sim.funds` and the premise `Sim.oracle`; the memory compilers reject
`transfer`/`send`, and their certificates have no payment outcome. `Agrees`, `correct` and every frozen statement are
unchanged; `agrees_of_exact` recovers `Agrees` from `AgreesExact`.
-/

namespace Solidity.Evm.Compiler

variable {C : Contract}

namespace Compilation

/-- `Agrees` without the payment disjuncts: both succeed in related states,
both revert, or the typed run diverges and the machine faults. -/
def AgreesExact {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (L frame : Nat) (base : Nat → Fin W)
    (σ : State C Γ) (m : Machine) : Prop :=
  (∃ o m', P.run σ = .ok o ∧ run result.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
    result.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m') ∨
  ((P.run σ = .error .revert ∨ (P.asserts = true ∧ P.run σ = .error .panic)) ∧
    run result.code m = .revert) ∨
  (P.run σ = .error .diverge ∧ run result.code m = .fault)

/-- `AgreesExact` is the stronger statement. -/
theorem agrees_of_exact {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    {result : Compilation b F P} {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (h : result.AgreesExact L frame base σ m) : result.Agrees L frame base σ m := by
  rcases h with h | h | ⟨h1, h2⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inr ⟨h1, .inl h2⟩))

/-- **The checked compiler agrees exactly** (G43): every compilation result,
under its `Input`, satisfies `AgreesExact`; no payment outcome remains. -/
theorem correct_exact {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (h : result.Input L frame base σ m) : result.AgreesExact L frame base σ m := by
  cases result with
  | core out cert => exact Payments.compile_paid cert h.1 h.2
  | memory out =>
    simp only [AgreesExact, code, Rep, out.cert.pushes_zero, Nat.add_zero]
    rcases out.cert.correct h.1 h.2.1 h.2.2 with
      ⟨o, m', base', ho, hc, hm, hst, he, ha⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, base', hm, he, ha⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)
  | referenceArrays out =>
    simp only [AgreesExact, code, Rep, out.cert.pushes_zero, Nat.add_zero]
    rcases out.cert.correct h with ⟨o, m', ho, hc, hm, hst⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, hm⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)
  | objects out =>
    simp only [AgreesExact, code, Rep, out.cert.pushes_zero, Nat.add_zero]
    rcases out.cert.correct h.1 h.2 with ⟨o, m', ho, hc, hm, hst, ha⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, hm, ha⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)
  | construction out =>
    simp only [AgreesExact, code, Rep, out.cert.pushes_zero, Nat.add_zero]
    rcases out.cert.correct h.1 h.2.1 h.2.2 with
      ⟨o, m', base', ho, hc, hm, hst, he, ha⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, base', hm, he, ha⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)
  | memoryLoops out =>
    simp only [AgreesExact, code, Rep, out.cert.pushes_zero, Nat.add_zero]
    rcases out.cert.correct h.1 h.2.1 h.2.2 with
      ⟨o, m', base', cost, ho, hc, hcost, hm, hst, he, ha⟩ | ⟨ho, hc⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, base', cost, o.ext, hcost, hm, he, ha⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)
    · exact .inr (.inr ⟨ho, hc⟩)
  | memoryLoopScopes out =>
    simp only [AgreesExact, code, Rep, out.cert.pushes_zero, Nat.add_zero]
    rcases out.cert.correct σ base m h.1 h.2.1 h.2.2 with
      ⟨o, m', base', cost, ho, hc, hcost, hm, hst, he, ha⟩ | ⟨ho, hc⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, base', cost, o.ext, hcost, hm, he, ha⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)
    · exact .inr (.inr ⟨ho, hc⟩)
  | memoryCalls out hz =>
    simp only [AgreesExact, code, Rep, hz, Nat.add_zero]
    rcases out.sound h.1 h.2.1 h.2.2 with
      ⟨o, m', base', ho, hc, hm, hst, he, ha⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, base', hm, he, ha⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)
  | memoryCopy out =>
    simp only [AgreesExact, code, Rep, out.cert.pushes_zero, Nat.add_zero]
    rcases out.cert.correct h.1 h.2.1 h.2.2.1 h.2.2.2 with
      ⟨o, m', base', ho, hc, hm, hst, he, ha⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, base', hm, he, ha⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)
  | fixedMemory out =>
    simp only [AgreesExact, code, Rep, out.cert.pushes_zero, Nat.add_zero]
    rcases out.cert.correct h.1 h.2 with
      ⟨o, m', ho, hc, hm, hst, hmem, hH, hheap⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, hm, hmem, hH, hheap⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)
  | copyConstruction out =>
    simp only [AgreesExact, code, Rep, out.cert.pushes_zero, Nat.add_zero, frag]
    rcases out.cert.correct h.1 h.2.1 h.2.2.1 h.2.2.2 with
      ⟨o, m', base', ho, hc, hm, hst, he, ha⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, base', hm, he, ha⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)

/-- **Compiler success** (G43, OBL-SUCCESS), over every compilation result:
a typed run that succeeds from an accepted input is matched by a machine run
that succeeds, its stack as it was, in the state `Rep` relates. -/
theorem compile_success {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (h : result.Input L frame base σ m) {o : Solidity.Out C σ.H Δ} (ho : P.run σ = .ok o) :
    ∃ m', run result.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
      result.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m' := by
  rcases correct_exact result h with ⟨o', m', h1, h2, h3, h4⟩ | ⟨h1 | ⟨-, h1⟩, -⟩ | ⟨h1, -⟩
  · rw [ho] at h1
    cases h1
    exact ⟨m', h2, h3, h4⟩
  all_goals (rw [ho] at h1; cases h1)

/-- The machine reverts only where the typed run reverts or panics. -/
theorem revert_exact {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (h : result.Input L frame base σ m) (hr : run result.code m = .revert) :
    P.run σ = .error .revert ∨ (P.asserts = true ∧ P.run σ = .error .panic) := by
  rcases correct_exact result h with ⟨_, _, -, h2, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
  · rw [hr] at h2; cases h2
  · exact h1
  · rw [hr] at h2; cases h2

end Compilation
end Solidity.Evm.Compiler

/-! ## Axioms: Lean's three -/

/-- info: 'Solidity.Evm.Compiler.Compilation.correct_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Evm.Compiler.Compilation.correct_exact

/-- info: 'Solidity.Evm.Compiler.Compilation.compile_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Evm.Compiler.Compilation.compile_success

/-- info: 'Solidity.Evm.Payments.compile_paid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Evm.Payments.compile_paid

/-- info: 'Solidity.Evm.Payments.compile_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Evm.Payments.compile_success
