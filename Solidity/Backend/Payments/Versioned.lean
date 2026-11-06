import Solidity.Backend.Payments.CompilerExact

/-!
# G43 V2 headlines: the compiler agreement with no payment disjunct

The versioned pair (H57, user decision H98) for the frozen compiler headlines
that still list the outcome "the typed run succeeds, the machine alone reverts
at a refused payment": `Compiler.Compilation.Agrees`/`correct` and
`Evm.compile_correct`. The frozen statements are unchanged; their V2
counterparts stand beside them, under the same premises:

- `Compiler.Compilation.AgreesV2`/`correct_v2` (from `Compilation.correct_exact`;
  dot notation `result.correct_v2` works),
- `Evm.compile_correct_v2` (from `Payments.compile_paid`),

and each has a migration lemma deriving the frozen statement from V2
(`Compilation.agrees_of_v2`, `Compilation.correct_of_v2`,
`Evm.compile_correct_of_v2`), so a consumer moves to V2 without losing
anything it used. `Solidity/Backend/Payments/Headlines.lean` does the same for
`Theorems.compiler_correct`/`compiler_checked`.

`payment_disjunct_empty` and `diverge_revert_empty` show both payment
branches of the frozen statements are empty under V2's premises. The
witnesses and controls are in `Backend/Payments/VersionedControls.lean`, so
this module imports no examples or elaborator.
Migration notes for the consumers of that disjunct are in
`docs/feature-work/v14-g43.md`.
-/

namespace Solidity.Evm

open Solidity (Ctx State)

variable {C : Contract}

namespace Compiler.Compilation

/-- **V2 agreement**: both succeed in related states, both revert, or the
typed run diverges and the machine faults (`Compilation.AgreesExact`). -/
abbrev AgreesV2 {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Solidity.Prog C Γ Δ}
    (result : Compiler.Compilation b F P) (L frame : Nat) (base : Nat → Fin W)
    (σ : State C Γ) (m : Machine) : Prop :=
  result.AgreesExact L frame base σ m

/-- **V2 of `Compilation.correct`**: under the same `Input`, V2 agreement. -/
theorem correct_v2 {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Solidity.Prog C Γ Δ}
    (result : Compiler.Compilation b F P) {base : Nat → Fin W} {σ : State C Γ}
    {m : Machine} (h : result.Input L frame base σ m) :
    result.AgreesV2 L frame base σ m :=
  result.correct_exact h

/-- Migration: V2 agreement gives the frozen `Compilation.Agrees`. -/
theorem agrees_of_v2 {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Solidity.Prog C Γ Δ}
    {result : Compiler.Compilation b F P} {base : Nat → Fin W} {σ : State C Γ}
    {m : Machine} (h : result.AgreesV2 L frame base σ m) : result.Agrees L frame base σ m :=
  Compiler.Compilation.agrees_of_exact h

/-- Migration: the frozen `Compilation.correct` statement, from V2. -/
theorem correct_of_v2 {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Solidity.Prog C Γ Δ}
    (result : Compiler.Compilation b F P) {base : Nat → Fin W} {σ : State C Γ}
    {m : Machine} (h : result.Input L frame base σ m) : result.Agrees L frame base σ m :=
  agrees_of_v2 (correct_v2 result h)

end Compiler.Compilation

section Core

variable {L b : Nat} {Γ Γ' : Ctx} {F : Frag Γ} {F' : Frag Γ'} {σ : State C Γ}
  {m : Machine}

/-- **V2 of `compile_correct`**: the frozen premises, no payment disjunct. -/
theorem compile_correct_v2 {P : Solidity.Prog C Γ Γ'} (hP : inFragP F P = some F')
    (hm : Sim C L b F σ m) (hL : L + Prog.pushes P ≤ Lmax) :
    (∃ o m', Solidity.Prog.run σ P = .ok o ∧ run (compileProg b P) m = .ok m' 0 ∧
      m'.stack = m.stack ∧ Sim C (L + Prog.pushes P) b F' o.st m') ∨
    ((Solidity.Prog.run σ P = .error .revert ∨
        (Prog.asserts P = true ∧ Solidity.Prog.run σ P = .error .panic)) ∧
      run (compileProg b P) m = .revert) ∨
    (Solidity.Prog.run σ P = .error .diverge ∧ run (compileProg b P) m = .fault) :=
  Payments.compile_paid hP hm hL

/-- Migration: the frozen `compile_correct` statement, from V2. -/
theorem compile_correct_of_v2 {P : Solidity.Prog C Γ Γ'} (hP : inFragP F P = some F')
    (hm : Sim C L b F σ m) (hL : L + Prog.pushes P ≤ Lmax) :
    (∃ o m', Solidity.Prog.run σ P = .ok o ∧ run (compileProg b P) m = .ok m' 0 ∧
      m'.stack = m.stack ∧ Sim C (L + Prog.pushes P) b F' o.st m') ∨
    ((Solidity.Prog.run σ P = .error .revert ∨
        (Prog.asserts P = true ∧ Solidity.Prog.run σ P = .error .panic)) ∧
      run (compileProg b P) m = .revert) ∨
    (Prog.pays P = true ∧ run (compileProg b P) m = .revert ∧ ∃ o m',
      Solidity.Prog.run σ P = .ok o ∧
      Sim C (L + Prog.pushes P) b F' o.st m') ∨
    (Solidity.Prog.run σ P = .error .diverge ∧ (run (compileProg b P) m = .fault ∨
      (Prog.pays P = true ∧ run (compileProg b P) m = .revert))) := by
  rcases compile_correct_v2 hP hm hL with h | h | ⟨h1, h2⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inr ⟨h1, .inl h2⟩))

/-- Under V2's premises the frozen success-side payment disjunct (machine
reverts, typed run succeeds) is never inhabited. -/
theorem payment_disjunct_empty {P : Solidity.Prog C Γ Γ'} (hP : inFragP F P = some F')
    (hm : Sim C L b F σ m) (hL : L + Prog.pushes P ≤ Lmax) :
    ¬ (run (compileProg b P) m = .revert ∧ ∃ o, Solidity.Prog.run σ P = .ok o) := by
  rintro ⟨hr, o, ho⟩
  rcases Payments.compile_revert hP hm hL hr with h | ⟨-, h⟩ <;> rw [ho] at h <;> cases h

/-- Under V2's premises the payment branch of the frozen divergence disjunct
is never inhabited either: a diverging typed run is met by a fault, not a
revert. -/
theorem diverge_revert_empty {P : Solidity.Prog C Γ Γ'} (hP : inFragP F P = some F')
    (hm : Sim C L b F σ m) (hL : L + Prog.pushes P ≤ Lmax) :
    ¬ (Solidity.Prog.run σ P = .error .diverge ∧ run (compileProg b P) m = .revert) := by
  rintro ⟨hd, hr⟩
  rcases compile_correct_v2 hP hm hL with ⟨_, _, h1, _⟩ | ⟨h1 | ⟨-, h1⟩, -⟩ | ⟨-, h2⟩
  · rw [hd] at h1; cases h1
  · rw [hd] at h1; cases h1
  · rw [hd] at h1; cases h1
  · rw [hr] at h2; cases h2

end Core

/-! ## Axioms: Lean's three -/

/-- info: 'Solidity.Evm.compile_correct_v2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile_correct_v2

/-- info: 'Solidity.Evm.Compiler.Compilation.correct_v2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compiler.Compilation.correct_v2

end Solidity.Evm
