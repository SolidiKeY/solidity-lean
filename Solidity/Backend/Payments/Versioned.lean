import Solidity.Backend.Payments.CompilerExact
import Solidity.Evm.Examples

/-!
# G43 V2 headlines: the compiler agreement with no payment disjunct

The versioned pair (H57, user decision H98) for the frozen compiler headlines
that still list the outcome "the typed run succeeds, the machine alone reverts
at a refused payment": `Compiler.Compilation.Agrees`/`correct` and
`Evm.compile_correct`. The frozen statements are unchanged; their V2
counterparts stand beside them, under the same premises:

- `Compiler.CompilationV2.Agrees`/`correct` (from `Compilation.correct_exact`),
- `Evm.compile_correct_v2` (from `Payments.compile_paid`),

and each has a migration lemma deriving the frozen statement from V2
(`CompilationV2.agrees_frozen`, `CompilationV2.correct_frozen`,
`Evm.compile_correct_of_v2`), so a consumer moves to V2 without losing
anything it used. `Solidity/Backend/Payments/Headlines.lean` does the same for
`Theorems.compiler_correct`/`compiler_checked`.

Controls: `paying_premises` is a joint-satisfiability witness (a program that
pays, in the fragment, from a fresh contract a machine represents, within the
bounds), so V2 is not vacuous on paying code; `refusing_world_not_sim` is a
negative control: a machine whose `accepts` refuses while the typed world
records no refusal is not represented (`Sim.oracle`), so V2 never applies to
the mismatched worlds where the frozen payment disjunct would be inhabited.
Migration notes for the consumers of that disjunct are in
`docs/feature-work/v14-g43.md`.
-/

namespace Solidity.Evm

open Solidity (Ctx State)

variable {C : Contract}

namespace Compiler.CompilationV2

/-- **V2 agreement**: both succeed in related states, both revert, or the
typed run diverges and the machine faults (`Compilation.AgreesExact`). -/
abbrev Agrees {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Solidity.Prog C Γ Δ}
    (result : Compiler.Compilation b F P) (L frame : Nat) (base : Nat → Fin W)
    (σ : State C Γ) (m : Machine) : Prop :=
  result.AgreesExact L frame base σ m

/-- **V2 of `Compilation.correct`**: under the same `Input`, V2 agreement. -/
theorem correct {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Solidity.Prog C Γ Δ}
    (result : Compiler.Compilation b F P) {base : Nat → Fin W} {σ : State C Γ}
    {m : Machine} (h : result.Input L frame base σ m) :
    Agrees result L frame base σ m :=
  result.correct_exact h

/-- Migration: V2 agreement gives the frozen `Compilation.Agrees`. -/
theorem agrees_frozen {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Solidity.Prog C Γ Δ}
    {result : Compiler.Compilation b F P} {base : Nat → Fin W} {σ : State C Γ}
    {m : Machine} (h : Agrees result L frame base σ m) : result.Agrees L frame base σ m :=
  Compiler.Compilation.agrees_of_exact h

/-- Migration: the frozen `Compilation.correct` statement, from V2. -/
theorem correct_frozen {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Solidity.Prog C Γ Δ}
    (result : Compiler.Compilation b F P) {base : Nat → Fin W} {σ : State C Γ}
    {m : Machine} (h : result.Input L frame base σ m) : result.Agrees L frame base σ m :=
  agrees_frozen (correct result h)

end Compiler.CompilationV2

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

/-- Under V2's premises the frozen payment disjunct is never inhabited. -/
theorem payment_disjunct_empty {P : Solidity.Prog C Γ Γ'} (hP : inFragP F P = some F')
    (hm : Sim C L b F σ m) (hL : L + Prog.pushes P ≤ Lmax) :
    ¬ (run (compileProg b P) m = .revert ∧ ∃ o, Solidity.Prog.run σ P = .ok o) := by
  rintro ⟨hr, o, ho⟩
  rcases Payments.compile_revert hP hm hL hr with h | ⟨-, h⟩ <;> rw [ho] at h <;> cases h

end Core

/-! ## Controls -/

namespace PaymentControls

open Solidity.Evm.Examples (payOwner)

/-- **Joint satisfiability**: `owner = 5; owner.transfer(30);` pays, is in the
fragment, and every fresh contract (any balance below `2^256`, any world
balances, any address) is represented by the fresh machine within the bounds,
so `compile_correct_v2`'s premises hold together for paying code. -/
theorem paying_premises (balance : Nat) (hb : balance < W) (bal : Fin W → Nat)
    (self : Fin W) (hbalance : balance = bal self) :
    ∃ F', inFragP (Frag.init []) payOwner = some F' ∧ Prog.pays payOwner = true ∧
      Sim StandardExample 1 0 (Frag.init []) (freshT StandardExample balance hb self)
        (Machine.init bal self) ∧ 1 + Prog.pushes payOwner ≤ Lmax := by
  have hc : (inFragP (Frag.init []) payOwner).isSome = true := by decide +kernel
  obtain ⟨F', hF'⟩ := Option.isSome_iff_exists.mp hc
  exact ⟨F', hF', by decide +kernel, Sim.init StandardExample balance hb bal self hbalance,
    by decide +kernel⟩

/-- **Negative control**: a machine whose world refuses every payment while
the fresh typed world records no refusal is not represented: `Sim.oracle`
fails, so V2 (and `compile_correct`) never speak about it. This is the
mismatch under which the frozen payment disjunct could be inhabited. -/
theorem refusing_world_not_sim (balance : Nat) (hb : balance < W) (bal : Fin W → Nat)
    (self : Fin W) :
    ¬ Sim C 1 0 (Frag.init []) (freshT C balance hb self)
      { Machine.init bal self with accepts := fun _ _ => false } := by
  intro h
  have := h.oracle (uintT 0 (by decide)) (uintT 0 (by decide)) ⟨0, by decide⟩ ⟨0, by decide⟩
    rfl rfl
  simp only [freshT] at this
  cases this

end PaymentControls

end Solidity.Evm
