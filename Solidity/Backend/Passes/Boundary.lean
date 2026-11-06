import Solidity.Evm.Compiler

/-!
# Exact terminal adapters for the checked compilation entry

These lemmas retain the selected branch's complete dependent representation.
They extend the existing core `compile_exact` to the unified entry; they do
not discharge payment freedom, panic bytes, sessions, or finite-prefix
adequacy. In particular they are not instances of Roadmap.Cert.
-/
namespace Solidity.Backend.Passes

open Solidity.Evm
open Solidity.Evm.Compiler

variable {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ}

/-- Exact terminal agreement under the existing payment-freedom premise.
The panic alternative remains explicit and is not an ABI observation. -/
theorem compilation_exact (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : result.Input L frame base σ m) (hpay : Evm.Prog.pays P = false) :
    (∃ o m', P.run σ = .ok o ∧ run result.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧
      result.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m') ∨
    ((P.run σ = .error .revert ∨ (P.asserts = true ∧ P.run σ = .error .panic)) ∧
      run result.code m = .revert) ∨
    (P.run σ = .error .diverge ∧ run result.code m = .fault) := by
  rcases result.correct hi with h | h | ⟨hp, _⟩ | ⟨hs, ht | ⟨hp, _⟩⟩
  · exact .inl h
  · exact .inr (.inl h)
  · rw [hpay] at hp
    cases hp
  · exact .inr (.inr ⟨hs, ht⟩)
  · rw [hpay] at hp
    cases hp

/-- A given successful source result has a correlated successful target,
including the original entry state, machine, base map and output fragment. -/
theorem compilation_success (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : result.Input L frame base σ m) (hpay : Evm.Prog.pays P = false)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o) :
    ∃ m', run result.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
      result.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m' := by
  rcases compilation_exact result hi hpay with
    ⟨o', m', hs', ht, hstack, hr⟩ | ⟨hs' | ⟨_, hs'⟩, _⟩ | ⟨hs', _⟩
  · have ho : o' = o := Except.ok.inj (hs'.symm.trans hs)
    cases ho
    exact ⟨m', ht, hstack, hr⟩
  · rw [hs] at hs'
    cases hs'
  · rw [hs] at hs'
    cases hs'
  · rw [hs] at hs'
    cases hs'

/-- Target success reflects the source and the same branch-specific relation.
This direction needs no payment-freedom premise. -/
theorem compilation_reflect_success (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m m' : Machine}
    (hi : result.Input L frame base σ m) (ht : run result.code m = .ok m' 0) :
    ∃ o, P.run σ = .ok o ∧ m'.stack = m.stack ∧
      result.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m' := by
  rcases result.correct hi with
    ⟨o, m'', hs, ht', hstack, hr⟩ | ⟨_, ht'⟩ | ⟨_, ht', _⟩ |
      ⟨_, ht' | ⟨_, ht'⟩⟩
  · have hm : m'' = m' := (Evm.Out.ok.inj (ht'.symm.trans ht)).1
    cases hm
    exact ⟨o, hs, hstack, hr⟩
  · rw [ht] at ht'
    cases ht'
  · rw [ht] at ht'
    cases ht'
  · rw [ht] at ht'
    cases ht'
  · rw [ht] at ht'
    cases ht'

/-- Two-sided coarse revert transport. Panic is deliberately visible in the
source predicate; no statement about exact revert bytes is made. -/
theorem compilation_revert_iff (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : result.Input L frame base σ m) (hpay : Evm.Prog.pays P = false) :
    run result.code m = .revert ↔
      P.run σ = .error .revert ∨ (P.asserts = true ∧ P.run σ = .error .panic) := by
  have h := compilation_exact result hi hpay
  constructor
  · intro ht
    rcases h with ⟨_, _, _, ht', _, _⟩ | ⟨hs, _⟩ | ⟨_, ht'⟩
    · rw [ht] at ht'
      cases ht'
    · exact hs
    · rw [ht] at ht'
      cases ht'
  · intro hs
    rcases h with ⟨_, _, hs', _, _, _⟩ | ⟨_, ht⟩ | ⟨hs', _⟩
    · rcases hs with hs | ⟨_, hs⟩ <;> rw [hs] at hs' <;> cases hs'
    · exact ht
    · rcases hs with hs | ⟨_, hs⟩ <;> rw [hs] at hs' <;> cases hs'

end Solidity.Backend.Passes
