import Solidity.Backend.Passes.Frame

/-!
# Value-certificate adapters over published intrinsic expression semantics

The existing CompiledVal certificate chooses the code. These adapters neither
select scalar/environment instructions nor extend their supported families.
They preserve the exact typed value and entire machine below the result word.
-/
namespace Solidity.Backend.Passes

open Solidity.Evm
open Solidity.Evm.Memory
variable {C : Contract} {b L frame : Nat} {Γ : Ctx} {F : Frag Γ}
  {p : PrimTy} {e : Val C Γ p} {σ : State C Γ}
  {base : Nat → Fin W} {m : Machine}

/-- A typed successful expression pushes exactly one representing word over
any saved tail, leaving every non-stack machine component unchanged. -/
theorem value_success_tail (result : CompiledVal b F e)
    (hi : StateRepr L b frame F σ base m)
    {value : p.Denote} (hs : e.evalT σ = .ok value) (tail : List Word) :
    ∃ word, ReprV p value word ∧
      run result.code {m with stack := tail} =
        .ok ({m with stack := tail}.push word) 0 := by
  rcases result.cert.correct (hi.stack tail) with
    ⟨value', word, hs', hw, ht⟩ | ⟨hs', _⟩
  · have hv : value' = value := Except.ok.inj (hs'.symm.trans hs)
    cases hv
    exact ⟨word, hw, ht⟩
  · rw [hs] at hs'
    cases hs'

/-- For the published expression fragment, both directions of revert
transport hold with an arbitrary saved tail and no lost state relation. -/
theorem value_revert_iff (result : CompiledVal b F e)
    (hi : StateRepr L b frame F σ base m) (tail : List Word) :
    run result.code {m with stack := tail} = .revert ↔ e.evalT σ = .error .revert := by
  have h := result.cert.correct (hi.stack tail)
  constructor
  · intro ht
    rcases h with ⟨_, _, _, _, ht'⟩ | ⟨hs, _⟩
    · rw [ht] at ht'
      cases ht'
    · exact hs
  · intro hs
    rcases h with ⟨_, _, hs', _, _⟩ | ⟨_, ht⟩
    · rw [hs] at hs'
      cases hs'
    · exact ht

end Solidity.Backend.Passes
