import Solidity.Backend.Passes.Sequence
import Solidity.Backend.Passes.Frame
import Solidity.Backend.Passes.Controls

/-! Concrete links, fresh frames and reached failures for the staged adapters. -/
namespace Solidity.Backend.Passes.LinkedControls

open Solidity.Evm
open Solidity.Evm.Compiler
open Solidity.Evm.Memory
open Solidity.Backend.Passes.Controls
open Solidity.Backend.Passes.Controls.Fixture

theorem assertion_source :
    (assertion true).run σ = .ok ⟨σ, List.prefix_refl _⟩ := by rfl

/-- The physical boundary obligation is actually discharged for the
core-only assertion followed by the populated memory stage. -/
theorem concrete_link (tail : List Word) :
    BoundaryLink (assertionCompiled true) memoryCompiled 1 4 base base
      σ {machine with stack := tail} := by
  intro o m' hs ht _
  have ho : o = ⟨σ, List.prefix_refl _⟩ := Except.ok.inj (hs.symm.trans assertion_source)
  have hm : {machine with stack := tail} = m' :=
    (Evm.Out.ok.inj ((assertion_run _).symm.trans ht)).1
  cases ho
  cases hm
  exact compilation_input_stack memoryCompiled memory_input tail

/-- Instantiate the general sequencing proof, retaining *both* branch
representations rather than erasing the core prefix from the certificate. -/
theorem linked_success (tail : List Word) :
    ∃ m' m'',
      run stagedCode {machine with stack := tail} = .ok m'' 0 ∧
      m''.stack = tail ∧
      (assertionCompiled true).Rep 1 4 base
        σ {machine with stack := tail} σ m' ∧
      memoryCompiled.Rep 1 4 base σ m' sourceOutput.st m'' := by
  have hi : (assertionCompiled true).Input 1 4 base σ
      {machine with stack := tail} :=
    ⟨fixture_repr.core.stack tail, fixture_repr.core.bound⟩
  obtain ⟨m', m'', _, _, ht, hstack, hr, hr'⟩ :=
    compilation_sequence_success (assertionCompiled true) memoryCompiled
      hi (concrete_link tail) rfl rfl assertion_source source_success
  exact ⟨m', m'', ht, hstack, hr, hr'⟩

private theorem base_ge_sixteen (id : Nat) : 16 ≤ (base id).val := by
  unfold base
  split <;> decide +kernel

/-- Two additional local slots are reserved below both populated objects.
This is an inhabited frame change, not a frame bound assumed without slack. -/
theorem frame_six : StateRepr 1 0 6 (Frag.init Γ) σ base machine :=
  memory_frame fixture_repr (by decide +kernel)
    (fun r => Nat.le_trans (by decide +kernel) (base_ge_sixteen r.id))
    (fun r => Nat.le_trans (by decide +kernel) (base_ge_sixteen r.id))

/-- An actual fresh typed value occupies the reserved slot and coexists
with arbitrary saved tails and the original aliasing heap. -/
theorem fresh_value (tail : List Word) :
    StateRepr 1 0 6 ((Frag.init Γ).push (.val .uint) .ok)
      (σ.push (t := .val .uint) (CompileExamples.uint 11 (by decide)))
      base (writeMachine {machine with stack := tail} 4 w[11]) :=
  memory_extend_value fixture_repr (CompileExamples.uint 11 (by decide)) w[11] ⟨⟨11, by decide⟩, rfl, rfl⟩
    (by decide +kernel)
    (fun r => Nat.le_trans (by decide +kernel) (base_ge_sixteen r.id))
    (fun r => Nat.le_trans (by decide +kernel) (base_ge_sixteen r.id)) tail

/-- Reserving across an occupied heap header is impossible: frame growth
needs the separation premise even though the locals themselves would fit. -/
theorem frame_seventeen_impossible :
    ¬ StateRepr 1 0 17 (Frag.init Γ) σ base machine := by
  intro h
  have hbad := h.heap.above CompileExamples.r0
  change 17 ≤ 16 at hbad
  omega

/-- A reachable failure in the right memory stage is not hidden by a
successful core prefix; this is a distinct side of the failure transport. -/
theorem right_stage_reverts :
    run ((assertionCompiled true).code ++ CompileExamples.checkedBadRhs.code) machine =
      .revert := by
  rw [run_append_ok (assertion_run _)]
  exact Evm.Out.eq_revert (by decide +kernel)

/-- An actual source panic in the left stage short-circuits a memory
suffix, including every saved tail. This is coarse internal panic/revert
agreement, not equality of public ABI observations. -/
theorem left_stage_failure (tail : List Word) :
    (assertion false).run σ = .error .panic ∧
      run ((assertionCompiled false).code ++ memoryCompiled.code)
        {machine with stack := tail} = .revert :=
  ⟨rfl, run_append_revert rfl⟩

/-- The right-stage control also has an actual independent source revert. -/
theorem right_stage_source_revert : CompileExamples.badRhsRead.run σ = .error .revert := by
  with_unfolding_all rfl

end Solidity.Backend.Passes.LinkedControls
