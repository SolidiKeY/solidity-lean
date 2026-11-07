import Solidity.Assurance.NonVacuityH28.CheckedObjects

/-! A positive-cost allocator output queried at an actual input cursor. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics
variable (C : Contract)

theorem construction_allocator_growth :
    ∃ m : Evm.Machine, ∃ base : Nat → Fin Evm.W,
      Evm.run (constructionCompiled C).code memoryMachine = .ok m 0 ∧
      m.stack = memoryMachine.stack ∧
      Evm.Memory.Objects.StateRepr 1 1 128 (constructionResult C).frag
        (primitiveOutcome C).st base m ∧
      Evm.Memory.Objects.AllocatorRepr (primitiveOutcome C).st.heap base 128
        ⟨258, by decide +kernel⟩ m := by
  obtain ⟨m, ht, hstack, hr⟩ := checked_success_after_source (constructionCompiled C)
    (construction_input C) rfl (primitive_source_eq C)
  obtain ⟨base, hstate, _, hgrow⟩ := hr
  have hspace : (Evm.wmod 256).val + 2 < Evm.W := by decide +kernel
  have hg := hgrow (Evm.wmod 256) (by decide) (fresh_object_allocator C) hspace
  exact ⟨m, base, ht, hstack, hstate, hg⟩

/-- The legacy memory path's distinct allocator contract is queried too;
object ownership is not substituted for its weaker universal input. -/
theorem primitive_allocator_growth :
    ∃ m : Evm.Machine, ∃ base : Nat → Fin Evm.W,
      Evm.run (primitiveCompiled C).code memoryMachine = .ok m 0 ∧
      Evm.Memory.StructAllocatorRepr (primitiveOutcome C).st.heap base 128
        ⟨258, by decide +kernel⟩ m := by
  obtain ⟨m, ht, _, hr⟩ := checked_success_after_source (primitiveCompiled C)
    (primitive_input C) rfl (primitive_source_eq C)
  obtain ⟨base, _, _, hgrow⟩ := hr
  have hspace : (Evm.wmod 256).val + 2 < Evm.W := by decide +kernel
  have hg := hgrow (Evm.wmod 256) (by decide) (fresh_object_allocator C).legacy hspace
  exact ⟨m, base, ht, hg⟩

theorem construction_cursor_observation :
    ∃ m : Evm.Machine, Evm.run (constructionCompiled C).code memoryMachine = .ok m 0 ∧
      memoryMachine.mem 0 = .val (Evm.wmod 256) ∧ m.mem 0 = .val (Evm.wmod 258) := by
  obtain ⟨m, _, ht, _, _, ha⟩ := construction_allocator_growth C
  exact ⟨m, ht, rfl, ha.free.cell⟩

theorem construction_cursor_erasure_rejected :
    ∃ m : Evm.Machine, Evm.run (constructionCompiled C).code memoryMachine = .ok m 0 ∧
      m.mem 0 ≠ Evm.Word.val (Evm.wmod 0) := by
  obtain ⟨m, ht, _, hc⟩ := construction_cursor_observation C
  refine ⟨m, ht, ?_⟩
  intro hz
  have he : Evm.Word.val (Evm.wmod 258) = .val (Evm.wmod 0) := hc.symm.trans hz
  have hn : (Evm.wmod 258).val = (Evm.wmod 0).val := congrArg Fin.val (Evm.Word.val.inj he)
  change 258 = 0 at hn
  cases hn

end Solidity.Assurance.NonVacuityH28
