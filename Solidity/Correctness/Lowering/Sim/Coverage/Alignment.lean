import Solidity.Correctness.Lowering.Sim.Match

/-!
# Alignment from the existing spelling relation

A prerequisite for `Solidity.Goals.loweringBySimulation`.

This supplies the context-map part of coverage independently of the H117
restriction choice. It reuses the decoder owner’s primitive-locals theorem;
no decoder, association premise, or restricted totality statement is added.
-/
namespace Solidity.Correctness.Lowering.Sim.Coverage

/-- Actual Source spelling supplies an aligned map in the request context. -/
theorem spells_aligned {r : Total.Request} {s : Total.SourceProgram}
    (h : Total.Spells r s) :
    ∃ m : Solidity.Lowering.V07.ContextMap s.before r.context.ctx, Aligned m := by
  obtain ⟨plain, C, L, b, L', d, _, hL, _, rfl⟩ := h
  obtain ⟨contract, input, callee⟩ := r
  have none : callee = none := by
    simp only [Total.Decode.plain, Bool.and_eq_true, Option.isNone_iff_eq_none] at plain
    exact plain.1.1.1
  subst none
  obtain ⟨ps, hs, hm⟩ := Total.Simulation.locals_primitive _ _
    ((Total.Decode.locals_tables1 _).symm.trans hL)
  have key : ∀ {srcΓ : Source.RCtx} {Γ : Ctx},
      srcΓ = Source.Agreement.sourceContext ps → Γ = Source.Agreement.modelContext ps →
      ∃ m : Solidity.Lowering.V07.ContextMap srcΓ Γ, Aligned m := by
    intro srcΓ Γ e e'
    subst e e'
    exact ⟨Total.Simulation.primitiveMap ps, aligned_primitiveMap ps⟩
  exact key hs (hm input.names)

end Solidity.Correctness.Lowering.Sim.Coverage
