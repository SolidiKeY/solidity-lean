import Solidity.Correctness.Lowering.Sim.Coverage.BooleanDecoding
import Solidity.Correctness.Lowering.Sim.Coverage.ProductionV2
import Solidity.Correctness.Lowering.Sim.Coverage.Alignment

/-! The additive H1184 coverage boundary selected by H1361, toward
`Solidity.Goals.loweringBySimulation`. Frozen Diagram.Total and its checked
obstructions are unchanged. An actual production nonvacuity receipt remains
separate from the static Source decoding and association proved here. -/
namespace Solidity.Correctness.Lowering.Sim.Coverage

open Solidity.Goals.Shrink.Lowering

/-- An approved Boolean input has a resolved body with exactly the same
production input. Caller placement is the existing H1182 v2 contract. -/
theorem BooleanDomain.Input.associated {b u} (h : BooleanDomain.Input b u)
    (placed : ThreadedV2 b u) :
    ∃ b' : Body, b'.SameInput b ∧ ∃ m, diagram.Assoc b' u m := by
  obtain ⟨C, L, s, d, decoded⟩ := h.decoded_stmt
  let b' : Body :=
    { E := C.env, returns := C.rets, modifier := C.inModifier, control := .body,
      ctx := Source.tysOf L,
      input :=
        { raw := b.input.raw, resolved := d.toR, returnSlots := b.input.returnSlots,
          scope := b.input.scope, before := b.input.before },
      site := b.site }
  have spelled := Total.decode_spells decoded
  obtain ⟨m, aligned⟩ := spells_aligned spelled
  have transport : ∀ (Γ : Ctx), Γ = (request b u).context.ctx →
      ∃ m : Solidity.Lowering.V07.ContextMap b'.ctx Γ, Aligned m := by
    intro Γ same
    subst Γ
    exact ⟨m, aligned⟩
  obtain ⟨m', aligned'⟩ := transport u.Γ placed.2.1
  refine ⟨b', ⟨rfl, rfl, rfl, rfl, rfl⟩, m', placed.2.1, placed.2.2,
    aligned', Total.SourceProgram.ofStmt d.toR, spelled, ?_⟩
  simp only [Reads, b', h.1]

/-- Restricted v2 coverage: the H1361 syntax domain and H1182 production
placement, with the original acceptance predicate unchanged. This is not the
frozen all-input Diagram.Total statement. -/
def BooleanTotalV2 (D : Diagram) : Prop :=
  ∀ (b : Body) (u : Emitted), BooleanDomain.Input b u →
    @ProductionV2 productionNames b u → Accepted u →
    ∃ b' : Body, b'.SameInput b ∧ ∃ m, D.Assoc b' u m

/-- Every accepted production in the approved Boolean v2 boundary is covered.
This theorem needs no producer equations: decoding depends only on the raw
input; the actual production and acceptance hypotheses remain in the boundary. -/
theorem diagram_total_boolean : BooleanTotalV2 diagram := by
  intro b u input production _accepted
  exact input.associated production.2.2

end Solidity.Correctness.Lowering.Sim.Coverage
