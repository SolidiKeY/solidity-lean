import Solidity.Correctness.Lowering.Sim.Coverage.BooleanCoverage

/-! Additive Boolean-block coverage toward `Solidity.Goals.loweringBySimulation`.
The H2157 proposal extends the delivered Boolean domain without changing its
grammar, the owned decoder, placement, acceptance or frozen v1 statements. -/
namespace Solidity.Correctness.Lowering.Sim.Coverage

open Solidity.Goals.Shrink.Lowering

namespace BooleanBlocksV3

/-- A singleton block of the existing Boolean grammar, with the same caller
boundary as BooleanDomain.Input. Counter and memo are unrestricted. -/
def BlockInput (b : Body) (u : Emitted) : Prop :=
  b.site = .loop ∧ u.C = { vars := [] } ∧ b.input.returnSlots = none ∧
  b.input.scope = { funs := [] } ∧
  ∃ (names : List String) (ss : List RawStmt),
    b.input.before.locals.1 = names.map (fun x => (x, .val .bool)) ∧
    b.input.raw = [.block ss] ∧ BooleanDomain.Stmts names false ss

/-- The delivered domain remains included verbatim. -/
def Input (b : Body) (u : Emitted) : Prop :=
  BooleanDomain.Input b u ∨ BlockInput b u

/-- Inclusion requires no production, acceptance or decoder hypothesis. -/
theorem of_boolean {b u} (h : BooleanDomain.Input b u) : Input b u := .inl h

private theorem locals_decoded (names : List String) :
    Total.Decode.locals (names.map (fun x => (x, .val .bool))) =
      some (names.map (fun x => (x, Source.STy.bool))) := by
  induction names with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, Total.Decode.locals, Total.Decode.localTy,
      Source.Agreement.sourceTy, ih]
    rfl

/-- Completeness uses the actual Source inference and the existing decoder;
domain membership contains neither decoder success nor an association. -/
theorem BlockInput.decoded_stmt {b u} (h : BlockInput b u) :
    ∃ (C : Source.Ctx) (L : List (String × Source.STy)) (s : Source.Syn (.stmt .body))
      (d : Source.StmtD C L s L),
      Total.Decode.decode (request b u) = some (Total.SourceProgram.ofStmt d.toR) := by
  obtain ⟨site, contract, slots, scope, names, ss, locals, raw, hs⟩ := h
  obtain ⟨C, hC⟩ : ∃ C, Total.Decode.context (request b u) = some C := by
    simp only [Total.Decode.context, request, contract]
    exact ⟨_, rfl⟩
  let L := names.map (fun x => (x, Source.STy.bool))
  obtain ⟨s, spelled, inferred⟩ :=
    (BooleanDomain.Stmt.block hs).inferred (C := C) (L := L) rfl
  obtain ⟨d, hd⟩ := inferred.singleton
  have hp : Total.Decode.plain (request b u) = true := by
    simp only [Total.Decode.plain, request, site, siteCallee, slots, scope]
    rfl
  have hl : Total.Decode.locals (request b u).input.before.locals.1 = some L := by
    change Total.Decode.locals b.input.before.locals.1 = some L
    rw [locals]
    exact locals_decoded names
  have ht : Total.Decode.items .body (request b u).input.raw =
      some (.cons (.stmtItem s) .nil) := by
    change Total.Decode.items .body b.input.raw = _
    rw [raw]
    exact Total.Spells.Items.decode (.stmt spelled .nil)
  refine ⟨C, L, s, d, ?_⟩
  unfold Total.Decode.decode
  rw [hp, hC, hl, ht]
  simp only [ite_true]
  dsimp only [Bind.bind, Option.bind]
  rw [hd]
  rfl

/-- A Boolean block resolves with exactly the same production input. -/
theorem BlockInput.associated {b u} (h : BlockInput b u)
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

end BooleanBlocksV3

/-- Additive coverage of Boolean while inputs and Boolean blocks, under the
unchanged production-placement and acceptance contracts. -/
def BooleanBlocksTotalV3 (D : Diagram) : Prop :=
  ∀ (b : Body) (u : Emitted), BooleanBlocksV3.Input b u →
    @ProductionV2 productionNames b u → Accepted u →
    ∃ b' : Body, b'.SameInput b ∧ ∃ m, D.Assoc b' u m

/-- Every accepted production in the additive Boolean-block domain is covered.
This is not unrestricted all-site Diagram.Total. -/
theorem diagram_total_boolean_blocks : BooleanBlocksTotalV3 diagram := by
  intro b u input production accepted
  rcases input with old | block
  · exact diagram_total_boolean b u old production accepted
  · exact block.associated production.2.2

end Solidity.Correctness.Lowering.Sim.Coverage

#print axioms Solidity.Correctness.Lowering.Sim.Coverage.diagram_total_boolean_blocks
