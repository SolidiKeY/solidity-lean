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

/-- Include the block boundary in the shared singleton-statement domain. -/
theorem BlockInput.toStatementInput {b u} (h : BlockInput b u) :
    BooleanStatements.Input b u := by
  obtain ⟨site, contract, slots, scope, names, ss, locals, raw, hs⟩ := h
  exact ⟨site, contract, slots, scope, names, _, locals, raw, .block hs⟩

/-- Completeness uses the actual Source inference and the existing decoder;
domain membership contains neither decoder success nor an association. -/
theorem BlockInput.decoded_stmt {b u} (h : BlockInput b u) :
    ∃ (C : Source.Ctx) (L : List (String × Source.STy)) (s : Source.Syn (.stmt .body))
      (d : Source.StmtD C L s L),
      Total.Decode.decode (request b u) = some (Total.SourceProgram.ofStmt d.toR) := by
  exact h.toStatementInput.decoded_stmt

/-- A Boolean block resolves with exactly the same production input. -/
theorem BlockInput.associated {b u} (h : BlockInput b u)
    (placed : ThreadedV2 b u) :
    ∃ b' : Body, b'.SameInput b ∧ ∃ m, diagram.Assoc b' u m := by
  exact h.toStatementInput.associated placed

end BooleanBlocksV3

/-- Include both established input boundaries in the shared statement domain. -/
theorem BooleanStatements.of_blocks {b u} (h : BooleanBlocksV3.Input b u) :
    BooleanStatements.Input b u := by
  rcases h with old | block
  · exact BooleanStatements.of_while old
  · exact block.toStatementInput

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
  exact diagram_total_boolean_statements b u (BooleanStatements.of_blocks input)
    production accepted

end Solidity.Correctness.Lowering.Sim.Coverage

#print axioms Solidity.Correctness.Lowering.Sim.Coverage.diagram_total_boolean_blocks
