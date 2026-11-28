import Solidity.Correctness.Lowering.Sim.Coverage.BooleanStmtInference
import Solidity.Correctness.Lowering.Sim.Coverage.ProductionV2
import Solidity.Correctness.Lowering.Sim.Coverage.Alignment

/-! Coverage for singleton Boolean statements, using the existing Source
inference and decoder. The while-only and block entry points delegate here;
their narrower predicates remain available for existing callers. -/
namespace Solidity.Correctness.Lowering.Sim.Coverage

open Solidity.Goals.Shrink.Lowering

namespace BooleanStatements

/-- Any singleton statement of the existing Boolean grammar at the approved
plain caller boundary. Counter, memo and loop specifications are unrestricted. -/
def Input (b : Body) (u : Emitted) : Prop :=
  b.site = .loop ∧ u.C = { vars := [] } ∧ b.input.returnSlots = none ∧
  b.input.scope = { funs := [] } ∧
  ∃ (names : List String) (stmt : RawStmt),
    b.input.before.locals.1 = names.map (fun x => (x, .val .bool)) ∧
    b.input.raw = [stmt] ∧ BooleanDomain.Stmt names false stmt

/-- Singleton Boolean inputs in any checked caller scope with no overflow hook.
All other scope fields, the counter and memo are unrestricted. -/
def CheckedInput (b : Body) (u : Emitted) : Prop :=
  b.site = .loop ∧ u.C = { vars := [] } ∧ b.input.returnSlots = none ∧
  b.input.scope.unchecked = false ∧ b.input.scope.overflow = none ∧
  ∃ (names : List String) (stmt : RawStmt),
    b.input.before.locals.1 = names.map (fun x => (x, .val .bool)) ∧
    b.input.raw = [stmt] ∧ BooleanDomain.Stmt names false stmt

/-- The established default-scope domain is included without producer premises. -/
theorem Input.checked {b u} (h : Input b u) : CheckedInput b u := by
  obtain ⟨site, contract, slots, scope, rest⟩ := h
  exact ⟨site, contract, slots, by rw [scope], by rw [scope], rest⟩

/-- Inclusion of the while-only caller boundary, without production hypotheses. -/
theorem of_while {b u} (h : BooleanDomain.Input b u) : Input b u := by
  obtain ⟨site, contract, slots, scope, names, c, ss, locals, raw, hc, hs⟩ := h
  exact ⟨site, contract, slots, scope, names, _, locals, raw, .whileLoop hc hs⟩

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
theorem CheckedInput.decoded_stmt {b u} (h : CheckedInput b u) :
    ∃ (C : Source.Ctx) (L : List (String × Source.STy)) (s : Source.Syn (.stmt .body))
      (d : Source.StmtD C L s L),
      Total.Decode.decode (request b u) = some (Total.SourceProgram.ofStmt d.toR) := by
  obtain ⟨site, contract, slots, checked, overflow, names, stmt, locals, raw, hs⟩ := h
  obtain ⟨C, hC⟩ : ∃ C, Total.Decode.context (request b u) = some C := by
    simp only [Total.Decode.context, request, contract]
    exact ⟨_, rfl⟩
  let L := names.map (fun x => (x, Source.STy.bool))
  obtain ⟨s, spelled, inferred⟩ :=
    hs.inferred (C := C) (L := L) rfl
  obtain ⟨d, hd⟩ := inferred.singleton
  have hp : Total.Decode.plain (request b u) = true := by
    simp only [Total.Decode.plain, request, site, siteCallee, slots, checked, overflow]
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

/-- A Boolean statement resolves with exactly the same production input. -/
theorem CheckedInput.associated {b u} (h : CheckedInput b u)
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

/-- Compatibility decoding at the default caller scope. -/
theorem Input.decoded_stmt {b u} (h : Input b u) :
    ∃ (C : Source.Ctx) (L : List (String × Source.STy)) (s : Source.Syn (.stmt .body))
      (d : Source.StmtD C L s L),
      Total.Decode.decode (request b u) = some (Total.SourceProgram.ofStmt d.toR) :=
  h.checked.decoded_stmt

/-- Compatibility association at the default caller scope. -/
theorem Input.associated {b u} (h : Input b u) (placed : ThreadedV2 b u) :
    ∃ b' : Body, b'.SameInput b ∧ ∃ m, diagram.Assoc b' u m :=
  h.checked.associated placed

end BooleanStatements

/-- Additive singleton-statement coverage under unchanged production and acceptance. -/
def BooleanStatementsTotal (D : Diagram) : Prop :=
  ∀ (b : Body) (u : Emitted), BooleanStatements.Input b u →
    @ProductionV2 productionNames b u → Accepted u →
    ∃ b' : Body, b'.SameInput b ∧ ∃ m, D.Assoc b' u m

/-- Coverage in checked scopes, with the existing production and acceptance contracts. -/
def CheckedBooleanStatementsTotal (D : Diagram) : Prop :=
  ∀ (b : Body) (u : Emitted), BooleanStatements.CheckedInput b u →
    @ProductionV2 productionNames b u → Accepted u →
    ∃ b' : Body, b'.SameInput b ∧ ∃ m, D.Assoc b' u m

/-- Every accepted singleton Boolean production in a checked scope is associated.
Unchecked scopes, overflow hooks and non-loop sites are outside this boundary. -/
theorem diagram_total_checked_boolean_statements : CheckedBooleanStatementsTotal diagram := by
  intro b u input production _accepted
  exact input.associated production.2.2

/-- Every accepted production in the singleton Boolean-statement domain has a resolved association.
This restricted theorem does not prove unrestricted all-site Diagram.Total. -/
theorem diagram_total_boolean_statements : BooleanStatementsTotal diagram := by
  intro b u input production accepted
  exact diagram_total_checked_boolean_statements b u input.checked production accepted

end Solidity.Correctness.Lowering.Sim.Coverage

#print axioms Solidity.Correctness.Lowering.Sim.Coverage.diagram_total_boolean_statements

#print axioms Solidity.Correctness.Lowering.Sim.Coverage.diagram_total_checked_boolean_statements
