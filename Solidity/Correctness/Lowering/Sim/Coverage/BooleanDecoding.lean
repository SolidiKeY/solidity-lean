import Solidity.Correctness.Lowering.Sim.Coverage.BooleanStmtInference
import Solidity.Correctness.Lowering.Sim.Match

/-! Completeness of the existing decoder on the approved Boolean input
boundary, toward `Solidity.Goals.loweringBySimulation`. No decoder is added. -/
namespace Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain

open Solidity.Goals.Shrink.Lowering

private theorem locals_decoded (names : List String) :
    Total.Decode.locals (names.map (fun x => (x, .val .bool))) =
      some (names.map (fun x => (x, Source.STy.bool))) := by
  induction names with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, Total.Decode.locals, Total.Decode.localTy,
      Source.Agreement.sourceTy, ih]
    rfl

/-- Every approved input decodes to the singleton resolution of an actual
Source statement derivation. Production and acceptance are not assumed here. -/
theorem Input.decoded_stmt {b u} (h : Input b u) :
    ∃ (C : Source.Ctx) (L : List (String × Source.STy)) (s : Source.Syn (.stmt .body))
      (d : Source.StmtD C L s L),
      Total.Decode.decode (request b u) = some (Total.SourceProgram.ofStmt d.toR) := by
  obtain ⟨site, contract, slots, scope, names, c, ss, locals, raw, hc, hs⟩ := h
  obtain ⟨C, hC⟩ : ∃ C, Total.Decode.context (request b u) = some C := by
    simp only [Total.Decode.context, request, contract]
    exact ⟨_, rfl⟩
  let L := names.map (fun x => (x, Source.STy.bool))
  obtain ⟨s, spelled, inferred⟩ := (Stmt.whileLoop hc hs).inferred (C := C) (L := L) rfl
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

end Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain
