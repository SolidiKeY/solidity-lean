import Solidity.Correctness.Lowering.Sim.Match
import Solidity.Goals.ElabTotal

namespace Solidity.Correctness.Lowering.Sim.Coverage

open Solidity.Goals.Shrink.Lowering

/-- Empty production input, with no caller locals. -/
def body : Body where
  E := ⟨[]⟩
  returns := []
  modifier := false
  control := .body
  ctx := []
  input :=
    { raw := [], resolved := .block .nil, returnSlots := none,
      scope := { funs := [] }, before := ⟨([], 0), {}⟩ }
  site := .loop

/-- The empty program can be placed in an unrelated Boolean context. -/
def emitted : Emitted where
  C := { vars := [] }
  Γ := [.val .bool]
  output :=
    { raw := [], afterLower := ⟨([], 0), {}⟩,
      elabScope := { funs := [] }, beforeElab := ⟨([], 0), {}⟩,
      afterElab := ⟨([], 0), {}⟩, elaborated := [], names := [],
      program := ⟨[.val .bool], .nil⟩ }

/-- The empty elaboration equation comes from the explicit kernel hypothesis. -/
theorem production (hk : Solidity.Goals.elabKernelTotal) :
    @Production productionNames body emitted := by
  letI : FreshNames := productionNames
  have hn := (hk.1 emitted.C).2.1
  rcases hn with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, _⟩
  have he : elabStmtsP emitted.C [] = pure [] := by
    rw [← hn]
    exact (hk.1 emitted.C).1.1
  refine ⟨?_, ⟨?_, rfl⟩, rfl, rfl, rfl⟩
  · exact ⟨rfl, by simp only [body, emitted, lowerAt, lowerLoops, lowerList]; rfl⟩
  · change (((elabStmtsP emitted.C []).run _).run _).run _ = _
    rw [he]
    rfl

theorem accepted : Accepted emitted := .nil

/-- SameInput cannot repair the emitted context: the caller has no locals. -/
theorem unassociated (b' : Body) (h : b'.SameInput body)
    (m : Solidity.Lowering.V07.ContextMap b'.ctx emitted.Γ) :
    ¬ diagram.Assoc b' emitted m := by
  intro ha
  have hc := ha.1
  change [.val .bool] = (ECtx.toNCtx
    (((siteCallee b'.site).map (·.locals)).getD b'.input.before.locals.1)).ctx at hc
  rw [h.1, h.2.2.2.2] at hc
  cases hc

/-- The frozen v1 totality statement fails even with the kernel equations. -/
theorem not_total (hk : Solidity.Goals.elabKernelTotal) :
    ¬ @Diagram.Total productionNames diagram := by
  intro ht
  obtain ⟨b', same, m, assoc⟩ := ht body emitted (production hk) accepted
  exact unassociated b' same m assoc

end Solidity.Correctness.Lowering.Sim.Coverage

#print axioms Solidity.Correctness.Lowering.Sim.Coverage.production
#print axioms Solidity.Correctness.Lowering.Sim.Coverage.not_total
