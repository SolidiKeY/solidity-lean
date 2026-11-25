import Solidity.Correctness.Lowering.Sim.Coverage.Obstruction
import Solidity.Correctness.Lowering.Sim.Coverage.ProductionV2

namespace Solidity.Correctness.Lowering.Sim.Coverage

open Solidity.Goals.Shrink.Lowering

/-- Empty input in an unchecked caller scope. -/
def uncheckedBody : Body :=
  { body with input := { body.input with scope := { funs := [], unchecked := true } } }

/-- Correct caller placement does not make the unchecked request plain. -/
def uncheckedEmitted : Emitted where
  C := { vars := [] }
  Γ := []
  output :=
    { raw := [], afterLower := ⟨([], 0), {}⟩,
      elabScope := { funs := [], unchecked := true }, beforeElab := ⟨([], 0), {}⟩,
      afterElab := ⟨([], 0), {}⟩, elaborated := [], names := [], program := ⟨[], .nil⟩ }

theorem unchecked_production (hk : Solidity.Goals.elabKernelTotal) :
    @ProductionV2 productionNames uncheckedBody uncheckedEmitted := by
  letI : FreshNames := productionNames
  have hn := (hk.1 uncheckedEmitted.C).2.1
  rcases hn with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, _⟩
  have he : elabStmtsP uncheckedEmitted.C [] = pure [] := by
    rw [← hn]
    exact (hk.1 uncheckedEmitted.C).1.1
  refine ⟨?_, ⟨?_, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl, rfl⟩
  · exact ⟨rfl, by simp only [uncheckedBody, body, uncheckedEmitted, lowerAt, lowerLoops, lowerList]; rfl⟩
  · change (((elabStmtsP uncheckedEmitted.C []).run _).run _).run _ = _
    rw [he]
    rfl

theorem unchecked_accepted : Accepted uncheckedEmitted := .nil

/-- The frozen spelling relation rejects this accepted, correctly placed run. -/
theorem unchecked_unassociated (b' : Body) (h : b'.SameInput uncheckedBody)
    (m : Solidity.Lowering.V07.ContextMap b'.ctx uncheckedEmitted.Γ) :
    ¬ diagram.Assoc b' uncheckedEmitted m := by
  intro ha
  obtain ⟨s, spells, _⟩ := ha.2.2.2
  have hp := spells.1
  unfold Total.Decode.plain request at hp
  rw [h.1, h.2.2.1, h.2.2.2.1] at hp
  cases hp

/-- Caller placement alone cannot close coverage with the frozen association. -/
theorem not_totalV2 (hk : Solidity.Goals.elabKernelTotal) :
    ¬ @TotalV2 productionNames diagram := by
  intro ht
  obtain ⟨b', same, m, assoc⟩ := ht uncheckedBody uncheckedEmitted
    (unchecked_production hk) unchecked_accepted
  exact unchecked_unassociated b' same m assoc

end Solidity.Correctness.Lowering.Sim.Coverage

#print axioms Solidity.Correctness.Lowering.Sim.Coverage.unchecked_production
#print axioms Solidity.Correctness.Lowering.Sim.Coverage.not_totalV2
