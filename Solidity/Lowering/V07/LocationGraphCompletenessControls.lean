import Solidity.Lowering.V07.LocationGraphCompleteness
import Solidity.Lowering.V07.LocationProducerControls
namespace Solidity.Lowering.V07.LocationGraphCompletenessControls
open LocationGraphProducer LocationGraphCompleteness

def E := LocationProducerControls.chain
def fs : Fin 3 → List (Name × TypeGraph.Ty 3) := fun i =>
  if i.val = 0 then [("next",.node ⟨1,by decide⟩)]
  else if i.val = 1 then [("next",.node ⟨2,by decide⟩)] else [("value",.prim .uint)]
def r : Fin 3 → Nat := fun i => if i.val = 0 then 30 else if i.val = 1 then 20 else 10

def related : ∀ i, GraphFieldsRel E.layout (name E .memory) (sourceFields E .memory i) (fs i) := by
  intro i
  rcases i with ⟨i,hi⟩
  change i < 3 at hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · exact .cons rfl (.node .memory ⟨1,by decide⟩) .nil
  · exact .cons rfl (.node .memory ⟨2,by decide⟩) .nil
  · exact .cons rfl (.int ⟨false,8,by decide⟩) .nil

def support : ∀ i s, s ∈ sourceFields E .memory i → LocalFieldSupport.Supported E.layout s.2 := by
  intro i s member
  rcases i with ⟨i,hi⟩
  change i < 3 at hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases with rfl | rfl | rfl <;>
    have equal := List.mem_singleton.mp member <;> cases equal <;> exact True.intro

-- Actual selected graph computation; no supplied successful producer/check premise.
def producer_client : (produce "component-from-structural-fields" E .memory).isSome = true :=
  producer_success E .memory _ (by decide) fs related support (by decide) (by decide) r (by decide)
def fields_client (i : Fin 3) : (RecursiveGraph.lowerFields E.layout (name E .memory)
    (sourceFields E .memory i)).map Subtype.val = some (fs i) :=
  fields_exact (by intro a b h; exact (show SelectionOK E .memory by decide).2.1 a b h)
    (related i) (support i)
example : r ⟨0,by decide⟩ = 30 ∧ ranks E .memory ⟨0,by decide⟩ = 3 := by decide
example : (sourceIndex E .memory ⟨0,by decide⟩).val = 2 := by decide
example : ((RecursiveGraph.lowerFields E.layout (name E .memory)
    (sourceFields E .memory ⟨0,by decide⟩)).map Subtype.val) ≠
      some [("next",.node ⟨0,by decide⟩)] := by decide
example : ¬ (∀ i f, f ∈ fs i → f.2.inlineRank (fun _ => 1) < 1) := by decide

-- Cycles and unsupported fields retain the actual old component failures.
example : (produce "inline-cycle" GraphAdmissionBoundary.directEnv .storage).isNone = true := by decide
example : (produce "bytes-open" LocationProducerControls.withBytes .memory).isNone = true := by decide
example : ¬ ([("value",(.prim .uint : TypeGraph.Ty 1)),("value",.prim .bool)] |>
    Semantics.nodupKeysB) = true := by decide

/-- info: [true, true, true, true, true, true, false] -/
#guard_msgs in
#eval IO.println (reprStr [(produce "component-from-structural-fields" E .memory).isSome,
  decide (ranks E .memory ⟨0,by decide⟩ = 3),
  decide ((sourceIndex E .memory ⟨0,by decide⟩).val = 2),
  (produce "inline-cycle" GraphAdmissionBoundary.directEnv .storage).isNone,
  (produce "bytes-open" LocationProducerControls.withBytes .memory).isNone,
  decide ((fs ⟨0,by decide⟩) = [("next",.node ⟨1,by decide⟩)]),
  decide ((fs ⟨0,by decide⟩) = [("next",.node ⟨0,by decide⟩)])])
end Solidity.Lowering.V07.LocationGraphCompletenessControls
