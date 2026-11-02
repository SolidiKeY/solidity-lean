import tests.«internal-flow».ProgramCompositionChecks
import Solidity.Backend.InternalFlow.ProgramAssociation

namespace Solidity.Backend.InternalFlow.ProgramAssociationChecks
open Evm Evm.Memory
open ProgramComposition
open PublishedDirectCalls.Checks (callerPrefix prefixProducer initial machine bases initial_repr words caller)
open ArgumentFailureTarget.Checks (C A Final goodArgs badArgs ret body exported)
open SharedCallPrefix.Checks (publicGood publicBad)
open ProgramComposition.Checks (output)

def suffix : Prog C Final (.mem A :: Final) :=
 .cons (.declMem A (.user "next") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl)
 (.cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
  (.val (.simple (.lit 19 rfl)))) .nil)
def third : Calls.Program 1 publicGood.frag suffix :=
 Calls.plain ((Memory.compileProg 1 publicGood.frag suffix).get (by decide +kernel))
def left := join (join prefixProducer publicGood) third
def right := join prefixProducer (join publicGood third)
def lastOutput : Solidity.Out C output.st.H (.mem A :: Final) :=
 (suffix.run output.st).toOption.get (by decide +kernel)
def finalOutput : Solidity.Out C initial.H (.mem A :: Final) :=
 ⟨lastOutput.st,output.ext.trans lastOutput.ext⟩
private theorem actual_get {α : Type} (r : TRes α) (ok : r.toOption.isSome = true) :
 r = .ok (r.toOption.get ok) := by cases r with | error e => cases ok | ok v => rfl

theorem suffix_execution : suffix.run output.st = .ok lastOutput := actual_get _ _
theorem suffix_admitted : (Memory.compileProg 1 publicGood.frag suffix).isSome = true := by decide +kernel

theorem source_left :
 ((callerPrefix.join (.cons (.call "arguments" goodArgs ret body) .nil)).join suffix).run initial = .ok finalOutput := by
 rw [DeferredSource.join_run]
 have hp : (callerPrefix.join (.cons (.call "arguments" goodArgs ret body) .nil)).runR initial = .ok output :=
  ProgramComposition.Checks.source_success
 have hs : suffix.runR output.st = .ok lastOutput := suffix_execution
 rw [TRun.seq,hp]
 dsimp only
 rw [hs];rfl

theorem source_right :
 (callerPrefix.join ((Prog.cons (.call "arguments" goodArgs ret body) .nil).join suffix)).run initial = .ok finalOutput := by
 rw [← syntax_association]
 exact source_left

theorem associated_fields : left.code = right.code ∧ left.frag = right.frag ∧
 left.need = right.need ∧ left.cost initial = right.cost initial :=
 association prefixProducer publicGood third initial

theorem exact_costs : third.cost output.st = 2 ∧ left.cost initial = 9 ∧ right.cost initial = 9 := by
 have hc : third.cost output.st = 2 := by decide +kernel
 have step : left.cost initial = ProgramComposition.Checks.good.cost initial + third.cost output.st :=
  cost_success ProgramComposition.Checks.good third initial output ProgramComposition.Checks.source_success
 have numeric : ProgramComposition.Checks.good.cost initial + third.cost output.st = 9 :=
  (congrArg (fun n => n + third.cost output.st) ProgramComposition.Checks.actual_costs.1).trans
   ((congrArg (Nat.add 7) hc).trans rfl)
 have hl : left.cost initial = 9 := step.trans numeric
 exact ⟨hc,hl,associated_fields.2.2.2.symm.trans hl⟩

theorem rooms : 1 + left.need ≤ 128 ∧ 1 + right.need ≤ 128 := by
 have hp := ProgramComposition.Checks.actual_rooms.1
 have ht : 1 + third.need ≤ 128 := by decide +kernel
 have hl : 1 + left.need ≤ 128 := by
  change 1 + max ProgramComposition.Checks.good.need third.need ≤ 128
  omega
 exact ⟨hl,by rw [← associated_fields.2.2.1];exact hl⟩

theorem capacity : AllocationInput 1 128 (left.cost initial) initial bases machine := by
 rw [exact_costs.2.1]
 exact .inr ⟨by decide,wmod 256,initial_repr.2,by decide +kernel⟩

/-- Observation of the existing typed heap, not another execution semantics. -/
def contents {Γ : Ctx} (state : State C Γ) (index : Idx Γ (.mem A)) : Option (List Int) :=
 (TEnv.get index state.env).map (fun (ref : HRef state.H A) => (state.heap.get ref).1.map Subtype.val)

/-- The third stage actually allocates/writes a new object; returned object2
and both old aliases0 survive with their ordered source contents. -/
theorem source_observations :
 (finalOutput.st.H.length,finalOutput.st.env.1.map HRef.id,
  finalOutput.st.env.2.1.map HRef.id,finalOutput.st.env.2.2.1.map HRef.id,
  finalOutput.st.env.2.2.2.1.map HRef.id,finalOutput.st.env.2.2.2.2.1.1,
  ProgramComposition.Checks.output.st.H.length,
  contents finalOutput.st .here,
  contents finalOutput.st (.there .here),
  contents finalOutput.st (.there (.there .here)),
  contents finalOutput.st (.there (.there (.there .here)))) =
 (4,some 3,some 2,some 0,some 0,42,3,some [19],some [0,0],some [7,11],some [7,11]) := by
 simp only [Prod.mk.injEq]
 decide +kernel

theorem both_target_endpoints : ∃ reached addresses,
 Evm.run left.code machine = .ok reached 0 ∧ Evm.run right.code machine = .ok reached 0 ∧
 StateRepr 1 1 128 left.frag finalOutput.st addresses reached ∧
 reached.stack = machine.stack ∧ BaseExtends initial.H bases addresses ∧
 GrowsAllocator 1 128 9 initial bases machine finalOutput.st addresses reached := by
 obtain ⟨m,b,ht,hr,hk,he,hg⟩ := PublishedDirectCalls.program_endpoint left initial_repr.1
  rooms.1 capacity finalOutput source_left
 refine ⟨m,b,ht,?_,hr,hk,he,?_⟩
 · rw [← associated_fields.1];exact ht
 · simpa only [exact_costs.2.1] using hg

theorem complete_target_vector : words (Evm.run left.code machine)
 [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262,263,264] =
 some [77,265,99,42,256,256,260,263,11,260,260,0,0,2,7,11,0,2,0,0,1,19] := by decide +kernel

theorem right_target_vector : words (Evm.run right.code machine)
 [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262,263,264] =
 some [77,265,99,42,256,256,260,263,11,260,260,0,0,2,7,11,0,2,0,0,1,19] := by
 rw [← associated_fields.1];exact complete_target_vector

theorem wrong_cursor : words (Evm.run left.code machine)
 [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262,263,264] ≠
 some [77,263,99,42,256,256,260,263,11,260,260,0,0,2,7,11,0,2,0,0,1,19] := by
 rw [complete_target_vector];decide

theorem wrong_new_alias : finalOutput.st.env.1.map HRef.id ≠ some 2 := by
 have actual := congrArg (fun v => v.2.1) source_observations
 change finalOutput.st.env.1.map HRef.id = some 3 at actual
 rw [actual];decide

def failedRight := join prefixProducer (join publicBad ProgramComposition.Checks.allocationProducer)
theorem failure_association : Evm.run failedRight.code machine = .revert ∧ failedRight.cost initial = 3 := by
 have same := association prefixProducer publicBad ProgramComposition.Checks.allocationProducer initial
 constructor
 · change Evm.run (join prefixProducer (join publicBad ProgramComposition.Checks.allocationProducer)).code machine = _
   rw [← same.1];exact ProgramComposition.Checks.failed_first_target
 · change (join prefixProducer (join publicBad ProgramComposition.Checks.allocationProducer)).cost initial = _
   exact same.2.2.2.symm.trans ProgramComposition.Checks.failed_first_cost

theorem wrong_included_failed_cost : failedRight.cost initial ≠ 5 := by
 rw [failure_association.2];decide

#print axioms Solidity.Backend.InternalFlow.ProgramComposition.syntax_association
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.association
#print axioms Solidity.Backend.InternalFlow.ProgramAssociationChecks.suffix_execution
#print axioms Solidity.Backend.InternalFlow.ProgramAssociationChecks.suffix_admitted
#print axioms Solidity.Backend.InternalFlow.ProgramAssociationChecks.source_left
#print axioms Solidity.Backend.InternalFlow.ProgramAssociationChecks.source_right
#print axioms Solidity.Backend.InternalFlow.ProgramAssociationChecks.associated_fields
#print axioms Solidity.Backend.InternalFlow.ProgramAssociationChecks.exact_costs
#print axioms Solidity.Backend.InternalFlow.ProgramAssociationChecks.rooms
#print axioms Solidity.Backend.InternalFlow.ProgramAssociationChecks.capacity
#print axioms Solidity.Backend.InternalFlow.ProgramAssociationChecks.source_observations
#print axioms Solidity.Backend.InternalFlow.ProgramAssociationChecks.both_target_endpoints
#print axioms Solidity.Backend.InternalFlow.ProgramAssociationChecks.complete_target_vector
#print axioms Solidity.Backend.InternalFlow.ProgramAssociationChecks.right_target_vector
#print axioms Solidity.Backend.InternalFlow.ProgramAssociationChecks.wrong_cursor
#print axioms Solidity.Backend.InternalFlow.ProgramAssociationChecks.wrong_new_alias
#print axioms Solidity.Backend.InternalFlow.ProgramAssociationChecks.failure_association
#print axioms Solidity.Backend.InternalFlow.ProgramAssociationChecks.wrong_included_failed_cost
end Solidity.Backend.InternalFlow.ProgramAssociationChecks
