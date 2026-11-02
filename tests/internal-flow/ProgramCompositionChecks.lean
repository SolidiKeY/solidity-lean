import tests.«internal-flow».SharedArgumentEndpoint
import Solidity.Backend.InternalFlow.ProgramComposition
import Solidity.Backend.InternalFlow.RuntimeWorld
import Solidity.Backend.InternalFlow.WorldProgramTarget

namespace Solidity.Backend.InternalFlow.ProgramComposition.Checks
open Evm Evm.Memory ContractWorld
open PublishedDirectCalls.Checks (prefixProducer caller initial machine bases words initial_repr callerPrefix)
open ArgumentFailureTarget.Checks
open SharedCallPrefix.Checks (publicGood publicBad public_metadata)

def good := join prefixProducer publicGood
def bad := join prefixProducer publicBad

def output : Solidity.Out C initial.H Final := ⟨exported.st,caller.ext.trans exported.ext⟩

theorem good_suffix : (Prog.cons (.call "arguments" goodArgs ret body) .nil).run caller.st = .ok exported := by
 change TRun.seq (Stmt.runR (.call "arguments" goodArgs ret body)) TRun.nil caller.st = _
 rw [RuntimeWorld.seq_nil]
 exact good_call

theorem bad_suffix : (Prog.cons (.call "arguments" badArgs ret body) .nil).run caller.st = .error .revert := by
 change TRun.seq (Stmt.runR (.call "arguments" badArgs ret body)) TRun.nil caller.st = _
 rw [RuntimeWorld.seq_nil]
 exact bad_call

theorem source_success :
 (callerPrefix.join (.cons (.call "arguments" goodArgs ret body) .nil)).run initial = .ok output := by
 rw [DeferredSource.join_run]
 change TRun.seq callerPrefix.runR (Prog.cons (.call "arguments" goodArgs ret body) .nil).runR initial = _
 have hp : callerPrefix.runR initial = .ok caller := prefix_execution
 have hs : (Prog.cons (.call "arguments" goodArgs ret body) .nil).runR caller.st = .ok exported := good_suffix
 rw [TRun.seq,hp]
 dsimp only
 rw [hs]
 rfl

theorem source_failure :
 (callerPrefix.join (.cons (.call "arguments" badArgs ret body) .nil)).run initial = .error .revert := by
 rw [DeferredSource.join_run]
 have hp : callerPrefix.runR initial = .ok caller := prefix_execution
 have hs : (Prog.cons (.call "arguments" badArgs ret body) .nil).runR caller.st = .error .revert := bad_suffix
 rw [TRun.seq,hp]
 dsimp only
 rw [hs]
 rfl

theorem actual_costs : good.cost initial = 7 ∧ bad.cost initial = 3 := by
 constructor
 · change (join prefixProducer publicGood).cost initial = 7
   rw [cost_success prefixProducer publicGood initial caller prefix_execution,costs.1,public_metadata.2.1]
 · change (join prefixProducer publicBad).cost initial = 3
   rw [cost_success prefixProducer publicBad initial caller prefix_execution,costs.1,public_metadata.1]

theorem actual_rooms : 1 + good.need ≤ 128 ∧ 1 + bad.need ≤ 128 := by
 have hp := frame_rooms.1
 have hg := public_metadata.2.2.2
 have hb := public_metadata.2.2.1
 change 1 + max prefixProducer.need publicGood.need ≤ 128 ∧
   1 + max prefixProducer.need publicBad.need ≤ 128
 rw [hg,hb]
 omega

theorem initial_capacity : AllocationInput 1 128 (good.cost initial) initial bases machine ∧
 AllocationInput 1 128 (bad.cost initial) initial bases machine := by
 constructor
 · rw [actual_costs.1]
   simpa only [costs.1,costs.2.2] using good_capacity
 · rw [actual_costs.2]
   simpa only [costs.1,costs.2.1] using bad_capacity

/-- Whole-program soundness derives its actual reached representation and total
allocator growth from the real initial representation, not a supplied midpoint. -/
theorem complete_endpoint : ∃ reached addresses,
 Evm.run good.code machine = .ok reached 0 ∧
 StateRepr 1 1 128 good.frag output.st addresses reached ∧
 reached.stack = machine.stack ∧ BaseExtends initial.H bases addresses ∧
 GrowsAllocator 1 128 7 initial bases machine output.st addresses reached := by
 obtain ⟨m,b,ht,hr,hk,he,hg⟩ := PublishedDirectCalls.program_endpoint good initial_repr.1
  actual_rooms.1 initial_capacity.1 output source_success
 exact ⟨m,b,ht,hr,hk,he,by simpa only [actual_costs.1] using hg⟩

theorem complete_failure : Evm.run bad.code machine = .revert := by
 rcases bad.sound initial_repr.1 actual_rooms.2 initial_capacity.2 with
  ⟨o,m,b,hs,_⟩ | ⟨_,ht⟩
 · rw [source_failure] at hs
   contradiction
 · exact ht

/-- BOTH constituent call programs are the actual public selector results.
The owned whole-program emitter is not claimed to be the global selection. -/
theorem constituent_selectors :
 Calls.compile 1 prefixProducer.frag (.cons (.call "arguments" goodArgs ret body) .nil) = some publicGood ∧
 Calls.compile 1 prefixProducer.frag (.cons (.call "arguments" badArgs ret body) .nil) = some publicBad := by
 rw [SharedCallPrefix.Checks.selected_good_root,SharedCallPrefix.Checks.selected_bad_root]
 exact ⟨SharedCallPrefix.Checks.public_good_root,SharedCallPrefix.Checks.public_bad_root⟩

theorem complete_vector : words (Evm.run good.code machine)
 [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262] =
 some [77,263,99,42,256,256,260,42,11,260,260,0,0,2,7,11,0,2,0,0] :=
 SharedCallPrefix.Checks.emitted_success_vector

theorem wrong_alias : words (Evm.run good.code machine)
 [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262] ≠
 some [77,263,99,42,256,260,260,42,11,260,260,0,0,2,7,11,0,2,0,0] := by
 rw [complete_vector];decide

theorem wrong_cursor : words (Evm.run good.code machine)
 [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262] ≠
 some [77,259,99,42,256,256,260,42,11,260,260,0,0,2,7,11,0,2,0,0] := by
 rw [complete_vector];decide

theorem suffix_not_reached_cost : bad.cost initial ≠ good.cost initial := by
 rw [actual_costs.1,actual_costs.2];decide

theorem failure_not_fault : Evm.run bad.code machine ≠ .fault := by
 rw [complete_failure];intro h;cases h

/-- The very same represented initial state is an actual ordinary world entry,
not an invented world/machine relation or supplied desired midpoint. -/
def zeroAddress : Address := ⟨PrimTy.dflt .uint,by decide +kernel⟩
def catalog (_ : Unit) : Contract := C
def world : World catalog :=
 {accounts := fun _ => some ⟨(),Storage.init C⟩,funds := fun _ => PrimTy.dflt .uint}
def self : Handle () := ⟨zeroAddress⟩
def context : Context := ⟨zeroAddress,.ordinary (PrimTy.dflt .uint),[]⟩
def decodeResult (σ : State C Final) : TRes (Option Nat) := .ok (σ.env.1.map HRef.id)
def goodEntry : Entry C (Option Nat) :=
 ⟨Final,callerPrefix.join (.cons (.call "arguments" goodArgs ret body) .nil),decodeResult,false⟩
def badEntry : Entry C (Option Nat) :=
 ⟨Final,callerPrefix.join (.cons (.call "arguments" badArgs ret body) .nil),decodeResult,false⟩

theorem entered : world.enter (k := ()) zeroAddress context (Storage.init C) false = .ok initial := rfl

theorem world_entry_target : ∃ σ, world.enter (k := ()) zeroAddress context (Storage.init C) false = .ok σ ∧
 StateRepr 1 1 128 (Frag.init []) σ bases machine ∧
 goodEntry.body.runSt σ = .ok output.st ∧
 ∃ reached addresses, Evm.run good.code machine = .ok reached 0 ∧
 StateRepr 1 1 128 good.frag output.st addresses reached ∧
 reached.stack = machine.stack ∧ BaseExtends σ.H bases addresses ∧
 GrowsAllocator 1 128 7 σ bases machine output.st addresses reached :=
 by
 refine ⟨initial,entered,initial_repr.1,?_,complete_endpoint⟩
 change ((callerPrefix.join (.cons (.call "arguments" goodArgs ret body) .nil)).run initial).map (·.st) = _
 rw [source_success];rfl

theorem actual_world_failure : world.callFrame self badEntry context = .error .revert := by
 change ((TRes.ofOpt (world.storage? self)).bind fun st =>
  (world.enter (k := ()) zeroAddress context st false).bind fun σ =>
  (badEntry.body.run σ).bind fun o =>
  (world.finish (k := ()) zeroAddress o.st).map fun w => (w,o.st)) = _
 have stored : world.storage? self = some (Storage.init C) := rfl
 rw [stored]
 change ((world.enter (k := ()) zeroAddress context (Storage.init C) false).bind fun σ =>
  (badEntry.body.run σ).bind fun o =>
  (world.finish (k := ()) zeroAddress o.st).map fun w => (w,o.st)) = _
 rw [entered]
 change ((callerPrefix.join (.cons (.call "arguments" badArgs ret body) .nil)).run initial).bind _ = _
 rw [source_failure]
 rfl

/-- A failed FIRST constituent is also real: this nonempty allocating suffix
is admitted, but its cost is excluded and its code is absorbed by bare revert.
Neither fact describes a failed output state or absence of hidden side effects. -/
def allocationAfter : Prog C Final (.mem A :: Final) :=
 .cons (.declMem A (.user "after") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl) .nil

def allocationProducer : Calls.Program 1 bad.frag allocationAfter :=
 Calls.plain ((Memory.compileProg 1 bad.frag allocationAfter).get (by decide +kernel))

def failedFirst := join bad allocationProducer

theorem allocating_suffix_admitted :
 (Memory.compileProg 1 bad.frag allocationAfter).isSome = true ∧
 allocationProducer.cost output.st = 2 := by
 constructor <;> decide +kernel

theorem failed_first_cost : failedFirst.cost initial = 3 := by
 change (join bad allocationProducer).cost initial = 3
 rw [cost_failure bad allocationProducer initial .revert source_failure,actual_costs.2]

theorem failed_first_source :
 ((callerPrefix.join (.cons (.call "arguments" badArgs ret body) .nil)).join allocationAfter).run initial =
 .error .revert := by
 rw [DeferredSource.join_run]
 have hs : (callerPrefix.join (.cons (.call "arguments" badArgs ret body) .nil)).runR initial = .error .revert := source_failure
 rw [TRun.seq,hs]

theorem failed_first_target : Evm.run failedFirst.code machine = .revert :=
 Evm.run_append_revert complete_failure

theorem failed_first_wrong_cost : failedFirst.cost initial ≠ bad.cost initial + allocationProducer.cost output.st := by
 rw [failed_first_cost,actual_costs.2,allocating_suffix_admitted.2];decide

/-- A successful frame settles through the EXISTING world operation as well;
this is a concrete zero-payment world, not arbitrary external/callback transport. -/
def nextWorld : World catalog :=
 (world.finish (k := ()) zeroAddress output.st).toOption.get (by decide +kernel)

private theorem actual_get {α : Type} (r : TRes α) (ok : r.toOption.isSome = true) :
 r = .ok (r.toOption.get ok) := by
 cases r with | error e => cases ok | ok value => rfl

theorem finished : world.finish (k := ()) zeroAddress output.st = .ok nextWorld :=
 actual_get _ (by decide +kernel)

theorem actual_world_success : world.callFrame self goodEntry context = .ok (nextWorld,output.st) := by
 change ((TRes.ofOpt (world.storage? self)).bind fun st =>
  (world.enter (k := ()) zeroAddress context st false).bind fun σ =>
  (goodEntry.body.run σ).bind fun o =>
  (world.finish (k := ()) zeroAddress o.st).map fun w => (w,o.st)) = _
 have stored : world.storage? self = some (Storage.init C) := rfl
 rw [stored]
 change ((world.enter (k := ()) zeroAddress context (Storage.init C) false).bind fun σ =>
  (goodEntry.body.run σ).bind fun o =>
  (world.finish (k := ()) zeroAddress o.st).map fun w => (w,o.st)) = _
 rw [entered]
 change ((callerPrefix.join (.cons (.call "arguments" goodArgs ret body) .nil)).run initial).bind _ = _
 rw [source_success]
 change (world.finish (k := ()) zeroAddress output.st).map (fun w => (w,output.st)) = _
 rw [finished];rfl

/-- The new world/body bridge is instantiated with actual settled execution;
lookup, entered representation, room and capacity are all discharged here. -/
theorem settled_body_target : ∃ reached addresses,
 Evm.run good.code machine = .ok reached 0 ∧
 StateRepr 1 1 128 good.frag output.st addresses reached ∧
 reached.stack = machine.stack ∧ BaseExtends initial.H bases addresses ∧
 GrowsAllocator 1 128 7 initial bases machine output.st addresses reached := by
 obtain ⟨out,m,b,hs,ho,hf,ht,hr,hk,he,hg⟩ := WorldProgramTarget.frame_endpoint
  world nextWorld self goodEntry context output.st good (Storage.init C) initial rfl entered
  initial_repr.1 actual_rooms.1 initial_capacity.1 actual_world_success
 exact ⟨m,b,ht,hr,hk,he,by simpa only [actual_costs.1] using hg⟩

/-- The failure pair is coupled by the identical actual body error, not by
inferring a failed machine or assuming that a world error arose inside a body. -/
theorem coupled_world_revert : world.callFrame self badEntry context = .error .revert ∧
 Evm.run bad.code machine = .revert :=
 WorldProgramTarget.frame_revert world self badEntry context bad (Storage.init C) initial
  rfl rfl entered initial_repr.1 actual_rooms.2 initial_capacity.2 source_failure

#print axioms Solidity.Backend.InternalFlow.ProgramComposition.join
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.fields
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.cost_success
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.cost_failure
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.good_suffix
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.bad_suffix
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.source_success
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.source_failure
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.actual_costs
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.actual_rooms
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.initial_capacity
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.complete_endpoint
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.complete_failure
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.constituent_selectors
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.complete_vector
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.wrong_alias
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.wrong_cursor
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.suffix_not_reached_cost
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.failure_not_fault
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.entered
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.world_entry_target
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.actual_world_failure
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.allocating_suffix_admitted
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.failed_first_cost
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.failed_first_source
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.failed_first_target
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.failed_first_wrong_cost
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.finished
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.actual_world_success
#print axioms Solidity.Backend.InternalFlow.WorldProgramTarget.frame_endpoint
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.settled_body_target
#print axioms Solidity.Backend.InternalFlow.WorldProgramTarget.frame_revert
#print axioms Solidity.Backend.InternalFlow.ProgramComposition.Checks.coupled_world_revert
end Solidity.Backend.InternalFlow.ProgramComposition.Checks
