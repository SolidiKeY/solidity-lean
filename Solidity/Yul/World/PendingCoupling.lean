import Solidity.Backend.WorldCalls.Premises
import Solidity.Backend.Transient.State
import Solidity.Yul.World.Adapters

/-! H26 pending P19 producer interface. No instance is supplied.
The existing G42 Step must be produced from an actual invocation. The producer
must establish the entire caller-selected physical representation and ordered
observation encoding; these fields are not a world/log implementation.
The Source observation relation and physical relation require their owners'
H25/G01/layout review; arbitrary choices are not adequacy certificates.
The observation relation carries the complete trace rather than attempting to
reconstruct interleaving from separate legacy lists. A raw Source halt retains
its own bytes in `raw`; it is not equated to caller-local last-returndata.
Timeout/stuck and their buffer policies remain H16/H25 producer obligations. -/
namespace Solidity.Yul.World.PendingCoupling
open Solidity.Source
open Solidity.Backend.WorldCalls

/-- Per-reached-invocation obligations. `Physical` is the consumer's existing
complete carrier, not a replacement state or a layout defined by this module.
All Source fields remain in `final`; representation must retain all physical
journals/owned bytes. The target transient carrier is the published P7 State.
No assumption of total reachability, emitter encoding, or static legality is
introduced outside the explicit producer fields. -/
structure WorldLogAt {E : Source.Env} {Γ : Source.RCtx} {dn : Source.DeclName}
    {ps rs : List Source.STy}
    (invocation : Solidity.Lowering.Readonly.InvocationFrame.Invocation E Γ dn ps rs)
    (producer : Premises invocation) (Physical : Type)
    (represented : Source.St E → Physical → Solidity.Backend.Transient.State →
      ObservedEffects E.layout E.lay E.lay → Prop)
    (SourceObserved : Source.St E → List Observation → Prop)
    (initial : Evm.Machine) (raw : Except Source.Halt Solidity.Roadmap.Outcome)
    (final : Source.St E) (target : Evm.Out)
    (physicalEntry physical : Physical)
    (transientEntry transient : Solidity.Backend.Transient.State)
    (observedEntry observed : ObservedEffects E.layout E.lay E.lay) : Prop where
  /-- Same captured call-entry Source/physical state, before invoking the callee. -/
  entryRepresentation : represented invocation.after.2 physicalEntry transientEntry observedEntry
  entryExecution : observedEntry.effects.execution = invocation.after.2.ex
  entryMachine : transientEntry.machine = initial
  entryEvents : interactionEvents observedEntry.trace = invocation.after.2.events
  entryObservations : SourceObserved invocation.after.2 observedEntry.trace
  /-- Actual G42 execution/refusal history remains a producer duty. -/
  step : producer.Step (identity invocation) initial raw final target
  /-- Complete source/physical/transient/observed coupling, not execution-only. -/
  fullRepresentation : represented final physical transient observed
  /-- A successful actual target endpoint is the same P7 machine. The coarse
  target revert/fault constructors carry no machine; their endpoint policies
  remain separate producer obligations rather than invented states. -/
  returnedMachine : ∀ machine skip, target = .ok machine skip →
    transient.machine = machine
  /-- Actual source persistent/transient world and its full journal. -/
  execution : observed.effects.execution = final.ex
  /-- Completed successful/ordinary-reverted calls retain the full last buffer. -/
  returndata : ∀ outcome, raw = .ok outcome →
    observed.effects.returndata = returnData outcome
  /-- Preserve actual ordered source interactions. -/
  events : interactionEvents observed.trace = final.events
  /-- Full ordered log/event agreement; no event-only/log-only projection. -/
  observations : SourceObserved final observed.trace

end Solidity.Yul.World.PendingCoupling
