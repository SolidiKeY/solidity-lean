import Solidity.Backend.AbiWorld.MixedPacket
import tests.«v13-abi-world».CallerPacketControls
import Solidity.Backend.AbiWorld.EnumControls
import tests.«v13-abi-world».MixedCallerValues

/-! Mixed packet consequences of the SAME actual producer prefix/call/tail.
Boundary codec fixtures are separate from compiled applications. Post-execution
literal packets run on a distinct byte-slice machine, not an ABI runtime encoder. -/
namespace Solidity.Backend.AbiWorld.MixedPacketControls
open Evm Evm.Memory InternalFlow
open InternalFlow.MemoryDispatchChecks
open InternalFlow.MemoryDispatchChecks.ProtectedTail

/-- Reuse the actual instantiated selected-call target, then apply the new
captured heterogeneous observer to THAT reached representation. The generic
MixedPacket.selected law remains separate; no desired target run is assumed. -/
theorem selected_client {m₁ : Machine} {base₁ : Nat → Fin W}
    (repr₁ : StateRepr 1 1 64 seed.frag mid.st base₁ m₁)
    (capacity₁ : AllocationInput 1 64 (checked.cost mid.st) mid.st base₁ m₁) :
    ∃ (m₂ : Machine) (base₂ : Nat → Fin W), Evm.run checked.code m₁ = .ok m₂ 0 ∧
      StateRepr 1 1 64 checked.frag chosen.st base₂ m₂ ∧ m₂.stack = m₁.stack ∧
      BaseExtends mid.st.H base₁ base₂ ∧
      GrowsAllocator 1 64 (checked.cost mid.st) mid.st base₁ m₁ chosen.st base₂ m₂ ∧
      m₂.mem (cellOf 1 (capIndex.wk projection)) = .val (base₁ old.id) ∧
      m₂.mem (cellOf 1 (markerIndex.wk projection)) =
        .val (wmod (TEnv.get (markerIndex.wk projection) mid.st.env).val.toNat) ∧
      MixedPacket.localObservation m₂ 1 (capIndex.wk projection) (markerIndex.wk projection) =
        some (MixedPacket.values (chosen.st.heap.get (old.wk chosen.ext)).1
          (TEnv.get (markerIndex.wk projection) mid.st.env)) := by
  obtain ⟨m₂,base₂,target,reached,stack,addresses,growth,pointer,array⟩ :=
    CallerPacketControls.selected_client repr₁ capacity₁
  have cap := MixedPacket.captured (σ := mid.st) chosen projection complete_caller_frame
    reached addresses capIndex old old_inputs.1 markerIndex
  exact ⟨m₂,base₂,target,reached,stack,addresses,growth,pointer,cap.2.2.1,cap.2.2.2.1⟩

/-- Complete160byte mixed and preserved128byte standalone observations refer to
ONE reached machine after an actual nonempty compiled prefix and selected call. -/
theorem application : ∃ (m₁ m₂ : Machine) (base₁ base₂ : Nat → Fin W),
    Evm.run seed.code machine = .ok m₁ 0 ∧ Evm.run checked.code m₁ = .ok m₂ 0 ∧
    Evm.run (seed.code ++ checked.code) machine = .ok m₂ 0 ∧
    StateRepr 1 1 64 checked.frag chosen.st base₂ m₂ ∧ BaseExtends mid.st.H base₁ base₂ ∧
    GrowsAllocator 1 64 (checked.cost mid.st) mid.st base₁ m₁ chosen.st base₂ m₂ ∧
    m₁.stack = [w[77]] ∧ m₂.stack = [w[77]] ∧
    m₂.mem (cellOf 1 (capIndex.wk projection)) = .val (base₁ old.id) ∧
    m₂.mem (cellOf 1 (markerIndex.wk projection)) = w[42] ∧ m₂.store (.root 0) = 11 ∧
    (MixedPacket.localObservation m₂ 1 (capIndex.wk projection) (markerIndex.wk projection)).map
      AbiEntry.encodeArgs = some packet ∧
    (WordArrayPacket.localObservation m₂ 1 (capIndex.wk projection)).map AbiEntry.encodeArgs =
      some CallerPacketControls.packet := by
  obtain ⟨m₁,base₁,prefixRun,repr₁,growth₁,capacity₁,stack₁⟩ := CallerPacketControls.prefix_client
  obtain ⟨m₂,base₂,target,repr₂,stack₂,addresses,growth₂,pointer,scalar,observed⟩ :=
    selected_client repr₁ capacity₁
  have mixed : (MixedPacket.localObservation m₂ 1 (capIndex.wk projection) (markerIndex.wk projection)).map
      AbiEntry.encodeArgs = some packet := by rw [observed,Option.map_some,encoded_current]
  have reference := CallerView.reference (σ := mid.st) chosen projection complete_caller_frame capIndex old old_inputs.1
  have standalone := (WordArrayPacket.local_complete repr₂ (capIndex.wk projection) (old.wk chosen.ext) reference).2.2.1
  have oldPacket : (WordArrayPacket.localObservation m₂ 1 (capIndex.wk projection)).map AbiEntry.encodeArgs =
      some CallerPacketControls.packet := by rw [standalone,Option.map_some,CallerPacketControls.encoded_current]
  exact ⟨m₁,m₂,base₁,base₂,prefixRun,target,by rw [run_append_ok prefixRun,target],repr₂,addresses,
    growth₂,stack₁,stack₂.trans stack₁,pointer,(CallerPacketControls.scalar_fields repr₂).1,
    (CallerPacketControls.scalar_fields repr₂).2,mixed,oldPacket⟩

/-- The old alias remains different from private and other represented objects,
while the observed heterogeneous packet includes the actual retained marker. -/
theorem aliases : ∃ (m₁ m₂ : Machine) (base₂ : Nat → Fin W),
    Evm.run seed.code machine = .ok m₁ 0 ∧ Evm.run checked.code m₁ = .ok m₂ 0 ∧
    (MixedPacket.localObservation m₂ 1 (capIndex.wk projection) (markerIndex.wk projection)).map
      AbiEntry.encodeArgs = some packet ∧
    m₂.mem (cellOf 1 (capIndex.wk projection)) ≠ .val (base₂ privateNew.id) ∧
    m₂.mem (cellOf 1 (capIndex.wk projection)) ≠ .val (base₂ other.id) := by
  obtain ⟨m₁,m₂,base₁,base₂,prefixRun,target,whole,repr,addresses,growth,s₁,s₂,ptr,marker,store,mixed,standalone⟩ := application
  exact ⟨m₁,m₂,base₂,prefixRun,target,mixed,
    CallerView.different_array (σ := mid.st) chosen projection complete_caller_frame repr
      capIndex old old_inputs.1 privateNew (by decide +kernel),
    CallerView.different_array (σ := mid.st) chosen projection complete_caller_frame repr
      capIndex old old_inputs.1 (other.wk chosen.ext) (by decide +kernel)⟩

/-- Actual prefix and reached allocation relations remain coupled to the mixed
packet. These cursors/costs describe word cells, not physical byte EVM resources. -/
theorem resources : ∃ (m₁ m₂ : Machine) (base₂ : Nat → Fin W),
    Evm.run seed.code machine = .ok m₁ 0 ∧ Evm.run checked.code m₁ = .ok m₂ 0 ∧
    GrowsAllocator 1 64 11 (State.init C) bases machine chosen.st base₂ m₂ ∧
    m₁.mem 0 = w[135] ∧ m₂.mem 0 = w[139] ∧ m₂.stack = [w[77]] ∧
    (MixedPacket.localObservation m₂ 1 (capIndex.wk projection) (markerIndex.wk projection)).map
      AbiEntry.encodeArgs = some packet := by
  obtain ⟨m₁,base₁,prefixRun,repr₁,growth₁,capacity₁,stack₁⟩ := CallerPacketControls.prefix_client
  obtain ⟨m₂,base₂,target,repr₂,stack₂,addresses,growth₂,pointer,scalar,observed⟩ :=
    selected_client repr₁ capacity₁
  have growth := growth₁.comp growth₂
  rw [seed_cost,reached_cost] at growth
  rw [seed_cost] at growth₁
  have c₁ := (growth₁ (wmod 128) (by decide) initial_repr.2 (by decide +kernel)).arrays.free.cell
  have c₂ := (growth (wmod 128) (by decide) initial_repr.2 (by decide +kernel)).arrays.free.cell
  change m₁.mem 0 = w[135] at c₁
  change m₂.mem 0 = w[139] at c₂
  refine ⟨m₁,m₂,base₂,prefixRun,target,growth,c₁,c₂,stack₂.trans stack₁,?_⟩
  rw [observed,Option.map_some,encoded_current]

/-- Source storage11 is NOT scalar marker42. Changed-marker claims are rejected
in the same actual result whose complete mixed packet is observed. -/
theorem marker_not_storage : ∃ (m₁ m₂ : Machine),
    Evm.run seed.code machine = .ok m₁ 0 ∧ Evm.run checked.code m₁ = .ok m₂ 0 ∧
    m₂.mem 1 = w[42] ∧ m₂.store (.root 0) = 11 ∧ m₂.mem 1 ≠ w[11] ∧
    (MixedPacket.localObservation m₂ 1 (capIndex.wk projection) (markerIndex.wk projection)).map
      AbiEntry.encodeArgs = some packet := by
  obtain ⟨m₁,m₂,base₁,base₂,prefixRun,target,whole,repr,addresses,growth,s₁,s₂,ptr,marker,store,mixed,standalone⟩ := application
  change m₂.mem 1 = w[42] at marker
  exact ⟨m₁,m₂,prefixRun,target,marker,store,by rw [marker]; decide +kernel,mixed⟩

/-- Post-execution value-specialized literal emission on a SEPARATE byte-slice
machine. No compiled runtime word-memory reader or cross-machine simulation. -/
theorem literal_result : ∃ (m₁ m₂ : Machine),
    Evm.run seed.code machine = .ok m₁ 0 ∧ Evm.run checked.code m₁ = .ok m₂ 0 ∧
    MixedPacket.observedPacket m₂ 1 (capIndex.wk projection) (markerIndex.wk projection)
      17 EnumControls.suffix EnumControls.machine =
      some ({EnumControls.machine with memory := (Backend.Failure.Slice.putBytes
        EnumControls.machine.memory 17 packet)},some (.success packet)) := by
  obtain ⟨m₁,m₂,base₁,base₂,prefixRun,target,whole,repr,addresses,growth,s₁,s₂,ptr,marker,store,mixed,standalone⟩ := application
  have reference := CallerView.reference (σ := mid.st) chosen projection complete_caller_frame capIndex old old_inputs.1
  have encoding : AbiEntry.encodeArgs (MixedPacket.values (chosen.st.heap.get (old.wk chosen.ext)).1
      (TEnv.get (markerIndex.wk projection) chosen.st.env)) = packet := by
    simpa only [entry_marker,reached_marker] using encoded_current
  have emitted := MixedPacket.execute_observed repr (capIndex.wk projection) (old.wk chosen.ext) reference
    (markerIndex.wk projection) 17 EnumControls.suffix EnumControls.machine
    (by rw [encoding]; unfold Backend.Failure.Fits; decide +kernel) (by decide +kernel)
  rw [encoding] at emitted
  exact ⟨m₁,m₂,prefixRun,target,emitted⟩

/-- info: 'Solidity.Backend.AbiWorld.MixedPacketControls.selected_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected_client
/-- info: 'Solidity.Backend.AbiWorld.MixedPacketControls.application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms application
/-- info: 'Solidity.Backend.AbiWorld.MixedPacketControls.aliases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms aliases
/-- info: 'Solidity.Backend.AbiWorld.MixedPacketControls.resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resources
/-- info: 'Solidity.Backend.AbiWorld.MixedPacketControls.marker_not_storage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms marker_not_storage
/-- info: 'Solidity.Backend.AbiWorld.MixedPacketControls.literal_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms literal_result
end Solidity.Backend.AbiWorld.MixedPacketControls
