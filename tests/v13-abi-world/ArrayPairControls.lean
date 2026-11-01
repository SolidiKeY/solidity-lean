import tests.«v13-abi-world».ArrayPairValues

/-! Two-array observations of ONE actual compiled selected call/tail result.
Equal and distinct retained references coexist with all earlier packet facts.
No target byte encoder or external-world execution is asserted. -/
namespace Solidity.Backend.AbiWorld.ArrayPairControls
open Evm Evm.Memory InternalFlow
open InternalFlow.MemoryDispatchChecks
open InternalFlow.MemoryDispatchChecks.ProtectedTail

/-- Actual nonempty compiled prefix, selected call and tail; both pair packets
and both earlier packets share the very same reached machine and representation. -/
theorem application : ∃ (m₁ m₂ : Machine) (base₁ base₂ : Nat → Fin W),
    Evm.run seed.code machine = .ok m₁ 0 ∧ Evm.run checked.code m₁ = .ok m₂ 0 ∧
    Evm.run (seed.code ++ checked.code) machine = .ok m₂ 0 ∧
    StateRepr 1 1 64 checked.frag chosen.st base₂ m₂ ∧ BaseExtends mid.st.H base₁ base₂ ∧
    GrowsAllocator 1 64 (checked.cost mid.st) mid.st base₁ m₁ chosen.st base₂ m₂ ∧
    m₁.stack = [w[77]] ∧ m₂.stack = [w[77]] ∧
    m₂.mem (cellOf 1 (capIndex.wk projection)) = .val (base₁ old.id) ∧
    m₂.mem (cellOf 1 (sameIndex.wk projection)) = .val (base₁ old.id) ∧
    m₂.mem (cellOf 1 (otherIndex.wk projection)) = .val (base₁ other.id) ∧
    m₂.mem (base₂ old.id).val = w[2] ∧ m₂.mem (base₂ other.id).val = w[2] ∧
    m₂.mem 1 = w[42] ∧ m₂.store (.root 0) = 11 ∧
    (ArrayPairPacket.localObservation m₂ 1 (capIndex.wk projection) (sameIndex.wk projection)).map
      AbiEntry.encodeArgs = some (packet true) ∧
    (ArrayPairPacket.localObservation m₂ 1 (capIndex.wk projection) (otherIndex.wk projection)).map
      AbiEntry.encodeArgs = some (packet false) ∧
    (MixedPacket.localObservation m₂ 1 (capIndex.wk projection) (MixedPacketControls.markerIndex.wk projection)).map
      AbiEntry.encodeArgs = some MixedPacketControls.packet ∧
    (WordArrayPacket.localObservation m₂ 1 (capIndex.wk projection)).map AbiEntry.encodeArgs =
      some CallerPacketControls.packet := by
  obtain ⟨m₁,m₂,base₁,base₂,prefixRun,target,whole,repr,addresses,growth,s₁,s₂,pointer,marker,store,mixed,standalone⟩ :=
    MixedPacketControls.application
  have shared := observed true repr addresses
  have separate := observed false repr addresses
  have heads := headers false repr
  exact ⟨m₁,m₂,base₁,base₂,prefixRun,target,whole,repr,addresses,growth,s₁,s₂,
    pointer,shared.2.1,separate.2.1,heads.1,heads.2,marker,store,shared.2.2,separate.2.2,mixed,standalone⟩

/-- Positive observations accompany equal-address and distinct/private-reference
counterclaims on one actual result. No disjointness was required for the observer. -/
theorem aliases : ∃ (m₁ m₂ : Machine) (base₂ : Nat → Fin W),
    Evm.run seed.code machine = .ok m₁ 0 ∧ Evm.run checked.code m₁ = .ok m₂ 0 ∧
    (ArrayPairPacket.localObservation m₂ 1 (capIndex.wk projection) (sameIndex.wk projection)).map
      AbiEntry.encodeArgs = some (packet true) ∧
    (ArrayPairPacket.localObservation m₂ 1 (capIndex.wk projection) (otherIndex.wk projection)).map
      AbiEntry.encodeArgs = some (packet false) ∧
    m₂.mem (cellOf 1 (capIndex.wk projection)) = m₂.mem (cellOf 1 (sameIndex.wk projection)) ∧
    m₂.mem (cellOf 1 (capIndex.wk projection)) ≠ m₂.mem (cellOf 1 (otherIndex.wk projection)) ∧
    m₂.mem (cellOf 1 (capIndex.wk projection)) ≠ .val (base₂ privateNew.id) ∧
    m₂.mem (cellOf 1 (otherIndex.wk projection)) ≠ .val (base₂ privateNew.id) := by
  obtain ⟨m₁,m₂,base₁,base₂,prefixRun,target,whole,repr,addresses,growth,s₁,s₂,ptr,same,otherPtr,h₁,h₂,marker,store,
    pairSame,pairOther,mixed,standalone⟩ := application
  have otherReference := CallerView.reference (σ := mid.st) chosen projection complete_caller_frame
    otherIndex other old_inputs.2.1
  have otherReached := (WordArrayPacket.local_complete repr (otherIndex.wk projection)
    (other.wk chosen.ext) otherReference).1
  have apart := CallerView.different_array (σ := mid.st) chosen projection complete_caller_frame repr
    capIndex old old_inputs.1 (other.wk chosen.ext) (by decide +kernel)
  refine ⟨m₁,m₂,base₂,prefixRun,target,pairSame,pairOther,ptr.trans same.symm,?_,?_,?_⟩
  · rw [otherReached]
    exact apart
  · exact CallerView.different_array (σ := mid.st) chosen projection complete_caller_frame repr
      capIndex old old_inputs.1 privateNew (by decide +kernel)
  · exact CallerView.different_array (σ := mid.st) chosen projection complete_caller_frame repr
      otherIndex other old_inputs.2.1 privateNew (by decide +kernel)

/-- Both packets are coupled to the actual prefix and reached word-cell growth.
These are not byte-memory or physical EVM gas/resource adequacy claims. -/
theorem resources : ∃ (m₁ m₂ : Machine) (base₂ : Nat → Fin W),
    Evm.run seed.code machine = .ok m₁ 0 ∧ Evm.run checked.code m₁ = .ok m₂ 0 ∧
    GrowsAllocator 1 64 11 (State.init C) bases machine chosen.st base₂ m₂ ∧
    m₁.mem 0 = w[135] ∧ m₂.mem 0 = w[139] ∧ m₂.stack = [w[77]] ∧
    (ArrayPairPacket.localObservation m₂ 1 (capIndex.wk projection) (sameIndex.wk projection)).map
      AbiEntry.encodeArgs = some (packet true) ∧
    (ArrayPairPacket.localObservation m₂ 1 (capIndex.wk projection) (otherIndex.wk projection)).map
      AbiEntry.encodeArgs = some (packet false) := by
  obtain ⟨m₁,base₁,prefixRun,repr₁,growth₁,capacity₁,stack₁⟩ := CallerPacketControls.prefix_client
  obtain ⟨m₂,base₂,target,repr,stack₂,addresses,growth₂,pointer,observed⟩ :=
    CallerPacketControls.selected_client repr₁ capacity₁
  have shared := ArrayPairControls.observed true repr addresses
  have separate := ArrayPairControls.observed false repr addresses
  have growth := growth₁.comp growth₂
  rw [seed_cost,reached_cost] at growth
  rw [seed_cost] at growth₁
  have c₁ := (growth₁ (wmod 128) (by decide) initial_repr.2 (by decide +kernel)).arrays.free.cell
  have c₂ := (growth (wmod 128) (by decide) initial_repr.2 (by decide +kernel)).arrays.free.cell
  change m₁.mem 0 = w[135] at c₁
  change m₂.mem 0 = w[139] at c₂
  exact ⟨m₁,m₂,base₂,prefixRun,target,growth,c₁,c₂,stack₂.trans stack₁,shared.2.2,separate.2.2⟩

/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms application
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.aliases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms aliases
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resources
end Solidity.Backend.AbiWorld.ArrayPairControls
