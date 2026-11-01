import Solidity.Backend.AbiWorld.CallerPacket
import tests.«internal-flow».FiniteDispatchEndpoint

/-! New codec consequences of the actual sealed producer fixture, not another
fixture evaluator. The seedRun, selected call, body, tail and compiler certificates
are reused unchanged. No byte-memory target execution is asserted. -/
namespace Solidity.Backend.AbiWorld.CallerPacketControls
open Evm Evm.Memory InternalFlow
open InternalFlow.MemoryDispatchChecks
open InternalFlow.MemoryDispatchChecks.ProtectedTail

def packet : List UInt8 := AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes 2 ++
  AbiEntry.wordBytes 12 ++ AbiEntry.wordBytes 11

theorem current_words :
    (chosen.st.heap.get (old.wk chosen.ext)).1 =
      [indexValue (wmod 12),indexValue (wmod 11)] := by
  apply (List.map_inj_right (f := fun v : PrimTy.uint.Denote => v.val)
    (fun x y h => Subtype.ext h)).mp
  decide +kernel

theorem encoded_current :
    AbiEntry.encodeArgs (WordArrayPacket.values (chosen.st.heap.get (old.wk chosen.ext)).1) =
      packet := by
  rw [WordArrayPacket.encoded_values,current_words]
  decide +kernel

/-- The selected direct call and its actual scoped tail instantiate the generic
consumer. Entry repr/capacity are discharged by the real prefix below. -/
theorem selected_client {m₁ : Machine} {base₁ : Nat → Fin W}
    (repr₁ : StateRepr 1 1 64 seed.frag mid.st base₁ m₁)
    (capacity₁ : AllocationInput 1 64 (checked.cost mid.st) mid.st base₁ m₁) :
    ∃ (m₂ : Machine) (base₂ : Nat → Fin W),
    Evm.run checked.code m₁ = .ok m₂ 0 ∧
    StateRepr 1 1 64 checked.frag chosen.st base₂ m₂ ∧
    m₂.stack = m₁.stack ∧ BaseExtends mid.st.H base₁ base₂ ∧
    GrowsAllocator 1 64 (checked.cost mid.st) mid.st base₁ m₁ chosen.st base₂ m₂ ∧
    m₂.mem (cellOf 1 (capIndex.wk projection)) = .val (base₁ old.id) ∧
    WordArrayPacket.localObservation m₂ 1 (capIndex.wk projection) =
      some (WordArrayPacket.values (chosen.st.heap.get (old.wk chosen.ext)).1) := by
  obtain ⟨m₂,base₂,target,reached,stack,addresses,growth,pointer,observed,bytes⟩ :=
    CallerPacket.selected (executed := body_run) projection (by trivial)
      tail_within (by exact tail_unwritten) actualSecond.cond [actualFirst] [] .revert checked
      mid.st (by intro a h; have ha := List.mem_singleton.mp h; subst a; exact first_miss)
      second_hit armOut repr₁ room capacity₁ capIndex old old_inputs.1
  exact ⟨m₂,base₂,target,reached,stack,addresses,growth,pointer,observed⟩

/-- The actual prefix supplies a populated heap, input representation and the
remaining capacity; this is not an empty-entry BaseExtends application. -/
theorem prefix_client : ∃ (m₁ : Machine) (base₁ : Nat → Fin W),
    Evm.run seed.code machine = .ok m₁ 0 ∧
    StateRepr 1 1 64 seed.frag mid.st base₁ m₁ ∧
    GrowsAllocator 1 64 (seed.cost (State.init C)) (State.init C) bases machine mid.st base₁ m₁ ∧
    AllocationInput 1 64 (checked.cost mid.st) mid.st base₁ m₁ ∧ m₁.stack = [w[77]] := by
  obtain ⟨m₁,base₁,seedRun,repr₁,stack₁,extends₁,growth₁⟩ :=
    PublishedDirectCalls.program_endpoint seed initial_repr.1 seed_frame
      (capacity.of_le (Nat.le_add_right _ _)) mid seed_run
  exact ⟨m₁,base₁,seedRun,repr₁,growth₁,growth₁.nextInput capacity,stack₁⟩

/-- Both actual runs and the exact complete current codec packet. -/
theorem application : ∃ (m₁ m₂ : Machine) (base₁ base₂ : Nat → Fin W),
    Evm.run seed.code machine = .ok m₁ 0 ∧
    Evm.run checked.code m₁ = .ok m₂ 0 ∧
    Evm.run (seed.code ++ checked.code) machine = .ok m₂ 0 ∧
    StateRepr 1 1 64 seed.frag mid.st base₁ m₁ ∧
    StateRepr 1 1 64 checked.frag chosen.st base₂ m₂ ∧
    BaseExtends mid.st.H base₁ base₂ ∧
    GrowsAllocator 1 64 (checked.cost mid.st) mid.st base₁ m₁ chosen.st base₂ m₂ ∧
    m₁.stack = [w[77]] ∧ m₂.stack = [w[77]] ∧
    m₂.mem (cellOf 1 (capIndex.wk projection)) = .val (base₁ old.id) ∧
    WordArrayPacket.localObservation m₂ 1 (capIndex.wk projection) =
      some (WordArrayPacket.values (chosen.st.heap.get (old.wk chosen.ext)).1) ∧
    (WordArrayPacket.localObservation m₂ 1 (capIndex.wk projection)).map AbiEntry.encodeArgs =
      some packet := by
  obtain ⟨m₁,base₁,seedRun,repr₁,growth₁,capacity₁,stack₁⟩ := prefix_client
  obtain ⟨m₂,base₂,target,repr₂,stack₂,addresses,growth₂,pointer,observed⟩ :=
    selected_client repr₁ capacity₁
  have current : (WordArrayPacket.localObservation m₂ 1 (capIndex.wk projection)).map
      AbiEntry.encodeArgs = some packet := by
    rw [observed,Option.map_some,encoded_current]
  exact ⟨m₁,m₂,base₁,base₂,seedRun,target,by rw [run_append_ok seedRun,target],
    repr₁,repr₂,addresses,growth₂,stack₁,stack₂.trans stack₁,pointer,observed,current⟩

/-- Exact resource observation of the same actual prefix and selected call.
Costs and cursors are word-cell facts, not physical EVM gas adequacy. -/
theorem resource_client : ∃ (m₁ m₂ : Machine) (base₂ : Nat → Fin W),
    Evm.run seed.code machine = .ok m₁ 0 ∧ Evm.run checked.code m₁ = .ok m₂ 0 ∧
    GrowsAllocator 1 64 11 (State.init C) bases machine chosen.st base₂ m₂ ∧
    m₁.mem 0 = w[135] ∧ m₂.mem 0 = w[139] ∧ m₂.stack = [w[77]] ∧
    (WordArrayPacket.localObservation m₂ 1 (capIndex.wk projection)).map AbiEntry.encodeArgs =
      some packet := by
  obtain ⟨m₁,base₁,seedRun,repr₁,growth₁,capacity₁,stack₁⟩ := prefix_client
  obtain ⟨m₂,base₂,target,repr₂,stack₂,addresses,growth₂,pointer,observed⟩ :=
    selected_client repr₁ capacity₁
  have growth := growth₁.comp growth₂
  rw [seed_cost,reached_cost] at growth
  rw [seed_cost] at growth₁
  have cursor₁ := (growth₁ (wmod 128) (by decide) initial_repr.2
    (by decide +kernel)).arrays.free.cell
  have cursor₂ := (growth (wmod 128) (by decide) initial_repr.2
    (by decide +kernel)).arrays.free.cell
  change m₁.mem 0 = w[135] at cursor₁
  change m₂.mem 0 = w[139] at cursor₂
  refine ⟨m₁,m₂,base₂,seedRun,target,growth,cursor₁,cursor₂,stack₂.trans stack₁,?_⟩
  rw [observed,Option.map_some,encoded_current]

private theorem uint_word {v : PrimTy.uint.Denote} {w : Evm.Word} {n : Fin W}
    (repr : ReprV .uint v w) (value : v.1 = (n.val : Int)) : w = .val n := by
  obtain ⟨a,hw,ha⟩ := repr
  have he : a = n := Fin.ext (Int.ofNat_inj.mp (ha.symm.trans value))
  exact hw.trans (congrArg Evm.Word.val he)

/-- Caller scalar42 is retained while the real callee changes storage9 to11. -/
theorem scalar_fields {m : Machine} {base : Nat → Fin W}
    (repr : StateRepr 1 1 64 checked.frag chosen.st base m) :
    m.mem 1 = w[42] ∧ m.store (.root 0) = 11 := by
  have marker := uint_word (n := wmod 42)
    (repr.core.vals (.there (.there (.there (.there (.there (.there (.there .here)))))) :
      Idx Caller (.val .uint))) (by decide +kernel)
  change m.mem 1 = w[42] at marker
  have storage := repr.core.store "count" (.prim .uint) rfl
  change ReprAt m.store 1 (.prim .uint) (rootSlot C "count")
    (chosen.st.storage.get (rfl : C.rootType "count" = some (.prim .uint))) at storage
  have value : chosen.st.storage.get (rfl : C.rootType "count" = some (.prim .uint)) =
      .prim (indexValue (wmod 11)) := by decide +kernel
  rw [value] at storage
  have cell : (.val (m.store.cells (.root 0)) : Evm.Word) = w[11] := by
    cases storage with | prim h => exact uint_word h rfl
  exact ⟨marker,congrArg Fin.val (Evm.Word.val.inj cell)⟩

/-- These scalar/store observations and the complete packet share one actual
compiled result, not independently selected existential machines. -/
theorem scalar_packet : ∃ (m₁ m₂ : Machine),
    Evm.run seed.code machine = .ok m₁ 0 ∧ Evm.run checked.code m₁ = .ok m₂ 0 ∧
    m₂.mem 1 = w[42] ∧ m₂.store (.root 0) = 11 ∧
    (WordArrayPacket.localObservation m₂ 1 (capIndex.wk projection)).map AbiEntry.encodeArgs =
      some packet := by
  obtain ⟨m₁,m₂,base₁,base₂,seedRun,target,whole,repr₁,repr₂,addresses,growth,
    stack₁,stack₂,pointer,observed,bytes⟩ := application
  exact ⟨m₁,m₂,seedRun,target,(scalar_fields repr₂).1,(scalar_fields repr₂).2,bytes⟩

/-- The same actual target result rejects a distinct older object and private
callee allocation. Positive codec observation is part of the same witness. -/
theorem alias_negatives : ∃ (m₁ m₂ : Machine) (base₂ : Nat → Fin W),
    Evm.run seed.code machine = .ok m₁ 0 ∧ Evm.run checked.code m₁ = .ok m₂ 0 ∧
    (WordArrayPacket.localObservation m₂ 1 (capIndex.wk projection)).map AbiEntry.encodeArgs =
      some packet ∧
    m₂.mem (cellOf 1 (capIndex.wk projection)) ≠ .val (base₂ privateNew.id) ∧
    m₂.mem (cellOf 1 (capIndex.wk projection)) ≠ .val (base₂ other.id) ∧
    m₂.mem (cellOf 1 (capIndex.wk projection)) ≠ .val (base₂ sharedDefault.id) := by
  obtain ⟨m₁,m₂,base₁,base₂,seedRun,target,whole,repr₁,repr₂,addresses,growth,
    stack₁,stack₂,pointer,observed,bytes⟩ := application
  exact ⟨m₁,m₂,base₂,seedRun,target,bytes,
    CallerView.different_array (σ := mid.st) chosen projection complete_caller_frame
      repr₂ capIndex old old_inputs.1 privateNew (by decide +kernel),
    CallerView.different_array (σ := mid.st) chosen projection complete_caller_frame
      repr₂ capIndex old old_inputs.1 (other.wk chosen.ext) (by decide +kernel),
    CallerView.different_array (σ := mid.st) chosen projection complete_caller_frame
      repr₂ capIndex old old_inputs.1 (sharedDefault.wk chosen.ext) (by decide +kernel)⟩

/-- Complete byte order, offset and length, paired with stale/order/private
counterclaims. These are codec observations, not additional admission rules. -/
theorem ordered_bytes :
    packet.length = 128 ∧ packet.take 32 = AbiEntry.wordBytes 32 ∧
    (packet.drop 32).take 32 = AbiEntry.wordBytes 2 ∧
    packet.drop 64 = AbiEntry.wordBytes 12 ++ AbiEntry.wordBytes 11 ∧
    packet ≠ AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes 2 ++
      AbiEntry.wordBytes 11 ++ AbiEntry.wordBytes 12 ∧
    packet ≠ AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes 2 ++
      AbiEntry.wordBytes 7 ++ AbiEntry.wordBytes 11 ∧
    packet ≠ AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes 2 ++
      AbiEntry.wordBytes 23 ++ AbiEntry.wordBytes 29 ∧
    packet ≠ AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes 2 ++
      AbiEntry.wordBytes 99 ++ AbiEntry.wordBytes 101 := by decide +kernel

/-- The nonempty entry and mutation are real source executions; selected-frame
transport intentionally does not preserve the whole caller environment. -/
theorem populated_mutation :
    seedProgram.run (State.init C) = .ok mid ∧
    actualSecond.body.run mid.st = .ok armOut ∧
    mid.st.H.length = 3 ∧ chosen.st.H.length = 5 ∧
    (mid.st.heap.get old).1 = [indexValue (wmod 7),indexValue (wmod 11)] ∧
    (chosen.st.heap.get (old.wk chosen.ext)).1 = [indexValue (wmod 12),indexValue (wmod 11)] ∧
    Prog.withinM .nonpayable actualSecond.body = false ∧
    chosen.st.env ≠ TEnv.wk chosen.ext Caller mid.st.env := by
  exact ⟨seed_run,body_run,by decide +kernel,by decide +kernel,
    by
      apply (List.map_inj_right (f := fun v : PrimTy.uint.Denote => v.val)
        (fun x y h => Subtype.ext h)).mp
      decide +kernel,current_words,whole_body_guard_stays_false,full_frame_changes⟩

/-- info: 'Solidity.Backend.AbiWorld.CallerPacketControls.current_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms current_words
/-- info: 'Solidity.Backend.AbiWorld.CallerPacketControls.encoded_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_current
/-- info: 'Solidity.Backend.AbiWorld.CallerPacketControls.selected_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected_client
/-- info: 'Solidity.Backend.AbiWorld.CallerPacketControls.prefix_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_client
/-- info: 'Solidity.Backend.AbiWorld.CallerPacketControls.application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms application
/-- info: 'Solidity.Backend.AbiWorld.CallerPacketControls.resource_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resource_client
/-- info: 'Solidity.Backend.AbiWorld.CallerPacketControls.scalar_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scalar_fields
/-- info: 'Solidity.Backend.AbiWorld.CallerPacketControls.scalar_packet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scalar_packet
/-- info: 'Solidity.Backend.AbiWorld.CallerPacketControls.alias_negatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms alias_negatives
/-- info: 'Solidity.Backend.AbiWorld.CallerPacketControls.ordered_bytes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms ordered_bytes
/-- info: 'Solidity.Backend.AbiWorld.CallerPacketControls.populated_mutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms populated_mutation
end Solidity.Backend.AbiWorld.CallerPacketControls
