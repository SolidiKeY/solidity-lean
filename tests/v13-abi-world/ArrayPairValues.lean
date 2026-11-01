import tests.«v13-abi-world».ArrayPairCodecControls
import tests.«v13-abi-world».MixedPacketControls

/-! Actual retained reference/value facts for the existing populated selected
caller. There is no new source fixture engine or source admission assertion. -/
namespace Solidity.Backend.AbiWorld.ArrayPairControls
open Evm Evm.Memory InternalFlow
open InternalFlow.MemoryDispatchChecks
open InternalFlow.MemoryDispatchChecks.ProtectedTail

def lastIndex (same : Bool) : Idx View (.mem bytesR) := if same then sameIndex else otherIndex
def lastRef (same : Bool) : HRef mid.st.H bytesR := if same then old else other

theorem last_input (same : Bool) :
    TEnv.get ((lastIndex same).wk projection) mid.st.env = some (lastRef same) := by
  cases same
  · exact old_inputs.2.1
  · exact old_inputs.2.2.1

theorem first_current : (chosen.st.heap.get (old.wk chosen.ext)).1 = firstWords :=
  CallerPacketControls.current_words

theorem last_current (same : Bool) :
    (chosen.st.heap.get ((lastRef same).wk chosen.ext)).1 = lastWords same := by
  cases same
  · apply (List.map_inj_right (f := fun v : PrimTy.uint.Denote => v.val)
      (fun x y h => Subtype.ext h)).mp
    decide +kernel
  · exact CallerPacketControls.current_words

theorem encoded_current (same : Bool) :
    AbiEntry.encodeArgs (ArrayPairPacket.values (chosen.st.heap.get (old.wk chosen.ext)).1
      (chosen.st.heap.get ((lastRef same).wk chosen.ext)).1) = packet same := by
  rw [first_current,last_current]
  exact encoded same

theorem lengths (same : Bool) : chosen.st.heap.len (old.wk chosen.ext) .dyn = 2 ∧
    chosen.st.heap.len ((lastRef same).wk chosen.ext) .dyn = 2 := by
  constructor
  · simp only [Heap.len,MObj.elems_dyn,first_current]
    rfl
  · simp only [Heap.len,MObj.elems_dyn,last_current]
    cases same <;> rfl

/-- The two actual runtime headers are retained; equality of references is legal. -/
theorem headers (same : Bool) {m : Machine} {base : Nat → Fin W}
    (repr : StateRepr 1 1 64 checked.frag chosen.st base m) :
    m.mem (base old.id).val = w[2] ∧ m.mem (base (lastRef same).id).val = w[2] := by
  have h₁ := (repr.heap.arrays (old.wk chosen.ext)).length
  have h₂ := (repr.heap.arrays ((lastRef same).wk chosen.ext)).length
  rw [(lengths same).1] at h₁
  rw [(lengths same).2] at h₂
  exact ⟨h₁,h₂⟩

/-- Captured BOTH old aliases in the SAME reached representation. -/
theorem observed (same : Bool) {m : Machine} {base₁ base₂ : Nat → Fin W}
    (repr : StateRepr 1 1 64 checked.frag chosen.st base₂ m)
    (addresses : BaseExtends mid.st.H base₁ base₂) :
    m.mem (cellOf 1 (capIndex.wk projection)) = .val (base₁ old.id) ∧
    m.mem (cellOf 1 ((lastIndex same).wk projection)) = .val (base₁ (lastRef same).id) ∧
    (ArrayPairPacket.localObservation m 1 (capIndex.wk projection) ((lastIndex same).wk projection)).map
      AbiEntry.encodeArgs = some (packet same) := by
  have pair := ArrayPairPacket.captured (σ := mid.st) chosen projection complete_caller_frame
    repr addresses capIndex (lastIndex same) old (lastRef same) old_inputs.1 (last_input same)
  refine ⟨pair.1,pair.2.1,?_⟩
  rw [pair.2.2.1,Option.map_some,encoded_current]

/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.last_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms last_input
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.first_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms first_current
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.last_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms last_current
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.encoded_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_current
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.lengths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lengths
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.headers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms headers
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observed
end Solidity.Backend.AbiWorld.ArrayPairControls
