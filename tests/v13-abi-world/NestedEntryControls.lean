import tests.«v13-abi-world».NestedCodecControls

/-! Finite REAL intrinsic entry/body witnesses, not a source/native compiler
agreement, universal nested admission theorem, or runtime source encoder. -/
namespace Solidity.Backend.AbiWorld.NestedControls
open AbiEntry

def location (lazy : Bool) : AbiEntry.Loc := if lazy then .calldata else .memory
def params (lazy : Bool) : List AbiEntry.Param := [{shape := NestedUintPacket.Shape,loc := location lazy}]

def actualValues (lazy : Bool) : Vals ((params lazy).map Param.shape) :=
  (EntryTransport.bodyObservation mixedInput 64 (params lazy) id).get (by cases lazy <;> decide +kernel)
attribute [irreducible] actualValues

private theorem option_get {α : Type} (x : Option α) (h : x.isSome = true) : x = some (x.get h) := by
  cases x with
  | none => cases h
  | some x => rfl

theorem accepted (lazy : Bool) : verdict mixedInput 64 (params lazy) = .run (actualValues lazy) := by
  apply EntryTransport.verdict_of_values
  unfold actualValues
  exact option_get _ _

/-- Values are extracted from the real execution, rather than a desired fixture. -/
theorem entry_body (lazy : Bool) : ∃ es,
    entry mixedInput 64 (params lazy) = .ok es ∧
    bodyValues mixedInput 64 (params lazy) es 0 = .ok (actualValues lazy) ∧
    EntryTransport.bodyObservation mixedInput 64 (params lazy) encodeArgs = some (encodeArgs (actualValues lazy)) :=
  EntryTransport.body_witness (actualValues lazy) encodeArgs (accepted lazy)

theorem complete_body_observation (lazy : Bool) :
    EntryTransport.bodyObservation mixedInput 64 (params lazy) encodeArgs = some (mixedInput.data.drop 4) := by
  cases lazy <;> decide +kernel

/-- Complete codec bytes of the actual typed body values match the independently
proved generic nested fixture. This does not assume typed-value equality. -/
theorem actual_encoding (lazy : Bool) : encodeArgs (actualValues lazy) = encodeArgs (NestedUintPacket.values mixed) := by
  obtain ⟨es,he,hb,observed⟩ := entry_body lazy
  rw [complete_body_observation] at observed
  exact (Option.some.inj observed).symm.trans mixed_encoding.symm

/-- Fuel exhaustion remains a named blocked result, never a certified revert. -/
theorem fuel_boundary : (verdict mixedInput 0 (params false)).kind =
    "blocked: ABI decoder fuel exhausted" ∧ EntryTransport.rejection mixedInput 0 (params false) 17 = none ∧
    mixedInput.size ≤ lim := by decide +kernel

/-- info: 'Solidity.Backend.AbiWorld.NestedControls.accepted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms accepted
/-- info: 'Solidity.Backend.AbiWorld.NestedControls.entry_body' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms entry_body
/-- info: 'Solidity.Backend.AbiWorld.NestedControls.actual_encoding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_encoding
/-- info: 'Solidity.Backend.AbiWorld.NestedControls.complete_body_observation' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms complete_body_observation
/-- info: 'Solidity.Backend.AbiWorld.NestedControls.fuel_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fuel_boundary
end Solidity.Backend.AbiWorld.NestedControls
