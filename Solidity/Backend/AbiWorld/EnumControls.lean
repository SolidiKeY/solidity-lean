import Solidity.Backend.AbiWorld.EnumEntry
import Solidity.Backend.AbiWorld.EntryControls

/-! New actual enum-entry clients and packet emission controls. These are
kernel codec/byte-slice facts, not source admission or target decoder execution. -/
namespace Solidity.Backend.AbiWorld.EnumControls
open AbiEntry EntryTransport EnumEntry PacketEmission
open AbiEntry.Checks (cd u8)

def params (copy : Bool) : List Param :=
  [param 3, {shape := .array u8, loc := if copy then .memory else .calldata}]
def input : Input := cd [2,64,3,7,0,255]
def gap : Input := cd [2,96,0xabcdef,3,7,0,255]
def expected : List UInt8 := input.data.drop 4

def actual (copy : Bool) : Vals ((params copy).map Param.shape) :=
  (bodyObservation input 64 (params copy) id).get (by cases copy <;> decide +kernel)
attribute [irreducible] actual

theorem actual_verdict (copy : Bool) : verdict input 64 (params copy) = .run (actual copy) := by
  apply verdict_of_values
  unfold actual
  exact EntryControls.option_get _ _

/-- Both memory and calldata signatures carry actual entry/bodyValues witnesses. -/
theorem actual_body (copy : Bool) : ∃ es,
    entry input 64 (params copy) = .ok es ∧
    bodyValues input 64 (params copy) es 0 = .ok (actual copy) ∧
    bodyObservation input 64 (params copy) encodeArgs = some (encodeArgs (actual copy)) :=
  body_witness (actual copy) encodeArgs (actual_verdict copy)

theorem encoded (copy : Bool) : encodeArgs (actual copy) = expected := by
  cases copy <;> decide +kernel

/-- Complete byte order, relative offset64, length3, embedded zero and last255. -/
theorem complete_bytes : expected =
    wordBytes 2 ++ wordBytes 64 ++ wordBytes 3 ++ wordBytes 7 ++ wordBytes 0 ++ wordBytes 255 ∧
    expected.length = 192 ∧ (expected.drop 32).take 32 = wordBytes 64 := by
  decide +kernel

/-- A gap before the dynamic tail is accepted without changing the input;
its actual typed-body diagnostic encoding has the canonical offset64. -/
theorem noncanonical (copy : Bool) :
    bodyObservation gap 64 (params copy) encodeArgs = some expected ∧
    rejection gap 64 (params copy) 17 = none := by
  cases copy <;> decide +kernel

def machine : Backend.Failure.Slice.Machine :=
  ⟨[⟨77,by decide +kernel⟩, ⟨88,by decide +kernel⟩], fun _ => 0xa5⟩
def suffix : Backend.Program := [.op .REVERT]

/-- Actual emitted aggregate RETURN, including exact memory and older stack.
The appended REVERT is unreachable. This is value-specialized packet emission. -/
theorem returned (copy : Bool) :
    Backend.Failure.Slice.checkedRun (emitResult 17 (actual copy) ++ suffix) machine =
      some ({ machine with memory := Backend.Failure.Slice.putBytes machine.memory 17 expected },
        some (.success expected)) := by
  have h := execute_result 17 (actual copy) suffix machine
    (by rw [encoded]; unfold Backend.Failure.Fits; decide +kernel) (by decide +kernel)
  rw [encoded] at h
  exact h

/-- Custom-error selector bytes precede the SAME argument-relative packet. -/
theorem custom_encoded (copy : Bool) : customBytes 0x11223344 (actual copy) =
    [0x11,0x22,0x33,0x44] ++ expected := by
  rw [customBytes, encoded]
  rfl

theorem custom_reverted (copy : Bool) :
    Backend.Failure.Slice.checkedRun (emitCustom 17 0x11223344 (actual copy) ++ suffix) machine =
      some ({ machine with memory := (Backend.Failure.Slice.putBytes machine.memory 17 ([0x11,0x22,0x33,0x44] ++ expected)) },
        some (.revert ([0x11,0x22,0x33,0x44] ++ expected))) := by
  have h := execute_custom 17 0x11223344 (actual copy) suffix machine
    (by rw [custom_encoded]; unfold Backend.Failure.Fits; decide +kernel) (by decide +kernel)
  rw [custom_encoded] at h
  exact h

/-- These full byte baselines reject wrong selector/order/offset/length claims. -/
theorem negative_packets :
    (([0x11,0x22,0x33,0x44] ++ expected).drop 36).take 32 = wordBytes 64 ∧
    (([0x11,0x22,0x33,0x44] ++ expected).drop 36).take 32 ≠ wordBytes 68 ∧
    (expected.drop 64).take 32 ≠ wordBytes 2 ∧
    expected ≠ (cd [2,64,3,7,255,0]).data.drop 4 ∧
    ([0x11,0x22,0x33,0x44] ++ expected).take 4 ≠ [0x11,0x22,0x33,0x45] := by
  decide +kernel

def onePast : Input := cd [3,4096]
def dirtyHigh : Input := cd [2^248+2,64,0]
def missing : Input := cd []
def truncated : Input := cd [] (List.replicate 31 0)
def dirtyArray : Input := cd [2,64,1,256]
def huge (e : Nat) : Input := cd [e,64,2^64]

/-- uint8 admits3, while the actual nominal enum does not. High bits are
validated as part of the WHOLE word, never truncated to its low byte. -/
theorem cardinality_boundary : Kind.valid (.uint 8) 3 = true ∧
    Kind.valid (.enumBelow 3) 3 = false ∧
    load dirtyHigh.data 4 = 2^248+2 ∧
    load missing.data 4 = 0 ∧ load truncated.data 4 = 0 := by decide +kernel

/-- Invalid leading enum rejects before its tail; for copy=true this preempts
a would-be allocation Panic, while calldata uses its own tail checks. -/
theorem preempts_panic (copy : Bool) :
    entry (huge 3) 64 (params copy) = .error .revert :=
  invalid_entry (huge 3) 62 3 _ (by decide +kernel)

theorem one_past_revert (copy : Bool) :
    runRejection onePast 64 (params copy) 17 suffix machine =
      some (machine, some (.revert [])) :=
  invalid_revert onePast 62 3 _ (by decide +kernel) 17 suffix machine
    (by unfold Backend.Failure.Fits; decide +kernel) (by decide +kernel)

theorem dirty_high_revert (copy : Bool) :
    runRejection dirtyHigh 64 (params copy) 17 suffix machine =
      some (machine, some (.revert [])) :=
  invalid_revert dirtyHigh 62 3 _ (by decide +kernel) 17 suffix machine
    (by unfold Backend.Failure.Fits; decide +kernel) (by decide +kernel)

theorem missing_revert (copy : Bool) :
    runRejection missing 64 (params copy) 17 suffix machine =
      some (machine, some (.revert [])) := by
  apply truncated_revert missing 64 3 _ _ 17 suffix machine
    (by unfold Backend.Failure.Fits; decide +kernel) (by decide +kernel)
  cases copy <;> decide +kernel

theorem truncated_word_revert (copy : Bool) :
    runRejection truncated 64 (params copy) 17 suffix machine =
      some (machine, some (.revert [])) := by
  apply truncated_revert truncated 64 3 _ _ 17 suffix machine
    (by unfold Backend.Failure.Fits; decide +kernel) (by decide +kernel)
  cases copy <;> decide +kernel

/-- Dirty memory elements fail at entry; lazy element failures and allocation
Panic remain named BLOCKED cases, never certified empty reverts. -/
theorem mixed_negatives :
    runRejection dirtyArray 64 (params true) 17 suffix machine =
      some (machine, some (.revert [])) ∧
    (verdict dirtyArray 64 (params false)).kind =
      "blocked: calldata element fails only on access: needs access-time calldata semantics" ∧
    rejection dirtyArray 64 (params false) 17 = none ∧
    (verdict (huge 2) 64 (params true)).kind =
      "blocked: possible Panic(0x41) allocation failure in memory decoding" ∧
    rejection (huge 2) 64 (params true) 17 = none ∧
    (verdict input 0 (params true)).kind = "blocked: ABI decoder fuel exhausted" := by
  constructor
  · exact entry_revert_exec dirtyArray 64 (params true) 17 suffix machine
      ((rejection_iff dirtyArray 64 (params true) 17).1 (by decide +kernel))
      (by unfold Backend.Failure.Fits; decide +kernel) (by decide +kernel)
  · decide +kernel

/-- Actual older byte observations, plus a rejected stack-overflow execution. -/
theorem frame_and_stack (copy : Bool) :
    Backend.Failure.Slice.putBytes machine.memory 17 (encodeArgs (actual copy)) 16 = 0xa5 ∧
    Backend.Failure.Slice.putBytes machine.memory 17 (encodeArgs (actual copy)) 209 = 0xa5 ∧
    Backend.Failure.Slice.checkedRun (emitResult 17 (actual copy) ++ suffix)
      {machine with stack := List.replicate 1023 ⟨77,by decide +kernel⟩} = none := by
  refine ⟨?_, ?_, ?_⟩
  · rw [encoded]; decide +kernel
  · rw [encoded]; decide +kernel
  · have hs : Backend.Failure.Slice.stackSafe (emitResult 17 (actual copy) ++ suffix)
        {machine with stack := List.replicate 1023 ⟨77,by decide +kernel⟩} = false := by
      simp only [emitResult, encoded]
      decide +kernel
    simp only [Backend.Failure.Slice.checkedRun, hs, Bool.false_eq_true, ite_false]

/-- Empty array is accepted with its full96-byte tuple, never confused with
missing/truncated words. -/
theorem empty_aggregate (copy : Bool) :
    bodyObservation (cd [0,64,0]) 64 (params copy) encodeArgs =
      some ((cd [0,64,0]).data.drop 4) ∧
    rejection (cd [0,64,0]) 64 (params copy) 17 = none := by
  cases copy <;> decide +kernel

def eagerArray : Val (.array u8) :=
  (eager input 64 (.array u8) 32).toOption.get (by decide +kernel)
attribute [irreducible] eagerArray

/-- Actual calldata reference AFTER the enum has address100 and length3;
the same eager value is read with the published one-step fuel difference. -/
theorem mixed_lazy_reference :
    cref input (.array u8) 4 32 = .ok (100,3) ∧
    cval input 63 (.array u8) 100 3 = .ok eagerArray ∧
    Val.enc eagerArray = wordBytes 3 ++ wordBytes 7 ++ wordBytes 0 ++ wordBytes 255 := by
  have hr : cref input (.array u8) 4 32 = .ok (100,3) :=
    EntryControls.except_some _ _ (by decide +kernel)
  have he : eager input (63+1) (.array u8) 32 = .ok eagerArray := by
    unfold eagerArray
    exact EntryControls.successful _ _
  obtain ⟨addr,len,hc,hv⟩ := eager_cref (by decide +kernel : input.size ≤ lim) he
  rw [hr] at hc
  cases hc
  exact ⟨hr,hv,by decide +kernel⟩

/-- A single inhabited actual-entry/body-values to emitted aggregate endpoint.
The tuple is computed by the published decoder, not assumed as a fixture. -/
theorem accepted_emission (copy : Bool) :
    (∃ es, entry input 64 (params copy) = .ok es ∧
      bodyValues input 64 (params copy) es 0 = .ok (actual copy) ∧
      bodyObservation input 64 (params copy) encodeArgs = some expected) ∧
    Backend.Failure.Slice.checkedRun (emitResult 17 (actual copy) ++ suffix) machine =
      some ({ machine with memory := Backend.Failure.Slice.putBytes machine.memory 17 expected },
        some (.success expected)) := by
  have h := accepted_packet (actual copy) (actual_verdict copy) 17 suffix machine
    (by rw [encoded]; unfold Backend.Failure.Fits; decide +kernel) (by decide +kernel)
  simpa only [encoded] using h


/-- info: 'Solidity.Backend.AbiWorld.EnumControls.actual_body' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms actual_body
/-- info: 'Solidity.Backend.AbiWorld.EnumControls.accepted_emission' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_emission
/-- info: 'Solidity.Backend.AbiWorld.EnumControls.custom_reverted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms custom_reverted
/-- info: 'Solidity.Backend.AbiWorld.EnumControls.mixed_lazy_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_lazy_reference
/-- info: 'Solidity.Backend.AbiWorld.EnumControls.mixed_negatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_negatives
/-- info: 'Solidity.Backend.AbiWorld.EnumControls.one_past_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms one_past_revert

end Solidity.Backend.AbiWorld.EnumControls
