import Solidity.Backend.AbiWorld.EntryTransport
import Solidity.Semantics.AbiEntryChecks

/-! Actual entry/typed body/emitter controls using the published codec and
published vector constructors unchanged. No compiler coverage is inferred. -/
namespace Solidity.Backend.AbiWorld.EntryControls
open AbiEntry EntryTransport
open AbiEntry.Checks (cd arr2 u256 u8 neg lazyOnly lazyFail panic41)

def nestedInput : Input := cd [32,1,32,1,23]
def overlapInput : Input := cd [32,2,64,64,1,23]
def lazyInput : Input := cd [32,1,neg 32]
def reading : List Param := [{shape := .array (.array u256), loc := .calldata, readsOnly := true}]
def unpadded : Input := cd [32,3] [66,0,254]
def bytesParams (loc : Loc) : List Param := [{shape := .bytes, loc}]

/-- Canonical diagnostic representation of typed values, not an executed
source body that copies/encodes a readsOnly calldata parameter. -/
def bodyBytes (I : Input) (ps : List Param) := bodyObservation I 64 ps encodeArgs

theorem option_get {α : Type} (x : Option α) (h : x.isSome = true) : x = some (x.get h) := by
  cases x with
  | none => cases h
  | some x => rfl

def actualNested : Vals ((arr2 .calldata).map Param.shape) :=
  (bodyObservation nestedInput 64 (arr2 .calldata) id).get (by decide +kernel)
attribute [irreducible] actualNested

theorem actual_nested_verdict : verdict nestedInput 64 (arr2 .calldata) = .run actualNested := by
  apply verdict_of_values
  unfold actualNested
  exact option_get _ _

/-- The accepted aggregate is extracted from an actual verdict, with actual
entry and body-values witnesses; not an arbitrary typed expected fixture. -/
theorem actual_nested_witness : ∃ es,
    entry nestedInput 64 (arr2 .calldata) = .ok es ∧
    bodyValues nestedInput 64 (arr2 .calldata) es 0 = .ok actualNested ∧
    bodyBytes nestedInput (arr2 .calldata) = some (encodeArgs actualNested) :=
  body_witness actualNested encodeArgs actual_nested_verdict

/-- Full ordered diagnostic value observations: canonical eager/lazy agreement, accepted
overlap normalization, a lazy-only negative-relative-offset layout and unpadded
bytes with an embedded zero. No input bytes are replaced in the entry check. -/
theorem accepted_ordered :
    bodyBytes nestedInput (arr2 .memory) = some (nestedInput.data.drop 4) ∧
    bodyBytes nestedInput (arr2 .calldata) = some (nestedInput.data.drop 4) ∧
    bodyBytes overlapInput (arr2 .calldata) = some ((cd [32,2,64,128,1,23,1,23]).data.drop 4) ∧
    bodyBytes lazyInput reading = some ((cd [32,1,32,1,neg 32]).data.drop 4) ∧
    bodyBytes unpadded (bytesParams .memory) =
      some ((cd [32,3] ([66,0,254] ++ List.replicate 29 0)).data.drop 4) ∧
    bodyBytes unpadded (bytesParams .calldata) =
      some ((cd [32,3] ([66,0,254] ++ List.replicate 29 0)).data.drop 4) := by decide +kernel

/-- These accepted lazy-only inputs are never mislabeled as certified reverts. -/
theorem accepted_not_rejected :
    rejection lazyInput 64 reading 17 = none ∧
    rejection overlapInput 64 (arr2 .calldata) 17 = none ∧
    rejection unpadded 64 (bytesParams .calldata) 17 = none := by decide +kernel

def lazyCopy : Input := cd [32,1,neg 32]
def accessFailure : Input := cd [32,1,4096]
def allocation : Input := cd [32,2^64]

/-- All refusal names stay distinct, including access-time failure after entry.
Allocation Panic and exhausted fuel are not certified empty reverts. -/
theorem named_blocked :
    (verdict lazyCopy 64 (arr2 .calldata)).kind = "blocked: " ++ lazyOnly ∧
    (verdict accessFailure 64 reading).kind = "blocked: " ++ lazyFail ∧
    (verdict allocation 64 (bytesParams .memory)).kind = "blocked: " ++ panic41 ∧
    (verdict nestedInput 0 (arr2 .memory)).kind = "blocked: ABI decoder fuel exhausted" ∧
    rejection lazyCopy 64 (arr2 .calldata) 17 = none ∧
    rejection accessFailure 64 reading 17 = none ∧
    rejection allocation 64 (bytesParams .memory) 17 = none ∧
    rejection nestedInput 0 (arr2 .memory) 17 = none := by decide +kernel

def machine : Failure.Slice.Machine := ⟨[⟨77, by decide +kernel⟩], fun _ => 0xa5⟩
def suffix : Program := [.op .RETURN]
def malformed : Input := cd [32,1,256]
def narrowMemory : List Param := [{shape := .array u8, loc := .memory}]
def truncated : Input := { data := [0,0,0,0] ++ (wordBytes 32).take 31, free := 2^32 }

theorem malformed_entry : entry malformed 64 narrowMemory = .error .revert := by rfl
theorem truncated_verdict : verdict truncated 64 (arr2 .calldata) = .revert := by rfl

/-- Actual aggregate validation failure executes the actual existing emitter,
with nonzero offset, nonempty old stack, arbitrary old memory and an unreachable
RETURN suffix. No marker pair of standalone decode/emission propositions. -/
theorem malformed_emitted : runRejection malformed 64 narrowMemory 17 suffix machine =
    some (machine, some (.revert [])) :=
  entry_revert_exec malformed 64 narrowMemory 17 suffix machine malformed_entry
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩ (by decide +kernel)

theorem truncated_emitted : runRejection truncated 64 (arr2 .calldata) 17 suffix machine =
    some (machine, some (.revert [])) :=
  verdict_revert_exec truncated 64 (arr2 .calldata) 17 suffix machine truncated_verdict
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩ (by decide +kernel)

/-- Stack safety is real: with only one cell spare the two PUSHes fail closed. -/
theorem stack_exhausted : runRejection malformed 64 narrowMemory 17 suffix
    {machine with stack := List.replicate 1023 ⟨77, by decide +kernel⟩} = none := by
  have hv := (verdict_revert_iff malformed 64 narrowMemory).2 malformed_entry
  have hs : Failure.Slice.stackSafe (Failure.emit 17 .empty ++ suffix)
      {machine with stack := List.replicate 1023 ⟨77, by decide +kernel⟩} = false := by decide +kernel
  simp only [runRejection, rejection, hv, Option.bind_some, Failure.Slice.checkedRun,
    hs, Bool.false_eq_true, ite_false]

theorem wrong_byte_order : bodyBytes nestedInput (arr2 .calldata) ≠
    some ((cd [32,1,32,1,24]).data.drop 4) := by
  rw [accepted_ordered.2.1]
  decide +kernel


theorem successful {ε α : Type} (x : Except ε α) (h : x.toOption.isSome = true) :
    x = .ok (x.toOption.get h) := by
  cases x with
  | error e => cases h
  | ok v => rfl

def eagerNested : Val (.array (.array u256)) :=
  (eager nestedInput 64 (.array (.array u256)) 0).toOption.get (by decide +kernel)
attribute [irreducible] eagerNested

theorem actual_eager : eager nestedInput 64 (.array (.array u256)) 0 = .ok eagerNested := by
  unfold eagerNested
  exact successful _ _

theorem except_some {ε α : Type} (x : Except ε α) (v : α) (h : x.toOption = some v) :
    x = .ok v := by
  cases x with
  | error e => cases h
  | ok a => cases h; rfl

theorem nested_reference : cref nestedInput (.array (.array u256)) 4 0 = .ok (68,1) :=
  except_some _ _ (by decide +kernel)

/-- Real eager decoding, entry reference, body values and lazy read all share
one actual typed aggregate. The published fuel decrement and size bound remain. -/
theorem actual_calldata_handoff :
    bodyBytes nestedInput (arr2 .calldata) = some (encodeArgs (.cons eagerNested .nil)) ∧
    cval nestedInput 63 (.array (.array u256)) 68 1 = .ok eagerNested := by
  exact calldata_handoff nestedInput 63 (.array (.array u256)) 68 1 eagerNested encodeArgs
    (by decide +kernel)
    (single_calldata_entry nestedInput 64 _ 68 1 (by decide +kernel) nested_reference)
    nested_reference actual_eager

/-- The complete ordered eager result is the nested aggregate tail, not a
three-cell truncation or a replacement expected-value fixture. -/
theorem eager_ordered : encodeArgs (.cons eagerNested .nil) = nestedInput.data.drop 4 := by decide +kernel


/-- A length-only typed observation, using recursors generalized over every
index (Gate G0). No element-value traversal, memory copy or whole-aggregate encoding. -/
def valueLength {s : Shape} (v : Val s) : Nat :=
  Val.casesOn (motive_1 := fun _ _ => Nat) v
    (fun _ => 0) (fun bs => bs.length)
    (fun {_} {n} _ => n) (fun {_} {n} _ => n) (fun _ => 0)

def firstLength {ss : List Shape} (vs : Vals ss) : Option Nat :=
  Vals.casesOn (motive_3 := fun _ _ => Option Nat) vs none (fun v _ => some (valueLength v))

/-- Accepted lazy-only input supports the permitted length-only observation;
copying bodies remain named blocked in named_blocked. -/
theorem lazy_length_body :
    bodyObservation lazyInput 64 reading firstLength = some (some 1) ∧
    bodyObservation overlapInput 64 (arr2 .calldata) firstLength = some (some 2) := by decide +kernel

/-- info: 'Solidity.Backend.AbiWorld.EntryControls.actual_nested_witness' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms actual_nested_witness
/-- info: 'Solidity.Backend.AbiWorld.EntryControls.actual_calldata_handoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_calldata_handoff
/-- info: 'Solidity.Backend.AbiWorld.EntryControls.malformed_emitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms malformed_emitted
/-- info: 'Solidity.Backend.AbiWorld.EntryControls.truncated_emitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms truncated_emitted
/-- info: 'Solidity.Backend.AbiWorld.EntryControls.lazy_length_body' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms lazy_length_body
/-- info: 'Solidity.Backend.AbiWorld.EntryControls.named_blocked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_blocked

end Solidity.Backend.AbiWorld.EntryControls
