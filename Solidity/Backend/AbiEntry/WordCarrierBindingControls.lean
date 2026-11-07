import Solidity.Backend.AbiEntry.WordCarrierBinding

/-! Enum and fixed-bytes carriers are bound only after actual validation.
The raw-byte controls preserve selectors, trailing bytes, fuel and saved state. -/
namespace Solidity.Backend.AbiEntry.WordCarrierBindingControls
open Solidity.Evm
open Interface (RouteCtx UIntBoundCtx singleWordParams rawArgumentWord uintBoundMachine wordCarrierOutcome)
private def C : Contract := {vars := []}
private def label : Fin W := wmod 99
private def compiled (kind : Solidity.AbiEntry.Kind) := WordCarrierBinding.compiled C 7 kind label
private def enumGood : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[2,0x77,0x88],free := 71}
private def enumBad : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[3],free := 71}
private def bytesGood : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12,0xab]++List.replicate 31 0++[0x77,0x88],free := 71}
private def bytesBad : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12,0xab]++List.replicate 30 0++[1],free := 71}
private def zero : Solidity.AbiEntry.Input := {data := List.replicate 36 0,free := 71}
private def machine (input : Solidity.AbiEntry.Input) : Machine :=
  {Machine.init with
    callvalue := wmod 17
    mem := fun address => if address=7 then .val (rawArgumentWord input)
      else if address=8 then .val (wmod input.size) else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def bound (input : Solidity.AbiEntry.Input) : Machine :=
  uintBoundMachine 7 label (rawArgumentWord input) (machine input)
private theorem actual (kind : Solidity.AbiEntry.Kind) (input : Solidity.AbiEntry.Input) :
    run (compiled kind).code (machine input)=
      wordCarrierOutcome 7 kind label (rawArgumentWord input) (wmod input.size) (machine input) :=
  WordCarrierBinding.executed C 7 kind label (compiled kind) (WordCarrierBinding.selected C 7 kind label)
    (machine input) _ _ rfl rfl
private theorem accept (kind : Solidity.AbiEntry.Kind) (input : Solidity.AbiEntry.Input)
    (full : ¬(wmod input.size).val<36) (valid : kind.valid (rawArgumentWord input).val=true) :
    run (compiled kind).code (machine input)=.ok (bound input) 0 := by
  simpa only [wordCarrierOutcome,if_neg full,if_pos valid] using actual kind input
private theorem reject (kind : Solidity.AbiEntry.Kind) (input : Solidity.AbiEntry.Input)
    (full : ¬(wmod input.size).val<36) (invalid : ¬kind.valid (rawArgumentWord input).val=true) :
    run (compiled kind).code (machine input)=.revert := by
  simpa only [wordCarrierOutcome,if_neg full,if_neg invalid] using actual kind input

theorem enum_raw_value_and_frame (fuel : Nat) :
    Solidity.AbiEntry.load enumGood.data 4=2 ∧ enumGood.size=38 ∧
    ∃ value : Solidity.AbiEntry.Word (.enumBelow 3),
      Solidity.AbiEntry.entry enumGood (fuel+2) (singleWordParams (.enumBelow 3))=
        .ok (.cons (.val (.word value)) .nil) ∧
      run (compiled (.enumBelow 3)).code (machine enumGood)=.ok (bound enumGood) 0 ∧
      (bound enumGood).mem (cellOf 7 (.here : Idx UIntBoundCtx (.val .uint)))=.val ⟨value.val,value.lt⟩ :=
  ⟨by decide,by decide,WordCarrierBinding.decoded_and_bound C 7 (.enumBelow 3) label
    (compiled (.enumBelow 3)) (WordCarrierBinding.selected C 7 (.enumBelow 3) label)
    enumGood fuel (machine enumGood) (wmod enumGood.size) rfl rfl (by decide) (by decide) (by decide)⟩

theorem bytes_raw_value_and_frame (fuel : Nat) :
    Solidity.AbiEntry.load bytesGood.data 4=0xab*2^248 ∧ bytesGood.size=38 ∧
    ∃ value : Solidity.AbiEntry.Word (.fixedBytes 1),
      Solidity.AbiEntry.entry bytesGood (fuel+2) (singleWordParams (.fixedBytes 1))=
        .ok (.cons (.val (.word value)) .nil) ∧
      run (compiled (.fixedBytes 1)).code (machine bytesGood)=.ok (bound bytesGood) 0 ∧
      (bound bytesGood).mem (cellOf 7 (.here : Idx UIntBoundCtx (.val .uint)))=.val ⟨value.val,value.lt⟩ :=
  ⟨by decide,by decide,WordCarrierBinding.decoded_and_bound C 7 (.fixedBytes 1) label
    (compiled (.fixedBytes 1)) (WordCarrierBinding.selected C 7 (.fixedBytes 1) label)
    bytesGood fuel (machine bytesGood) (wmod bytesGood.size) rfl rfl (by decide) (by decide) (by decide)⟩

theorem enum_out_of_range (fuel : Nat) :
    Solidity.AbiEntry.load enumBad.data 4=3 ∧ run (compiled (.enumBelow 3)).code (machine enumBad)=.revert ∧
    Solidity.AbiEntry.entry enumBad (fuel+2) (singleWordParams (.enumBelow 3))=.error .revert := by
  have rejected : run (compiled (.enumBelow 3)).code (machine enumBad)=.revert :=
    reject (.enumBelow 3) enumBad (by decide) (by decide)
  exact ⟨by decide,rejected,(WordCarrierBinding.entry_rejection C 7 (.enumBelow 3) label
    (compiled (.enumBelow 3)) (WordCarrierBinding.selected C 7 (.enumBelow 3) label)
    enumBad fuel (machine enumBad) (wmod enumBad.size) rfl rfl (by decide)).mp rejected⟩

theorem dirty_bytes_padding (fuel : Nat) :
    Solidity.AbiEntry.load bytesBad.data 4=0xab*2^248+1 ∧
    run (compiled (.fixedBytes 1)).code (machine bytesBad)=.revert ∧
    Solidity.AbiEntry.entry bytesBad (fuel+2) (singleWordParams (.fixedBytes 1))=.error .revert := by
  have rejected : run (compiled (.fixedBytes 1)).code (machine bytesBad)=.revert :=
    reject (.fixedBytes 1) bytesBad (by decide) (by decide)
  exact ⟨by decide,rejected,(WordCarrierBinding.entry_rejection C 7 (.fixedBytes 1) label
    (compiled (.fixedBytes 1)) (WordCarrierBinding.selected C 7 (.fixedBytes 1) label)
    bytesBad fuel (machine bytesBad) (wmod bytesBad.size) rfl rfl (by decide)).mp rejected⟩

theorem zero_boundaries :
    run (compiled (.fixedBytes 0)).code (machine zero)=.ok (bound zero) 0 ∧
    run (compiled (.fixedBytes 0)).code (machine bytesGood)=.revert ∧
    run (compiled (.enumBelow 0)).code (machine zero)=.revert :=
  ⟨accept (.fixedBytes 0) zero (by decide) (by decide),
    reject (.fixedBytes 0) bytesGood (by decide) (by decide),
    reject (.enumBelow 0) zero (by decide) (by decide)⟩

/-- Full-width and wider metadata keep the decoder's accepted cases. -/
theorem wide_bytes_accepted :
    run (compiled (.fixedBytes 32)).code (machine bytesBad)=.ok (bound bytesBad) 0 ∧
    run (compiled (.fixedBytes 33)).code (machine bytesBad)=.ok (bound bytesBad) 0 :=
  ⟨accept (.fixedBytes 32) bytesBad (by decide) (by decide),
    accept (.fixedBytes 33) bytesBad (by decide) (by decide)⟩

/-- Semantic enum cardinalities are never truncated into a machine immediate. -/
theorem large_enum_accepts (members : Nat) (large : W≤members) (word size : Fin W)
    (full : ¬size.val<36) (initial : Machine)
    (wordCell : initial.mem 7=.val word) (sizeCell : initial.mem 8=.val size) :
    run (compiled (.enumBelow members)).code initial=.ok (uintBoundMachine 7 label word initial) 0 := by
  have valid : (Solidity.AbiEntry.Kind.enumBelow members).valid word.val=true :=
    decide_eq_true (Nat.lt_of_lt_of_le word.isLt large)
  simpa only [wordCarrierOutcome,if_neg full,if_pos valid] using
    WordCarrierBinding.executed C 7 (.enumBelow members) label (compiled (.enumBelow members))
      (WordCarrierBinding.selected C 7 (.enumBelow members) label) initial word size wordCell sizeCell

theorem short_before_malformed_word (kind : Solidity.AbiEntry.Kind) (initial : Machine)
    (sizeCell : initial.mem 8=.val (wmod 35)) : run (compiled kind).code initial=.revert :=
  WordCarrierBinding.short_before_word C 7 kind label initial (wmod 35) sizeCell (by decide)

theorem insufficient_fuel :
    run (compiled (.fixedBytes 1)).code (machine bytesGood)=.ok (bound bytesGood) 0 ∧
    Solidity.AbiEntry.entry bytesGood 0 (singleWordParams (.fixedBytes 1))=.error .fuel ∧
    Solidity.AbiEntry.entry bytesGood 1 (singleWordParams (.fixedBytes 1))=.error .fuel :=
  ⟨accept (.fixedBytes 1) bytesGood (by decide) (by decide),
    SingleWordGate.insufficient_fuel bytesGood (.fixedBytes 1) (by decide)⟩

private def readBody : Prog C UIntBoundCtx UIntBoundCtx :=
  .cons (.assignLocal (.there .here) (.simple (.local .here))) .nil
private def bodyCompiled : Compiler.Compilation 7 (Frag.init UIntBoundCtx) readBody :=
  .core (Frag.init UIntBoundCtx) (by rfl)
theorem bound_argument_read :
    Compiler.compile 7 (Frag.init UIntBoundCtx) readBody=some bodyCompiled ∧
    run bodyCompiled.code (bound bytesGood)=
      .ok {bound bytesGood with mem := upd (bound bytesGood).mem 8 (.val (rawArgumentWord bytesGood))} 0 :=
  ⟨ValueGateBody.body_selected 7 _ _ _ (by rfl),by rfl⟩

theorem protected_and_saved :
    (bound bytesGood).mem 7=.val (rawArgumentWord bytesGood) ∧ (bound bytesGood).mem 8=.val label ∧
    (bound bytesGood).mem 9=.val (rawArgumentWord bytesGood) ∧ (bound bytesGood).mem 10=.val (wmod 71) ∧
    (bound bytesGood).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (bound bytesGood).callvalue=wmod 17 ∧ (bound bytesGood).store=(machine bytesGood).store ∧
    (bound bytesGood).bal=(machine bytesGood).bal := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBindingControls.enum_raw_value_and_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms enum_raw_value_and_frame
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBindingControls.bytes_raw_value_and_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bytes_raw_value_and_frame
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBindingControls.enum_out_of_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms enum_out_of_range
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBindingControls.dirty_bytes_padding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_bytes_padding
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBindingControls.zero_boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_boundaries
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBindingControls.wide_bytes_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wide_bytes_accepted
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBindingControls.large_enum_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms large_enum_accepts
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBindingControls.short_before_malformed_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_before_malformed_word
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBindingControls.insufficient_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms insufficient_fuel
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBindingControls.bound_argument_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bound_argument_read
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBindingControls.protected_and_saved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.WordCarrierBindingControls
