import Solidity.Backend.AbiEntry.UnsignedGate
import Solidity.Backend.AbiEntry.HeadCheck

/-! Actual selected unsigned guards, dirty-bit and raw-word boundaries.
These controls do not bypass the enclosing ABI head/span checks. -/
namespace Solidity.Backend.AbiEntry.UnsignedGateControls
open Solidity.Evm
open Interface (unsignedGateOutcome)
private def C : Contract := {vars := []}
private def label : Fin W := wmod 99
private def compiled (bound : Nat) := UnsignedGate.compiled C 7 bound label
private def machine (word : Fin W) : Machine :=
  {Machine.init with
    callvalue := wmod 17
    mem := fun address => if address=7 then .val word else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def written (word : Fin W) : Machine :=
  {machine word with mem := upd (machine word).mem 8 (.val label)}
private theorem actual (bound : Nat) (word : Fin W) :
    run (compiled bound).code (machine word)=unsignedGateOutcome 7 bound label word (machine word) :=
  UnsignedGate.executed C 7 bound label (compiled bound) (UnsignedGate.selected C 7 bound label) (machine word) word rfl
private theorem accepted (bound : Nat) (word : Fin W) (valid : word.val<bound) :
    run (compiled bound).code (machine word)=.ok (written word) 0 := by
  simpa only [unsignedGateOutcome,ite_eq_left valid,written] using actual bound word
private theorem rejected (bound : Nat) (word : Fin W) (invalid : ¬word.val<bound) :
    run (compiled bound).code (machine word)=.revert := by
  simpa only [unsignedGateOutcome,ite_eq_right invalid] using actual bound word

theorem bool_boundaries :
    run (compiled 2).code (machine (wmod 0))=.ok (written (wmod 0)) 0 ∧
    run (compiled 2).code (machine (wmod 1))=.ok (written (wmod 1)) 0 ∧
    run (compiled 2).code (machine (wmod 2))=.revert :=
  ⟨accepted 2 _ (by decide),accepted 2 _ (by decide),rejected 2 _ (by decide)⟩
theorem uint8_boundaries :
    run (compiled (2^8)).code (machine (wmod 255))=.ok (written (wmod 255)) 0 ∧
    run (compiled (2^8)).code (machine (wmod 256))=.revert :=
  ⟨accepted _ _ (by decide),rejected _ _ (by decide)⟩
theorem address_boundaries :
    run (compiled (2^160)).code (machine (wmod (2^160-1)))=.ok (written (wmod (2^160-1))) 0 ∧
    run (compiled (2^160)).code (machine (wmod (2^160)))=.revert :=
  ⟨accepted _ _ (by decide),rejected _ _ (by decide)⟩
theorem enum_boundaries :
    run (compiled 3).code (machine (wmod 2))=.ok (written (wmod 2)) 0 ∧
    run (compiled 3).code (machine (wmod 3))=.revert ∧
    run (compiled 0).code (machine (wmod 0))=.revert :=
  ⟨accepted _ _ (by decide),rejected _ _ (by decide),rejected _ _ (by decide)⟩

theorem uint256_all_words (word : Fin W) :
    run (compiled (2^256)).code (machine word)=.ok (written word) 0 :=
  accepted _ word (by change word.val<W;exact word.isLt)
theorem wide_bound_all_words (word : Fin W) :
    run (compiled (W+1)).code (machine word)=.ok (written word) 0 :=
  accepted _ word (Nat.lt_trans word.isLt (Nat.lt_succ_self W))
theorem wide_no_wrap : (W+1)%W=1 ∧
    run (compiled (W+1)).code (machine wMax)=.ok (written wMax) 0 :=
  ⟨by decide,wide_bound_all_words _⟩

private def raw : Solidity.AbiEntry.Input := {data := [0xaa]++List.replicate 31 0++[3],free := 0}
theorem raw_enum_failure (fuel len : Nat) :
    Solidity.AbiEntry.cval raw (fuel+1) (.word (.enumBelow 3)) 1 len=.error .revert :=
  UnsignedGate.enum_rejection C 7 3 label (compiled 3) (UnsignedGate.selected C 7 3 label)
    (machine (wmod 3)) (wmod 3) rfl raw 1 fuel len (by decide) enum_boundaries.2.1

theorem raw_uint8_kept : Solidity.AbiEntry.load raw.data 1=3 ∧
    run (compiled (2^8)).code (machine (wmod 3))=.ok (written (wmod 3)) 0 :=
  ⟨by decide,accepted _ _ (by decide)⟩

theorem raw_bool_failure (fuel len : Nat) :
    Solidity.AbiEntry.cval raw (fuel+1) (.word .bool) 1 len=.error .revert :=
  UnsignedGate.bool_rejection C 7 label (compiled 2) (UnsignedGate.selected C 7 2 label)
    (machine (wmod 3)) (wmod 3) rfl raw 1 fuel len (by decide) (rejected _ _ (by decide))

private def dirtyUint : Solidity.AbiEntry.Input := {data := [0xaa]++Solidity.AbiEntry.wordBytes 256,free := 0}
theorem raw_uint8_failure (fuel len : Nat) :
    Solidity.AbiEntry.cval dirtyUint (fuel+1) (.word (.uint 8)) 1 len=.error .revert :=
  UnsignedGate.uint_rejection C 7 8 label (compiled (2^8)) (UnsignedGate.selected C 7 (2^8) label)
    (machine (wmod 256)) (wmod 256) rfl dirtyUint 1 fuel len (by decide) uint8_boundaries.2

theorem raw_uint8_value (fuel len : Nat) :
    ∃ value,Solidity.AbiEntry.cval raw (fuel+1) (.word (.uint 8)) 1 len=.ok value := by
  have valid : (Solidity.AbiEntry.Kind.uint 8).valid (Solidity.AbiEntry.load raw.data 1)=true := by decide
  simp only [Solidity.AbiEntry.cval,dite_eq_left valid]
  exact ⟨_,rfl⟩

theorem empty_word_not_entry :
    Solidity.AbiEntry.load [] 0=0 ∧
    run (compiled 2).code (machine (wmod 0))=.ok (written (wmod 0)) 0 ∧
    Solidity.AbiEntry.entry {data := [],free := 0} 0 [{shape := .word .bool,loc := .value}]=.error .revert :=
  ⟨rfl,bool_boundaries.1,HeadCheck.early_revert _ 0 _ (by decide)⟩

theorem malformed_word_fault :
    run (compiled 2).code {machine (wmod 0) with mem := fun _ => .slot (.root 0)}=.fault := by rfl

theorem protected_and_saved (word : Fin W) :
    (written word).mem 7=.val word ∧ (written word).mem 9=.val (wmod 71) ∧
    (written word).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (written word).callvalue=wmod 17 := ⟨rfl,rfl,rfl,rfl⟩
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGateControls.bool_boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bool_boundaries
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGateControls.uint8_boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uint8_boundaries
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGateControls.address_boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms address_boundaries
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGateControls.enum_boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms enum_boundaries
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGateControls.uint256_all_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uint256_all_words
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGateControls.wide_bound_all_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wide_bound_all_words
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGateControls.wide_no_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wide_no_wrap
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGateControls.raw_enum_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_enum_failure
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGateControls.raw_uint8_kept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_uint8_kept
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGateControls.raw_bool_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_bool_failure
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGateControls.raw_uint8_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_uint8_failure
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGateControls.raw_uint8_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_uint8_value
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGateControls.empty_word_not_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_word_not_entry
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGateControls.malformed_word_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms malformed_word_fault
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGateControls.protected_and_saved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.UnsignedGateControls
