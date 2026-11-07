import Solidity.Backend.AbiEntry.WordGate

/-! All primitive families are exercised through one actual public compiler
entry point. Raw padding failure/success remain distinct from whole ABI entry. -/
namespace Solidity.Backend.AbiEntry.WordGateControls
open Solidity.Evm
open Interface (wordGateOutcome)
private def C : Contract := {vars := []}
private def label : Fin W := wmod 99
private def compiled (kind : Solidity.AbiEntry.Kind) := WordGate.compiled C 7 kind label
private def machine (word : Fin W) : Machine :=
  {Machine.init with
    callvalue := wmod 17
    mem := fun address => if address=7 then .val word else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def written (word : Fin W) : Machine := {machine word with mem := upd (machine word).mem 8 (.val label)}
private theorem actual (kind : Solidity.AbiEntry.Kind) (word : Fin W) :
    run (compiled kind).code (machine word)=wordGateOutcome 7 kind label word (machine word) :=
  WordGate.executed C 7 kind label (compiled kind) (WordGate.selected C 7 kind label) (machine word) word rfl
private theorem accept (kind : Solidity.AbiEntry.Kind) (word : Fin W) (valid : kind.valid word.val=true) :
    run (compiled kind).code (machine word)=.ok (written word) 0 := by
  simpa only [wordGateOutcome,valid,if_true] using actual kind word
private theorem reject (kind : Solidity.AbiEntry.Kind) (word : Fin W) (invalid : kind.valid word.val=false) :
    run (compiled kind).code (machine word)=.revert := by
  simpa only [wordGateOutcome,invalid,Bool.false_eq_true,if_false] using actual kind word

private def leftByte : Fin W := wmod (0xab*2^248)
private def dirtyByte : Fin W := wmod (0xab*2^248+1)

theorem bytes0_boundaries :
    run (compiled (.fixedBytes 0)).code (machine (wmod 0))=.ok (written (wmod 0)) 0 ∧
    run (compiled (.fixedBytes 0)).code (machine (wmod 1))=.revert :=
  ⟨accept _ _ (by decide),reject _ _ (by decide)⟩
theorem bytes1_boundaries :
    run (compiled (.fixedBytes 1)).code (machine leftByte)=.ok (written leftByte) 0 ∧
    run (compiled (.fixedBytes 1)).code (machine dirtyByte)=.revert :=
  ⟨accept _ _ (by decide),reject _ _ (by decide)⟩
theorem bytes31_boundaries :
    run (compiled (.fixedBytes 31)).code (machine (wmod 256))=.ok (written (wmod 256)) 0 ∧
    run (compiled (.fixedBytes 31)).code (machine (wmod 257))=.revert :=
  ⟨accept _ _ (by decide),reject _ _ (by decide)⟩

theorem full_and_oversized (size : Nat) (wide : 32≤size) (word : Fin W) :
    run (compiled (.fixedBytes size)).code (machine word)=.ok (written word) 0 := by
  apply accept
  have bound : 256≤8*size := Nat.mul_le_mul_left 8 wide
  have exponent : 256-8*size=0 := Nat.sub_eq_zero_of_le bound
  simp only [Solidity.AbiEntry.Kind.valid,exponent,Nat.pow_zero,Nat.mod_one]
  rfl

theorem every_kind_accepts :
    run (compiled (.uint 8)).code (machine (wmod 255))=.ok (written (wmod 255)) 0 ∧
    run (compiled (.int 8)).code (machine wMax)=.ok (written wMax) 0 ∧
    run (compiled .bool).code (machine (wmod 1))=.ok (written (wmod 1)) 0 ∧
    run (compiled (.fixedBytes 1)).code (machine leftByte)=.ok (written leftByte) 0 ∧
    run (compiled (.enumBelow 3)).code (machine (wmod 2))=.ok (written (wmod 2)) 0 :=
  ⟨accept _ _ (by decide),accept _ _ (by decide),accept _ _ (by decide),bytes1_boundaries.1,accept _ _ (by decide)⟩

theorem every_kind_rejects :
    run (compiled (.uint 8)).code (machine (wmod 256))=.revert ∧
    run (compiled (.int 8)).code (machine (wmod 128))=.revert ∧
    run (compiled .bool).code (machine (wmod 2))=.revert ∧
    run (compiled (.fixedBytes 1)).code (machine dirtyByte)=.revert ∧
    run (compiled (.enumBelow 3)).code (machine (wmod 3))=.revert :=
  ⟨reject _ _ (by decide),reject _ _ (by decide),reject _ _ (by decide),bytes1_boundaries.2,reject _ _ (by decide)⟩

private def rawDirty : Solidity.AbiEntry.Input := {data := [0xaa]++Solidity.AbiEntry.wordBytes dirtyByte.val,free := 0}
private def rawGood : Solidity.AbiEntry.Input := {data := [0xaa]++Solidity.AbiEntry.wordBytes leftByte.val,free := 0}

theorem raw_padding_failure (fuel len : Nat) :
    Solidity.AbiEntry.cval rawDirty (fuel+1) (.word (.fixedBytes 1)) 1 len=.error .revert := by
  apply (WordGate.correspondence C 7 (.fixedBytes 1) label (compiled (.fixedBytes 1))
    (WordGate.selected C 7 (.fixedBytes 1) label) (machine dirtyByte) dirtyByte rfl rawDirty 1 fuel len (by decide)).mp
  exact bytes1_boundaries.2

theorem raw_aligned_value (fuel len : Nat) :
    Solidity.AbiEntry.load rawGood.data 1=leftByte.val ∧
    ∃ value,Solidity.AbiEntry.cval rawGood (fuel+1) (.word (.fixedBytes 1)) 1 len=.ok value := by
  constructor
  · decide
  · have valid : (Solidity.AbiEntry.Kind.fixedBytes 1).valid (Solidity.AbiEntry.load rawGood.data 1)=true := by decide
    simp only [Solidity.AbiEntry.cval,dif_pos valid]
    exact ⟨_,rfl⟩

theorem malformed_word_fault :
    run (compiled (.fixedBytes 1)).code {machine (wmod 0) with mem := fun _ => .slot (.root 0)}=.fault := by rfl

theorem protected_and_saved (word : Fin W) :
    (written word).mem 7=.val word ∧ (written word).mem 9=.val (wmod 71) ∧
    (written word).stack=[.val (wmod 258),.val (wmod 513)] ∧ (written word).callvalue=wmod 17 := ⟨rfl,rfl,rfl,rfl⟩
/-- info: 'Solidity.Backend.AbiEntry.WordGateControls.bytes0_boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bytes0_boundaries
/-- info: 'Solidity.Backend.AbiEntry.WordGateControls.bytes1_boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bytes1_boundaries
/-- info: 'Solidity.Backend.AbiEntry.WordGateControls.bytes31_boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bytes31_boundaries
/-- info: 'Solidity.Backend.AbiEntry.WordGateControls.full_and_oversized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms full_and_oversized
/-- info: 'Solidity.Backend.AbiEntry.WordGateControls.every_kind_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms every_kind_accepts
/-- info: 'Solidity.Backend.AbiEntry.WordGateControls.every_kind_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms every_kind_rejects
/-- info: 'Solidity.Backend.AbiEntry.WordGateControls.raw_padding_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_padding_failure
/-- info: 'Solidity.Backend.AbiEntry.WordGateControls.raw_aligned_value' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_aligned_value
/-- info: 'Solidity.Backend.AbiEntry.WordGateControls.malformed_word_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms malformed_word_fault
/-- info: 'Solidity.Backend.AbiEntry.WordGateControls.protected_and_saved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.WordGateControls
