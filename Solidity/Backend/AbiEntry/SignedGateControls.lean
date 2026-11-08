import Solidity.Backend.AbiEntry.SignedGate

/-! Actual selected signed guards preserve valid sign extension and reject
dirty high bits. Full/wide widths remain accepted without native/body claims. -/
namespace Solidity.Backend.AbiEntry.SignedGateControls
open Solidity.Evm
open Interface (signedGateOutcome)
private def C : Contract := {vars := []}
private def label : Fin W := wmod 99
private def compiled (bits : Nat) := SignedGate.compiled C 7 bits label
private def machine (word : Fin W) : Machine :=
  {Machine.init with
    callvalue := wmod 17
    mem := fun address => if address=7 then .val word else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def written (word : Fin W) : Machine := {machine word with mem := upd (machine word).mem 8 (.val label)}
private theorem actual (bits : Nat) (word : Fin W) :
    run (compiled bits).code (machine word)=signedGateOutcome 7 bits label word (machine word) :=
  SignedGate.executed C 7 bits label (compiled bits) (SignedGate.selected C 7 bits label) (machine word) word rfl
private theorem accept (bits : Nat) (word : Fin W) (valid : (Solidity.AbiEntry.Kind.int bits).valid word.val=true) :
    run (compiled bits).code (machine word)=.ok (written word) 0 := by
  simpa only [written,signedGateOutcome,valid,ite_true] using actual bits word
private theorem reject (bits : Nat) (word : Fin W) (invalid : (Solidity.AbiEntry.Kind.int bits).valid word.val=false) :
    run (compiled bits).code (machine word)=.revert := by
  simpa only [signedGateOutcome,invalid,Bool.false_eq_true,ite_false] using actual bits word

theorem signed8_edges :
    run (compiled 8).code (machine (wmod 127))=.ok (written (wmod 127)) 0 ∧
    run (compiled 8).code (machine (wmod 128))=.revert ∧
    run (compiled 8).code (machine (wmod (W-128)))=.ok (written (wmod (W-128))) 0 ∧
    run (compiled 8).code (machine (wmod (W-129)))=.revert :=
  ⟨accept _ _ (by decide),reject _ _ (by decide),accept _ _ (by decide),reject _ _ (by decide)⟩

theorem zero_and_one_width :
    run (compiled 0).code (machine (wmod 0))=.ok (written (wmod 0)) 0 ∧
    run (compiled 0).code (machine wMax)=.ok (written wMax) 0 ∧
    run (compiled 1).code (machine (wmod 1))=.revert :=
  ⟨accept _ _ (by decide),accept _ _ (by decide),reject _ _ (by decide)⟩

theorem signed256_all_words (word : Fin W) : run (compiled 256).code (machine word)=.ok (written word) 0 := by
  apply accept
  by_cases positive : word.val<2^(256-1)
  · simp only [Solidity.AbiEntry.Kind.valid,decide_eq_true positive,Bool.true_or]
  · have split : Solidity.AbiEntry.W-2^(256-1)=2^(256-1) := by decide
    have negative : Solidity.AbiEntry.W-2^(256-1)≤word.val := by
      rw [split]
      exact Nat.le_of_not_gt positive
    simp only [Solidity.AbiEntry.Kind.valid,decide_eq_false positive,decide_eq_true negative,Bool.false_or]

theorem signed257_all_words (word : Fin W) : run (compiled 257).code (machine word)=.ok (written word) 0 := by
  apply accept
  have positive : word.val<2^(257-1) := by change word.val<W;exact word.isLt
  simp only [Solidity.AbiEntry.Kind.valid,decide_eq_true positive,Bool.true_or]

theorem wide_bound_not_truncated : SignedGate.low 257%W=0 ∧
    run (compiled 257).code (machine wMax)=.ok (written wMax) 0 := ⟨by decide,signed257_all_words _⟩

private def dirty : Solidity.AbiEntry.Input := {data := [0xaa]++Solidity.AbiEntry.wordBytes 128,free := 0}
private def negative : Solidity.AbiEntry.Input := {data := [0xaa]++Solidity.AbiEntry.wordBytes (W-128),free := 0}

theorem raw_dirty_failure (fuel len : Nat) :
    Solidity.AbiEntry.cval dirty (fuel+1) (.word (.int 8)) 1 len=.error .revert := by
  apply (SignedGate.correspondence C 7 8 label (compiled 8) (SignedGate.selected C 7 8 label)
    (machine (wmod 128)) (wmod 128) rfl dirty 1 fuel len (by decide)).mp
  exact signed8_edges.2.1

theorem raw_negative_value (fuel len : Nat) :
    Solidity.AbiEntry.load negative.data 1=W-128 ∧
    ∃ value,Solidity.AbiEntry.cval negative (fuel+1) (.word (.int 8)) 1 len=.ok value := by
  constructor
  · decide
  · have valid : (Solidity.AbiEntry.Kind.int 8).valid (Solidity.AbiEntry.load negative.data 1)=true := by decide
    simp only [Solidity.AbiEntry.cval,dite_eq_left valid]
    exact ⟨_,rfl⟩

theorem malformed_word_fault :
    run (compiled 8).code {machine (wmod 0) with mem := fun _ => .slot (.root 0)}=.fault := by rfl

theorem protected_and_saved (word : Fin W) :
    (written word).mem 7=.val word ∧ (written word).mem 9=.val (wmod 71) ∧
    (written word).stack=[.val (wmod 258),.val (wmod 513)] ∧ (written word).callvalue=wmod 17 := ⟨rfl,rfl,rfl,rfl⟩
/-- info: 'Solidity.Backend.AbiEntry.SignedGateControls.signed8_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms signed8_edges
/-- info: 'Solidity.Backend.AbiEntry.SignedGateControls.zero_and_one_width' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_and_one_width
/-- info: 'Solidity.Backend.AbiEntry.SignedGateControls.signed256_all_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms signed256_all_words
/-- info: 'Solidity.Backend.AbiEntry.SignedGateControls.signed257_all_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms signed257_all_words
/-- info: 'Solidity.Backend.AbiEntry.SignedGateControls.wide_bound_not_truncated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wide_bound_not_truncated
/-- info: 'Solidity.Backend.AbiEntry.SignedGateControls.raw_dirty_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_dirty_failure
/-- info: 'Solidity.Backend.AbiEntry.SignedGateControls.raw_negative_value' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_negative_value
/-- info: 'Solidity.Backend.AbiEntry.SignedGateControls.malformed_word_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms malformed_word_fault
/-- info: 'Solidity.Backend.AbiEntry.SignedGateControls.protected_and_saved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.SignedGateControls
