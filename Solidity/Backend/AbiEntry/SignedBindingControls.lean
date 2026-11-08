import Solidity.Backend.AbiEntry.SignedBinding

/-! Actual signed declaration and raw negative decoding, with a compiled signed
comparison consuming the new local. Source/native realization remains open. -/
namespace Solidity.Backend.AbiEntry.SignedBindingControls
open Solidity.Evm
open Interface (RouteCtx SignedBoundCtx rawArgumentWord singleWordParams signedBoundMachine signedBindingOutcome)
private def C : Contract := {vars := []}
private def label : Fin W := wmod 99
private def compiled (bits : Nat) := SignedBinding.compiled C 7 bits label
private def machine (word size : Fin W) : Machine :=
  {Machine.init with
    callvalue := wmod 17
    mem := fun address => if address=7 then .val word else if address=8 then .val size else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def bound (word size : Fin W) : Machine := signedBoundMachine 7 label word (machine word size)
private theorem actual (bits : Nat) (word size : Fin W) :
    run (compiled bits).code (machine word size)=signedBindingOutcome 7 bits label word size (machine word size) :=
  SignedBinding.executed C 7 bits label (compiled bits) (SignedBinding.selected C 7 bits label)
    (machine word size) word size rfl rfl
private theorem accept (bits : Nat) (word : Fin W) (valid : (Solidity.AbiEntry.Kind.int bits).valid word.val=true) :
    run (compiled bits).code (machine word (wmod 36))=.ok (bound word (wmod 36)) 0 := by
  have full : ¬(wmod 36).val<36 := by decide
  simpa only [bound,signedBindingOutcome,ite_eq_right full,ite_eq_left valid] using actual bits word (wmod 36)
private theorem reject (bits : Nat) (word : Fin W) (invalid : ¬(Solidity.AbiEntry.Kind.int bits).valid word.val=true) :
    run (compiled bits).code (machine word (wmod 36))=.revert := by
  have full : ¬(wmod 36).val<36 := by decide
  simpa only [bound,signedBindingOutcome,ite_eq_right full,ite_eq_right invalid] using actual bits word (wmod 36)

theorem signed8_edges :
    run (compiled 8).code (machine (wmod 127) (wmod 36))=.ok (bound (wmod 127) (wmod 36)) 0 ∧
    run (compiled 8).code (machine (wmod 128) (wmod 36))=.revert ∧
    run (compiled 8).code (machine (wmod (W-128)) (wmod 36))=.ok (bound (wmod (W-128)) (wmod 36)) 0 ∧
    run (compiled 8).code (machine (wmod (W-129)) (wmod 36))=.revert :=
  ⟨accept _ _ (by decide),reject _ _ (by decide),accept _ _ (by decide),reject _ _ (by decide)⟩

theorem zero_full_width_controls :
    run (compiled 0).code (machine (wmod 0) (wmod 36))=.ok (bound (wmod 0) (wmod 36)) 0 ∧
    run (compiled 0).code (machine wMax (wmod 36))=.ok (bound wMax (wmod 36)) 0 ∧
    run (compiled 1).code (machine (wmod 1) (wmod 36))=.revert ∧
    run (compiled 256).code (machine wH (wmod 36))=.ok (bound wH (wmod 36)) 0 :=
  ⟨accept _ _ (by decide),accept _ _ (by decide),reject _ _ (by decide),accept _ _ (by decide)⟩

theorem wide_accepts (bits : Nat) (wide : 257≤bits) (word : Fin W) :
    run (compiled bits).code (machine word (wmod 36))=.ok (bound word (wmod 36)) 0 := by
  have exponent : 256≤bits-1 := Nat.sub_le_sub_right wide 1
  have fits : word.val<2^(bits-1) := Nat.lt_of_lt_of_le word.isLt (Nat.pow_le_pow_right (by decide : 0<2) exponent)
  apply accept
  simp only [Solidity.AbiEntry.Kind.valid,decide_eq_true fits,Bool.true_or]

private def negative : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 255++[128,0x77,0x88],free := 71}
private def positive : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[127,0x77],free := 71}
private def dirty : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[128],free := 71}
private def rawMachine (input : Solidity.AbiEntry.Input) : Machine := machine (rawArgumentWord input) (wmod input.size)
private def rawBound (input : Solidity.AbiEntry.Input) : Machine := bound (rawArgumentWord input) (wmod input.size)

theorem negative_reading : Solidity.AbiEntry.load negative.data 4=W-128 ∧
    Solidity.AbiEntry.toInt (Solidity.AbiEntry.load negative.data 4)= -128 ∧
    sgn (rawArgumentWord negative).val= -128 := ⟨by decide,by decide,by decide⟩

theorem raw_decoded_and_bound (fuel : Nat) :
    ∃ value : Solidity.AbiEntry.Word (.int 8),
      Solidity.AbiEntry.entry negative (fuel+2) (singleWordParams (.int 8))=.ok (.cons (.val (.word value)) .nil) ∧
      run (compiled 8).code (rawMachine negative)=.ok (rawBound negative) 0 ∧
      (rawBound negative).mem (cellOf 7 (.here : Idx SignedBoundCtx (.val .int)))=.val ⟨value.val,value.lt⟩ ∧
      sgn value.val=Solidity.AbiEntry.toInt (Solidity.AbiEntry.load negative.data 4) :=
  SignedBinding.decoded_and_bound C 7 8 label (compiled 8) (SignedBinding.selected C 7 8 label)
    negative fuel (rawMachine negative) (wmod negative.size) rfl rfl (by decide) (by decide) (by decide)

theorem raw_dirty_rejection (fuel : Nat) :
    run (compiled 8).code (rawMachine dirty)=.revert ∧
    Solidity.AbiEntry.entry dirty (fuel+2) (singleWordParams (.int 8))=.error .revert := by
  have rejected : run (compiled 8).code (rawMachine dirty)=.revert := by
    have full : ¬(wmod dirty.size).val<36 := by decide
    have invalid : ¬(Solidity.AbiEntry.Kind.int 8).valid (rawArgumentWord dirty).val=true := by decide
    simpa only [rawMachine,rawBound,bound,signedBindingOutcome,ite_eq_right full,ite_eq_right invalid] using actual 8 (rawArgumentWord dirty) (wmod dirty.size)
  exact ⟨rejected,(SignedBinding.entry_rejection C 7 8 label (compiled 8) (SignedBinding.selected C 7 8 label)
    dirty fuel (rawMachine dirty) (wmod dirty.size) rfl rfl (by decide)).mp rejected⟩

theorem short_before_malformed_word :
    run (compiled 8).code {rawMachine negative with
      mem := fun address => if address=8 then .val (wmod 35) else .slot (.root 0)}=.revert :=
  SignedBinding.short_before_word C 7 8 label _ (wmod 35) rfl (by decide)

private def branchBody : Prog C SignedBoundCtx SignedBoundCtx :=
  .cons (.ite (.binop .lt rfl rfl (.simple (.local .here)) (.simple (.lit 0 (by decide))))
    (.cons (.assignLocal (.there .here) (.simple (.lit 11 (by decide)))) .nil)
    (.cons (.assignLocal (.there .here) (.simple (.lit 22 (by decide)))) .nil)) .nil
private theorem bodyCore : inFragP (Frag.init SignedBoundCtx) branchBody=some (Frag.init SignedBoundCtx) := by rfl
private def back : Compiler.Compilation 7 (Frag.init SignedBoundCtx) branchBody := .core (Frag.init SignedBoundCtx) bodyCore

theorem typed_signed_branch :
    Compiler.compile 7 (Frag.init SignedBoundCtx) branchBody=some back ∧
    run back.code (rawBound negative)=.ok {rawBound negative with mem := upd (rawBound negative).mem 8 (.val (wmod 11))} 0 ∧
    run back.code (rawBound positive)=.ok {rawBound positive with mem := upd (rawBound positive).mem 8 (.val (wmod 22))} 0 :=
  ⟨ValueGateBody.body_selected 7 _ _ _ bodyCore,by rfl,by rfl⟩

theorem fuel_boundary :
    run (compiled 8).code (rawMachine negative)=.ok (rawBound negative) 0 ∧
    Solidity.AbiEntry.entry negative 0 (singleWordParams (.int 8))=.error .fuel ∧
    Solidity.AbiEntry.entry negative 1 (singleWordParams (.int 8))=.error .fuel := by
  have actualRun : run (compiled 8).code (rawMachine negative)=.ok (rawBound negative) 0 := by
    have full : ¬(wmod negative.size).val<36 := by decide
    have valid : (Solidity.AbiEntry.Kind.int 8).valid (rawArgumentWord negative).val=true := by decide
    simpa only [rawMachine,rawBound,bound,signedBindingOutcome,ite_eq_right full,ite_eq_left valid] using actual 8 (rawArgumentWord negative) (wmod negative.size)
  exact ⟨actualRun,SingleWordGate.insufficient_fuel negative (.int 8) (by decide)⟩

theorem protected_and_saved :
    (rawBound negative).mem 7=.val (rawArgumentWord negative) ∧ (rawBound negative).mem 8=.val label ∧
    (rawBound negative).mem 10=.val (wmod 71) ∧
    (rawBound negative).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (rawBound negative).callvalue=wmod 17 ∧ (rawBound negative).store=(rawMachine negative).store ∧
    (rawBound negative).bal=(rawMachine negative).bal := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.AbiEntry.SignedBindingControls.signed8_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms signed8_edges
/-- info: 'Solidity.Backend.AbiEntry.SignedBindingControls.zero_full_width_controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_full_width_controls
/-- info: 'Solidity.Backend.AbiEntry.SignedBindingControls.wide_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wide_accepts
/-- info: 'Solidity.Backend.AbiEntry.SignedBindingControls.negative_reading' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms negative_reading
/-- info: 'Solidity.Backend.AbiEntry.SignedBindingControls.raw_decoded_and_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_decoded_and_bound
/-- info: 'Solidity.Backend.AbiEntry.SignedBindingControls.raw_dirty_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_dirty_rejection
/-- info: 'Solidity.Backend.AbiEntry.SignedBindingControls.short_before_malformed_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_before_malformed_word
/-- info: 'Solidity.Backend.AbiEntry.SignedBindingControls.typed_signed_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typed_signed_branch
/-- info: 'Solidity.Backend.AbiEntry.SignedBindingControls.fuel_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fuel_boundary
/-- info: 'Solidity.Backend.AbiEntry.SignedBindingControls.protected_and_saved' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.SignedBindingControls
