import Solidity.Backend.AbiEntry.SignedEntryBodyInterface

/-! The existing compiler composes value checking, signed validation, bit-
preserving typed declaration and actual body execution. No body run is assumed. -/
namespace Solidity.Backend.AbiEntry.SignedEntryBody
open Solidity.Evm
open Interface
variable {C : Contract} {Δ : Ctx}

namespace Binding
def program (bits : Nat) (label : Fin W) (body : Prog C SignedBoundCtx Δ) : Prog C RouteCtx Δ :=
  .cons (.block (SingleWordGate.program C (.int bits) label))
    (.cons (.declLocal .int (.user "argument") (some (SignedBinding.parameter C))) body)

theorem admitted (bits : Nat) (label : Fin W) (body : Prog C SignedBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init SignedBoundCtx) body=some outFrag) :
    inFragP (Frag.init RouteCtx) (program bits label body)=some outFrag := by
  simp only [program,inFragP,inFrag,SingleWordGate.admitted,Option.map_some]
  exact bodyCore

def selectedWhole (base bits : Nat) (label : Fin W) (body : Prog C SignedBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init SignedBoundCtx) body=some outFrag) :
    Compiler.Compilation base (Frag.init RouteCtx) (program bits label body) :=
  .core outFrag (admitted bits label body outFrag bodyCore)

def selectedBody (base : Nat) (body : Prog C SignedBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init SignedBoundCtx) body=some outFrag) :
    Compiler.Compilation base (Frag.init SignedBoundCtx) body :=
  ValueGateBody.selectedBody base _ body outFrag bodyCore

theorem whole_selected (base bits : Nat) (label : Fin W) (body : Prog C SignedBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init SignedBoundCtx) body=some outFrag) :
    Compiler.compile base (Frag.init RouteCtx) (program bits label body)=
      some (selectedWhole base bits label body outFrag bodyCore) :=
  ValueGateBody.body_selected base _ _ _ (admitted bits label body outFrag bodyCore)

theorem body_selected (base : Nat) (body : Prog C SignedBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init SignedBoundCtx) body=some outFrag) :
    Compiler.compile base (Frag.init SignedBoundCtx) body=some (selectedBody base body outFrag bodyCore) :=
  ValueGateBody.body_selected base _ _ _ bodyCore

theorem code (base bits : Nat) (label : Fin W) (body : Prog C SignedBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init SignedBoundCtx) body=some outFrag) :
    (selectedWhole base bits label body outFrag bodyCore).code=
      compileProg base (SignedBinding.program C bits label)++(selectedBody base body outFrag bodyCore).code := by
  change compileProg base (program bits label body)=compileProg base (SignedBinding.program C bits label)++compileProg base body
  rw [SignedBinding.code]
  simp only [program,compileProg,compileStmt,SignedBinding.parameter,compileVal,compileSimple,List.append_assoc]
  rfl

theorem composed (C : Contract) (base bits : Nat) (label : Fin W) (bodyCode : List Evm.Instr)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run (compileProg base (SignedBinding.program C bits label)++bodyCode) machine=
      if size.val<36 then .revert else
      if (Solidity.AbiEntry.Kind.int bits).valid word.val then
        run bodyCode (signedBoundMachine base label word machine) else .revert := by
  have bindingRun : run (compileProg base (SignedBinding.program C bits label)) machine=
      signedBindingOutcome base bits label word size machine :=
    SignedBinding.run_program C base bits label machine word size initialWord initialSize
  simp only [signedBindingOutcome] at bindingRun
  by_cases short : size.val<36
  · rw [ite_eq_left short] at bindingRun ⊢
    exact run_append_revert bindingRun
  · rw [ite_eq_right short] at bindingRun ⊢
    by_cases valid : (Solidity.AbiEntry.Kind.int bits).valid word.val=true
    · rw [ite_eq_left valid] at bindingRun ⊢
      exact run_append_ok bindingRun
    · rw [ite_eq_right valid] at bindingRun ⊢
      exact run_append_revert bindingRun

theorem executed (base bits : Nat) (label : Fin W) (body : Prog C SignedBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init SignedBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program bits label body))
    (back : Compiler.Compilation base (Frag.init SignedBoundCtx) body)
    (wholeFound : Compiler.compile base (Frag.init RouteCtx) (program bits label body)=some whole)
    (bodyFound : Compiler.compile base (Frag.init SignedBoundCtx) body=some back)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run whole.code machine=if size.val<36 then .revert else
      if (Solidity.AbiEntry.Kind.int bits).valid word.val then
        run back.code (signedBoundMachine base label word machine) else .revert := by
  have sameWhole : whole=selectedWhole base bits label body outFrag bodyCore :=
    Option.some.inj (wholeFound.symm.trans (whole_selected base bits label body outFrag bodyCore))
  have sameBody : back=selectedBody base body outFrag bodyCore :=
    Option.some.inj (bodyFound.symm.trans (body_selected base body outFrag bodyCore))
  rw [sameWhole,sameBody,code]
  exact composed C base bits label _ machine word size initialWord initialSize

set_option backward.isDefEq.respectTransparency false in
/-- Raw semantic success identifies the actual local subsequently read by the body. -/
theorem decoded_body (base bits : Nat) (label : Fin W) (body : Prog C SignedBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init SignedBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program bits label body))
    (back : Compiler.Compilation base (Frag.init SignedBoundCtx) body)
    (wholeFound : Compiler.compile base (Frag.init RouteCtx) (program bits label body)=some whole)
    (bodyFound : Compiler.compile base (Frag.init SignedBoundCtx) body=some back)
    (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Machine) (size : Fin W)
    (initialWord : machine.mem base=.val (rawArgumentWord input))
    (initialSize : machine.mem (base+1)=.val size) (represented : size.val=input.size)
    (full : ¬input.size<36)
    (valid : (Solidity.AbiEntry.Kind.int bits).valid (Solidity.AbiEntry.load input.data 4)=true) :
    ∃ value : Solidity.AbiEntry.Word (.int bits),
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams (.int bits))=
        .ok (.cons (.val (.word value)) .nil) ∧
      (signedBoundMachine base label (rawArgumentWord input) machine).mem
        (cellOf base (.here : Idx SignedBoundCtx (.val .int)))=.val ⟨value.val,value.lt⟩ ∧
      sgn value.val=Solidity.AbiEntry.toInt (Solidity.AbiEntry.load input.data 4) ∧
      run whole.code machine=run back.code (signedBoundMachine base label (rawArgumentWord input) machine) := by
  rcases SignedBinding.decoded_and_bound C base bits label (SignedBinding.compiled C base bits label)
    (SignedBinding.selected C base bits label) input fuel machine size initialWord initialSize represented full valid with
    ⟨value,semantic,_,cell,reading⟩
  refine ⟨value,semantic,cell,reading,?_⟩
  rw [executed base bits label body outFrag bodyCore whole back wholeFound bodyFound machine _ size initialWord initialSize]
  simp only [represented,ite_eq_right full,rawArgumentWord,ite_eq_left valid]

/-- A short head prevents both the word read and all body execution. -/
theorem short_before_body (base bits : Nat) (label : Fin W) (body : Prog C SignedBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init SignedBoundCtx) body=some outFrag)
    (machine : Machine) (size : Fin W) (initialSize : machine.mem (base+1)=.val size)
    (short : size.val<36) :
    run (selectedWhole base bits label body outFrag bodyCore).code machine=.revert := by
  rw [code,SignedBinding.code]
  rw [List.append_assoc]
  exact run_append_revert (SingleWordGate.short_before_word C base (.int bits) label machine size initialSize short)

/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBody.Binding.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBody.Binding.whole_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whole_selected
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBody.Binding.body_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_selected
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBody.Binding.code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms code
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBody.Binding.composed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composed
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBody.Binding.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBody.Binding.decoded_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_body
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBody.Binding.short_before_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_before_body
end Binding

def program (bits : Nat) (payable : Bool) (label : Fin W) (body : Prog C SignedBoundCtx Δ) : Prog C RouteCtx Δ :=
  ValueGateBody.guard payable (Binding.program bits label body)

theorem admitted (bits : Nat) (payable : Bool) (label : Fin W) (body : Prog C SignedBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init SignedBoundCtx) body=some outFrag) :
    inFragP (Frag.init RouteCtx) (program bits payable label body)=some outFrag :=
  ValueGateBody.admitted _ _ payable outFrag (Binding.admitted bits label body outFrag bodyCore)

def compiled (base bits : Nat) (payable : Bool) (label : Fin W) (body : Prog C SignedBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init SignedBoundCtx) body=some outFrag) :
    Compiler.Compilation base (Frag.init RouteCtx) (program bits payable label body) :=
  ValueGateBody.selectedWhole base _ (Binding.program bits label body) payable outFrag
    (Binding.admitted bits label body outFrag bodyCore)

theorem selected (base bits : Nat) (payable : Bool) (label : Fin W) (body : Prog C SignedBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init SignedBoundCtx) body=some outFrag) :
    Compiler.compile base (Frag.init RouteCtx) (program bits payable label body)=
      some (compiled base bits payable label body outFrag bodyCore) :=
  ValueGateBody.whole_selected base _ (Binding.program bits label body) payable outFrag
    (Binding.admitted bits label body outFrag bodyCore)

theorem gated (base bits : Nat) (payable : Bool) (label : Fin W) (body : Prog C SignedBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init SignedBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program bits payable label body))
    (found : Compiler.compile base (Frag.init RouteCtx) (program bits payable label body)=some whole)
    (machine : Machine) :
    run whole.code machine=if payable || decide (machine.callvalue.val=0) then
      run (Binding.selectedWhole base bits label body outFrag bodyCore).code machine else .revert :=
  ValueGateBody.executed base _ (Binding.program bits label body) payable outFrag
    (Binding.admitted bits label body outFrag bodyCore) whole
    (Binding.selectedWhole base bits label body outFrag bodyCore) found
    (Binding.whole_selected base bits label body outFrag bodyCore) machine

theorem executed (base bits : Nat) (payable : Bool) (label : Fin W) (body : Prog C SignedBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init SignedBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program bits payable label body))
    (back : Compiler.Compilation base (Frag.init SignedBoundCtx) body)
    (wholeFound : Compiler.compile base (Frag.init RouteCtx) (program bits payable label body)=some whole)
    (bodyFound : Compiler.compile base (Frag.init SignedBoundCtx) body=some back)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run whole.code machine=if payable || decide (machine.callvalue.val=0) then
      if size.val<36 then .revert else if (Solidity.AbiEntry.Kind.int bits).valid word.val then
        run back.code (signedBoundMachine base label word machine) else .revert else .revert := by
  rw [gated base bits payable label body outFrag bodyCore whole wholeFound machine]
  rw [Binding.executed base bits label body outFrag bodyCore
    (Binding.selectedWhole base bits label body outFrag bodyCore) back
    (Binding.whole_selected base bits label body outFrag bodyCore) bodyFound machine word size initialWord initialSize]

theorem early_rejection (base bits : Nat) (payable : Bool) (label : Fin W) (body : Prog C SignedBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init SignedBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program bits payable label body))
    (found : Compiler.compile base (Frag.init RouteCtx) (program bits payable label body)=some whole)
    (machine : Machine) (blocked : (payable || decide (machine.callvalue.val=0))=false) :
    run whole.code machine=.revert := by
  rw [gated base bits payable label body outFrag bodyCore whole found machine]
  simp only [blocked,Bool.false_eq_true,ite_false]

theorem decoded_body (base bits : Nat) (payable : Bool) (label : Fin W) (body : Prog C SignedBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init SignedBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program bits payable label body))
    (back : Compiler.Compilation base (Frag.init SignedBoundCtx) body)
    (wholeFound : Compiler.compile base (Frag.init RouteCtx) (program bits payable label body)=some whole)
    (bodyFound : Compiler.compile base (Frag.init SignedBoundCtx) body=some back)
    (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Machine) (size : Fin W)
    (initialWord : machine.mem base=.val (rawArgumentWord input))
    (initialSize : machine.mem (base+1)=.val size) (represented : size.val=input.size)
    (allowed : (payable || decide (machine.callvalue.val=0))=true) (full : ¬input.size<36)
    (valid : (Solidity.AbiEntry.Kind.int bits).valid (Solidity.AbiEntry.load input.data 4)=true) :
    ∃ value : Solidity.AbiEntry.Word (.int bits),
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams (.int bits))=.ok (.cons (.val (.word value)) .nil) ∧
      (signedBoundMachine base label (rawArgumentWord input) machine).mem
        (cellOf base (.here : Idx SignedBoundCtx (.val .int)))=.val ⟨value.val,value.lt⟩ ∧
      sgn value.val=Solidity.AbiEntry.toInt (Solidity.AbiEntry.load input.data 4) ∧
      run whole.code machine=run back.code (signedBoundMachine base label (rawArgumentWord input) machine) := by
  rcases Binding.decoded_body base bits label body outFrag bodyCore
    (Binding.selectedWhole base bits label body outFrag bodyCore) back
    (Binding.whole_selected base bits label body outFrag bodyCore) bodyFound
    input fuel machine size initialWord initialSize represented full valid with ⟨value,semantic,cell,reading,bodyRun⟩
  refine ⟨value,semantic,cell,reading,?_⟩
  rw [gated base bits payable label body outFrag bodyCore whole wholeFound machine,ite_eq_left allowed,bodyRun]

def certificate : Interface.SignedEntryBodyCertificate program where
  selected := fun base bits payable label body outFrag bodyCore =>
    ⟨compiled base bits payable label body outFrag bodyCore,Binding.selectedBody base body outFrag bodyCore,
      selected base bits payable label body outFrag bodyCore,Binding.body_selected base body outFrag bodyCore⟩
  executed := executed
  early_rejection := early_rejection

/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBody.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBody.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBody.gated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gated
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBody.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBody.early_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms early_rejection
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBody.decoded_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_body
/-- info: 'Solidity.Backend.AbiEntry.SignedEntryBody.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate

end Solidity.Backend.AbiEntry.SignedEntryBody
