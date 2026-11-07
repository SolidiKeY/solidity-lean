import Solidity.Backend.AbiEntry.WordCarrierEntryBodyInterface

/-! Existing compiler composition of value checking, primitive validation, raw
uint carrier binding and an actual typed body. No body run/result is assumed;
Source signature/body association and native loading remain separate. -/
namespace Solidity.Backend.AbiEntry.WordCarrierEntryBody
open Solidity.Evm
open Interface
variable {C : Contract} {Δ : Ctx}

namespace Binding
def program (kind : Solidity.AbiEntry.Kind) (label : Fin W) (body : Prog C UIntBoundCtx Δ) : Prog C RouteCtx Δ :=
  .cons (.block (SingleWordGate.program C kind label))
    (.cons (.declLocal .uint (.user "argument") (some (UIntBinding.parameter C))) body)

theorem admitted (kind : Solidity.AbiEntry.Kind) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag) :
    inFragP (Frag.init RouteCtx) (program kind label body)=some outFrag := by
  simp only [program,inFragP,inFrag,SingleWordGate.admitted,Option.map_some]
  exact bodyCore

def selectedWhole (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag) :
    Compiler.Compilation base (Frag.init RouteCtx) (program kind label body) :=
  .core outFrag (admitted kind label body outFrag bodyCore)

def selectedBody (base : Nat) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag) :
    Compiler.Compilation base (Frag.init UIntBoundCtx) body :=
  ValueGateBody.selectedBody base _ body outFrag bodyCore

theorem whole_selected (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag) :
    Compiler.compile base (Frag.init RouteCtx) (program kind label body)=
      some (selectedWhole base kind label body outFrag bodyCore) :=
  ValueGateBody.body_selected base _ _ _ (admitted kind label body outFrag bodyCore)

theorem body_selected (base : Nat) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag) :
    Compiler.compile base (Frag.init UIntBoundCtx) body=some (selectedBody base body outFrag bodyCore) :=
  ValueGateBody.body_selected base _ _ _ bodyCore

theorem code (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag) :
    (selectedWhole base kind label body outFrag bodyCore).code=
      compileProg base (WordCarrierBinding.program C kind label)++(selectedBody base body outFrag bodyCore).code := by
  change compileProg base (program kind label body)=compileProg base (WordCarrierBinding.program C kind label)++compileProg base body
  rw [WordCarrierBinding.code]
  simp only [program,compileProg,compileStmt,UIntBinding.parameter,compileVal,compileSimple,List.append_assoc]
  rfl

theorem composed (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W) (bodyCode : List Evm.Instr)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run (compileProg base (WordCarrierBinding.program C kind label)++bodyCode) machine=
      if size.val<36 then .revert else
      if kind.valid word.val then
        run bodyCode (uintBoundMachine base label word machine) else .revert := by
  have bindingRun : run (compileProg base (WordCarrierBinding.program C kind label)) machine=
      wordCarrierOutcome base kind label word size machine :=
    WordCarrierBinding.run_program C base kind label machine word size initialWord initialSize
  simp only [wordCarrierOutcome] at bindingRun
  by_cases short : size.val<36
  · rw [if_pos short] at bindingRun ⊢
    exact run_append_revert bindingRun
  · rw [if_neg short] at bindingRun ⊢
    by_cases valid : kind.valid word.val=true
    · rw [if_pos valid] at bindingRun ⊢
      exact run_append_ok bindingRun
    · rw [if_neg valid] at bindingRun ⊢
      exact run_append_revert bindingRun

theorem executed (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program kind label body))
    (back : Compiler.Compilation base (Frag.init UIntBoundCtx) body)
    (wholeFound : Compiler.compile base (Frag.init RouteCtx) (program kind label body)=some whole)
    (bodyFound : Compiler.compile base (Frag.init UIntBoundCtx) body=some back)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run whole.code machine=if size.val<36 then .revert else
      if kind.valid word.val then
        run back.code (uintBoundMachine base label word machine) else .revert := by
  have sameWhole : whole=selectedWhole base kind label body outFrag bodyCore :=
    Option.some.inj (wholeFound.symm.trans (whole_selected base kind label body outFrag bodyCore))
  have sameBody : back=selectedBody base body outFrag bodyCore :=
    Option.some.inj (bodyFound.symm.trans (body_selected base body outFrag bodyCore))
  rw [sameWhole,sameBody,code]
  exact composed C base kind label _ machine word size initialWord initialSize

/-- Raw semantic success identifies the actual local subsequently read by the body. -/
theorem decoded_body (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program kind label body))
    (back : Compiler.Compilation base (Frag.init UIntBoundCtx) body)
    (wholeFound : Compiler.compile base (Frag.init RouteCtx) (program kind label body)=some whole)
    (bodyFound : Compiler.compile base (Frag.init UIntBoundCtx) body=some back)
    (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Machine) (size : Fin W)
    (initialWord : machine.mem base=.val (rawArgumentWord input))
    (initialSize : machine.mem (base+1)=.val size) (represented : size.val=input.size)
    (full : ¬input.size<36)
    (valid : kind.valid (Solidity.AbiEntry.load input.data 4)=true) :
    ∃ value : Solidity.AbiEntry.Word kind,
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams kind)=
        .ok (.cons (.val (.word value)) .nil) ∧
      (uintBoundMachine base label (rawArgumentWord input) machine).mem
        (cellOf base (.here : Idx UIntBoundCtx (.val .uint)))=.val ⟨value.val,value.lt⟩ ∧
      run whole.code machine=run back.code (uintBoundMachine base label (rawArgumentWord input) machine) := by
  rcases WordCarrierBinding.decoded_and_bound C base kind label (WordCarrierBinding.compiled C base kind label)
    (WordCarrierBinding.selected C base kind label) input fuel machine size initialWord initialSize represented full valid with
    ⟨value,semantic,_,cell⟩
  refine ⟨value,semantic,cell,?_⟩
  rw [executed base kind label body outFrag bodyCore whole back wholeFound bodyFound machine _ size initialWord initialSize]
  simp only [represented,if_neg full,rawArgumentWord,if_pos valid]

/-- A short head prevents both the word read and all body execution. -/
theorem short_before_body (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag)
    (machine : Machine) (size : Fin W) (initialSize : machine.mem (base+1)=.val size)
    (short : size.val<36) :
    run (selectedWhole base kind label body outFrag bodyCore).code machine=.revert := by
  rw [code,WordCarrierBinding.code]
  rw [List.append_assoc]
  exact run_append_revert (SingleWordGate.short_before_word C base kind label machine size initialSize short)

/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBody.Binding.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBody.Binding.whole_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whole_selected
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBody.Binding.body_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_selected
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBody.Binding.code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms code
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBody.Binding.composed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composed
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBody.Binding.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBody.Binding.decoded_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_body
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBody.Binding.short_before_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_before_body
end Binding

def program (kind : Solidity.AbiEntry.Kind) (payable : Bool) (label : Fin W) (body : Prog C UIntBoundCtx Δ) : Prog C RouteCtx Δ :=
  ValueGateBody.guard payable (Binding.program kind label body)

theorem admitted (kind : Solidity.AbiEntry.Kind) (payable : Bool) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag) :
    inFragP (Frag.init RouteCtx) (program kind payable label body)=some outFrag :=
  ValueGateBody.admitted _ _ payable outFrag (Binding.admitted kind label body outFrag bodyCore)

def compiled (base : Nat) (kind : Solidity.AbiEntry.Kind) (payable : Bool) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag) :
    Compiler.Compilation base (Frag.init RouteCtx) (program kind payable label body) :=
  ValueGateBody.selectedWhole base _ (Binding.program kind label body) payable outFrag
    (Binding.admitted kind label body outFrag bodyCore)

theorem selected (base : Nat) (kind : Solidity.AbiEntry.Kind) (payable : Bool) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag) :
    Compiler.compile base (Frag.init RouteCtx) (program kind payable label body)=
      some (compiled base kind payable label body outFrag bodyCore) :=
  ValueGateBody.whole_selected base _ (Binding.program kind label body) payable outFrag
    (Binding.admitted kind label body outFrag bodyCore)

theorem gated (base : Nat) (kind : Solidity.AbiEntry.Kind) (payable : Bool) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program kind payable label body))
    (found : Compiler.compile base (Frag.init RouteCtx) (program kind payable label body)=some whole)
    (machine : Machine) :
    run whole.code machine=if payable || decide (machine.callvalue.val=0) then
      run (Binding.selectedWhole base kind label body outFrag bodyCore).code machine else .revert :=
  ValueGateBody.executed base _ (Binding.program kind label body) payable outFrag
    (Binding.admitted kind label body outFrag bodyCore) whole
    (Binding.selectedWhole base kind label body outFrag bodyCore) found
    (Binding.whole_selected base kind label body outFrag bodyCore) machine

theorem executed (base : Nat) (kind : Solidity.AbiEntry.Kind) (payable : Bool) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program kind payable label body))
    (back : Compiler.Compilation base (Frag.init UIntBoundCtx) body)
    (wholeFound : Compiler.compile base (Frag.init RouteCtx) (program kind payable label body)=some whole)
    (bodyFound : Compiler.compile base (Frag.init UIntBoundCtx) body=some back)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run whole.code machine=if payable || decide (machine.callvalue.val=0) then
      if size.val<36 then .revert else if kind.valid word.val then
        run back.code (uintBoundMachine base label word machine) else .revert else .revert := by
  rw [gated base kind payable label body outFrag bodyCore whole wholeFound machine]
  rw [Binding.executed base kind label body outFrag bodyCore
    (Binding.selectedWhole base kind label body outFrag bodyCore) back
    (Binding.whole_selected base kind label body outFrag bodyCore) bodyFound machine word size initialWord initialSize]

theorem early_rejection (base : Nat) (kind : Solidity.AbiEntry.Kind) (payable : Bool) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program kind payable label body))
    (found : Compiler.compile base (Frag.init RouteCtx) (program kind payable label body)=some whole)
    (machine : Machine) (blocked : (payable || decide (machine.callvalue.val=0))=false) :
    run whole.code machine=.revert := by
  rw [gated base kind payable label body outFrag bodyCore whole found machine]
  simp only [blocked,Bool.false_eq_true,if_false]

theorem decoded_body (base : Nat) (kind : Solidity.AbiEntry.Kind) (payable : Bool) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program kind payable label body))
    (back : Compiler.Compilation base (Frag.init UIntBoundCtx) body)
    (wholeFound : Compiler.compile base (Frag.init RouteCtx) (program kind payable label body)=some whole)
    (bodyFound : Compiler.compile base (Frag.init UIntBoundCtx) body=some back)
    (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Machine) (size : Fin W)
    (initialWord : machine.mem base=.val (rawArgumentWord input))
    (initialSize : machine.mem (base+1)=.val size) (represented : size.val=input.size)
    (allowed : (payable || decide (machine.callvalue.val=0))=true) (full : ¬input.size<36)
    (valid : kind.valid (Solidity.AbiEntry.load input.data 4)=true) :
    ∃ value : Solidity.AbiEntry.Word kind,
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams kind)=.ok (.cons (.val (.word value)) .nil) ∧
      (uintBoundMachine base label (rawArgumentWord input) machine).mem
        (cellOf base (.here : Idx UIntBoundCtx (.val .uint)))=.val ⟨value.val,value.lt⟩ ∧
      run whole.code machine=run back.code (uintBoundMachine base label (rawArgumentWord input) machine) := by
  rcases Binding.decoded_body base kind label body outFrag bodyCore
    (Binding.selectedWhole base kind label body outFrag bodyCore) back
    (Binding.whole_selected base kind label body outFrag bodyCore) bodyFound
    input fuel machine size initialWord initialSize represented full valid with ⟨value,semantic,cell,bodyRun⟩
  refine ⟨value,semantic,cell,?_⟩
  rw [gated base kind payable label body outFrag bodyCore whole wholeFound machine,if_pos allowed,bodyRun]

def certificate : Interface.WordCarrierEntryBodyCertificate program where
  selected := fun base kind payable label body outFrag bodyCore =>
    ⟨compiled base kind payable label body outFrag bodyCore,Binding.selectedBody base body outFrag bodyCore,
      selected base kind payable label body outFrag bodyCore,Binding.body_selected base body outFrag bodyCore⟩
  executed := executed
  early_rejection := early_rejection


/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBody.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBody.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBody.gated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gated
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBody.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBody.early_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms early_rejection
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBody.decoded_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_body
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierEntryBody.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.WordCarrierEntryBody
