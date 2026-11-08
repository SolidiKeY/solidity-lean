import Solidity.Backend.AbiEntry.UIntBindingBodyInterface

/-! One existing compiler program: head/word validation, typed uint declaration,
then the supplied typed body. Body execution is derived, never a premise. -/
namespace Solidity.Backend.AbiEntry.UIntBindingBody
open Solidity.Evm
open Interface (RouteCtx UIntBoundCtx singleWordParams rawArgumentWord uintBoundMachine uintBindingOutcome)
variable {C : Contract} {Δ : Ctx}

def program (bits : Nat) (label : Fin W) (body : Prog C UIntBoundCtx Δ) : Prog C RouteCtx Δ :=
  .cons (.block (SingleWordGate.program C (.uint bits) label))
    (.cons (.declLocal .uint (.user "argument") (some (UIntBinding.parameter C))) body)

theorem admitted (bits : Nat) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag) :
    inFragP (Frag.init RouteCtx) (program bits label body)=some outFrag := by
  simp only [program,inFragP,inFrag,SingleWordGate.admitted,Option.map_some]
  exact bodyCore

def selectedWhole (base bits : Nat) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag) :
    Compiler.Compilation base (Frag.init RouteCtx) (program bits label body) :=
  .core outFrag (admitted bits label body outFrag bodyCore)

def selectedBody (base : Nat) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag) :
    Compiler.Compilation base (Frag.init UIntBoundCtx) body :=
  ValueGateBody.selectedBody base _ body outFrag bodyCore

theorem whole_selected (base bits : Nat) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag) :
    Compiler.compile base (Frag.init RouteCtx) (program bits label body)=
      some (selectedWhole base bits label body outFrag bodyCore) :=
  ValueGateBody.body_selected base _ _ _ (admitted bits label body outFrag bodyCore)

theorem body_selected (base : Nat) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag) :
    Compiler.compile base (Frag.init UIntBoundCtx) body=some (selectedBody base body outFrag bodyCore) :=
  ValueGateBody.body_selected base _ _ _ bodyCore

theorem code (base bits : Nat) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag) :
    (selectedWhole base bits label body outFrag bodyCore).code=
      compileProg base (UIntBinding.program C bits label)++(selectedBody base body outFrag bodyCore).code := by
  change compileProg base (program bits label body)=compileProg base (UIntBinding.program C bits label)++compileProg base body
  rw [UIntBinding.code]
  simp only [program,compileProg,compileStmt,UIntBinding.parameter,compileVal,compileSimple,List.append_assoc]
  rfl

theorem composed (C : Contract) (base bits : Nat) (label : Fin W) (bodyCode : List Evm.Instr)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run (compileProg base (UIntBinding.program C bits label)++bodyCode) machine=
      if size.val<36 then .revert else
      if (Solidity.AbiEntry.Kind.uint bits).valid word.val then
        run bodyCode (uintBoundMachine base label word machine) else .revert := by
  have bindingRun := UIntBinding.run_program C base bits label machine word size initialWord initialSize
  simp only [uintBindingOutcome] at bindingRun
  by_cases short : size.val<36
  · rw [if_pos short] at bindingRun ⊢
    exact run_append_revert bindingRun
  · rw [if_neg short] at bindingRun ⊢
    by_cases valid : (Solidity.AbiEntry.Kind.uint bits).valid word.val=true
    · rw [if_pos valid] at bindingRun ⊢
      exact run_append_ok bindingRun
    · rw [if_neg valid] at bindingRun ⊢
      exact run_append_revert bindingRun

theorem executed (base bits : Nat) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program bits label body))
    (back : Compiler.Compilation base (Frag.init UIntBoundCtx) body)
    (wholeFound : Compiler.compile base (Frag.init RouteCtx) (program bits label body)=some whole)
    (bodyFound : Compiler.compile base (Frag.init UIntBoundCtx) body=some back)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run whole.code machine=if size.val<36 then .revert else
      if (Solidity.AbiEntry.Kind.uint bits).valid word.val then
        run back.code (uintBoundMachine base label word machine) else .revert := by
  have sameWhole : whole=selectedWhole base bits label body outFrag bodyCore :=
    Option.some.inj (wholeFound.symm.trans (whole_selected base bits label body outFrag bodyCore))
  have sameBody : back=selectedBody base body outFrag bodyCore :=
    Option.some.inj (bodyFound.symm.trans (body_selected base body outFrag bodyCore))
  rw [sameWhole,sameBody,code]
  exact composed C base bits label _ machine word size initialWord initialSize

/-- Raw semantic success identifies the actual local subsequently read by the body. -/
theorem decoded_body (base bits : Nat) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program bits label body))
    (back : Compiler.Compilation base (Frag.init UIntBoundCtx) body)
    (wholeFound : Compiler.compile base (Frag.init RouteCtx) (program bits label body)=some whole)
    (bodyFound : Compiler.compile base (Frag.init UIntBoundCtx) body=some back)
    (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Machine) (size : Fin W)
    (initialWord : machine.mem base=.val (rawArgumentWord input))
    (initialSize : machine.mem (base+1)=.val size) (represented : size.val=input.size)
    (full : ¬input.size<36)
    (valid : (Solidity.AbiEntry.Kind.uint bits).valid (Solidity.AbiEntry.load input.data 4)=true) :
    ∃ value : Solidity.AbiEntry.Word (.uint bits),
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams (.uint bits))=
        .ok (.cons (.val (.word value)) .nil) ∧
      (uintBoundMachine base label (rawArgumentWord input) machine).mem
        (cellOf base (.here : Idx UIntBoundCtx (.val .uint)))=.val ⟨value.val,value.lt⟩ ∧
      run whole.code machine=run back.code (uintBoundMachine base label (rawArgumentWord input) machine) := by
  rcases UIntBinding.decoded_and_bound C base bits label (UIntBinding.compiled C base bits label)
    (UIntBinding.selected C base bits label) input fuel machine size initialWord initialSize represented full valid with
    ⟨value,semantic,_,cell⟩
  refine ⟨value,semantic,cell,?_⟩
  rw [executed base bits label body outFrag bodyCore whole back wholeFound bodyFound machine _ size initialWord initialSize]
  simp only [represented,if_neg full,rawArgumentWord,if_pos valid]

/-- Raw decoder failure prevents body execution; success runs the selected body
with the byte-derived uint binding. No successful decoder result is assumed.
The existing source fuel boundary is retained as fuel+2. -/
theorem raw_executed (base bits : Nat) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag)
    (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Machine) (size : Fin W)
    (initialWord : machine.mem base=.val (rawArgumentWord input))
    (initialSize : machine.mem (base+1)=.val size) (represented : size.val=input.size) :
    run (selectedWhole base bits label body outFrag bodyCore).code machine=
      match Solidity.AbiEntry.entry input (fuel+2) (singleWordParams (.uint bits)) with
      | .error _ => .revert
      | .ok _ => run (selectedBody base body outFrag bodyCore).code
          (uintBoundMachine base label (rawArgumentWord input) machine) := by
  rw [code,composed C base bits label _ machine _ size initialWord initialSize,
    SingleWordGate.entry_form]
  simp only [represented,rawArgumentWord]
  by_cases short : input.size<36
  · simp only [if_pos short]
  · simp only [if_neg short]
    by_cases valid : (Solidity.AbiEntry.Kind.uint bits).valid (Solidity.AbiEntry.load input.data 4)=true
    · simp only [if_pos valid,dif_pos valid]
    · simp only [if_neg valid,dif_neg valid]

/-- A short head prevents both the word read and all body execution. -/
theorem short_before_body (base bits : Nat) (label : Fin W) (body : Prog C UIntBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init UIntBoundCtx) body=some outFrag)
    (machine : Machine) (size : Fin W) (initialSize : machine.mem (base+1)=.val size)
    (short : size.val<36) :
    run (selectedWhole base bits label body outFrag bodyCore).code machine=.revert := by
  rw [code,UIntBinding.code]
  rw [List.append_assoc]
  exact run_append_revert (SingleWordGate.short_before_word C base (.uint bits) label machine size initialSize short)

def certificate : Interface.UIntBindingBodyCertificate program where
  selected := fun base bits label body outFrag bodyCore =>
    ⟨selectedWhole base bits label body outFrag bodyCore,selectedBody base body outFrag bodyCore,
      whole_selected base bits label body outFrag bodyCore,body_selected base body outFrag bodyCore,
      code base bits label body outFrag bodyCore⟩
  executed := executed

/-- info: 'Solidity.Backend.AbiEntry.UIntBindingBody.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingBody.whole_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whole_selected
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingBody.body_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_selected
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingBody.code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms code
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingBody.composed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composed
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingBody.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingBody.decoded_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_body
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingBody.short_before_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_before_body
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingBody.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
/-- info: 'Solidity.Backend.AbiEntry.UIntBindingBody.raw_executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_executed
end Solidity.Backend.AbiEntry.UIntBindingBody
