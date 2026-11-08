import Solidity.Backend.AbiEntry.BoolBindingBodyInterface

/-! One existing compiler program: head/word validation, typed bool declaration,
then the supplied typed body. Body execution is derived, never a premise. -/
namespace Solidity.Backend.AbiEntry.BoolBindingBody
open Solidity.Evm
open Interface (RouteCtx BoolBoundCtx singleWordParams rawArgumentWord boolBoundMachine boolBindingOutcome)
variable {C : Contract} {Δ : Ctx}

def program (label : Fin W) (body : Prog C BoolBoundCtx Δ) : Prog C RouteCtx Δ :=
  .cons (.block (SingleWordGate.program C .bool label))
    (.cons (.declLocal .bool (.user "argument") (some (BoolBinding.parameter C))) body)

theorem admitted (label : Fin W) (body : Prog C BoolBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init BoolBoundCtx) body=some outFrag) :
    inFragP (Frag.init RouteCtx) (program label body)=some outFrag := by
  simp only [program,inFragP,inFrag,SingleWordGate.admitted,Option.map_some]
  exact bodyCore

def selectedWhole (base : Nat) (label : Fin W) (body : Prog C BoolBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init BoolBoundCtx) body=some outFrag) :
    Compiler.Compilation base (Frag.init RouteCtx) (program label body) :=
  .core outFrag (admitted label body outFrag bodyCore)

def selectedBody (base : Nat) (body : Prog C BoolBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init BoolBoundCtx) body=some outFrag) :
    Compiler.Compilation base (Frag.init BoolBoundCtx) body :=
  ValueGateBody.selectedBody base _ body outFrag bodyCore

theorem whole_selected (base : Nat) (label : Fin W) (body : Prog C BoolBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init BoolBoundCtx) body=some outFrag) :
    Compiler.compile base (Frag.init RouteCtx) (program label body)=
      some (selectedWhole base label body outFrag bodyCore) :=
  ValueGateBody.body_selected base _ _ _ (admitted label body outFrag bodyCore)

theorem body_selected (base : Nat) (body : Prog C BoolBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init BoolBoundCtx) body=some outFrag) :
    Compiler.compile base (Frag.init BoolBoundCtx) body=some (selectedBody base body outFrag bodyCore) :=
  ValueGateBody.body_selected base _ _ _ bodyCore

theorem code (base : Nat) (label : Fin W) (body : Prog C BoolBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init BoolBoundCtx) body=some outFrag) :
    (selectedWhole base label body outFrag bodyCore).code=
      compileProg base (BoolBinding.program C label)++(selectedBody base body outFrag bodyCore).code := by
  change compileProg base (program label body)=compileProg base (BoolBinding.program C label)++compileProg base body
  rw [BoolBinding.code]
  simp only [program,compileProg,compileStmt,BoolBinding.parameter,compileVal,compileSimple,List.append_assoc]
  rfl

theorem composed (C : Contract) (base : Nat) (label : Fin W) (bodyCode : List Evm.Instr)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run (compileProg base (BoolBinding.program C label)++bodyCode) machine=
      if size.val<36 then .revert else
      if Solidity.AbiEntry.Kind.bool.valid word.val then
        run bodyCode (boolBoundMachine base label word machine) else .revert := by
  have bindingRun : run (compileProg base (BoolBinding.program C label)) machine=
      boolBindingOutcome base label word size machine :=
    BoolBinding.run_program C base label machine word size initialWord initialSize
  simp only [boolBindingOutcome] at bindingRun
  by_cases short : size.val<36
  · rw [if_pos short] at bindingRun ⊢
    exact run_append_revert bindingRun
  · rw [if_neg short] at bindingRun ⊢
    by_cases valid : Solidity.AbiEntry.Kind.bool.valid word.val=true
    · rw [if_pos valid] at bindingRun ⊢
      exact run_append_ok bindingRun
    · rw [if_neg valid] at bindingRun ⊢
      exact run_append_revert bindingRun

theorem executed (base : Nat) (label : Fin W) (body : Prog C BoolBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init BoolBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program label body))
    (back : Compiler.Compilation base (Frag.init BoolBoundCtx) body)
    (wholeFound : Compiler.compile base (Frag.init RouteCtx) (program label body)=some whole)
    (bodyFound : Compiler.compile base (Frag.init BoolBoundCtx) body=some back)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run whole.code machine=if size.val<36 then .revert else
      if Solidity.AbiEntry.Kind.bool.valid word.val then
        run back.code (boolBoundMachine base label word machine) else .revert := by
  have sameWhole : whole=selectedWhole base label body outFrag bodyCore :=
    Option.some.inj (wholeFound.symm.trans (whole_selected base label body outFrag bodyCore))
  have sameBody : back=selectedBody base body outFrag bodyCore :=
    Option.some.inj (bodyFound.symm.trans (body_selected base body outFrag bodyCore))
  rw [sameWhole,sameBody,code]
  exact composed C base label _ machine word size initialWord initialSize

set_option backward.isDefEq.respectTransparency false in
/-- Raw semantic success identifies the actual local subsequently read by the body. -/
theorem decoded_body (base : Nat) (label : Fin W) (body : Prog C BoolBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init BoolBoundCtx) body=some outFrag)
    (whole : Compiler.Compilation base (Frag.init RouteCtx) (program label body))
    (back : Compiler.Compilation base (Frag.init BoolBoundCtx) body)
    (wholeFound : Compiler.compile base (Frag.init RouteCtx) (program label body)=some whole)
    (bodyFound : Compiler.compile base (Frag.init BoolBoundCtx) body=some back)
    (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Machine) (size : Fin W)
    (initialWord : machine.mem base=.val (rawArgumentWord input))
    (initialSize : machine.mem (base+1)=.val size) (represented : size.val=input.size)
    (full : ¬input.size<36)
    (valid : Solidity.AbiEntry.Kind.bool.valid (Solidity.AbiEntry.load input.data 4)=true) :
    ∃ value : Solidity.AbiEntry.Word .bool,
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams .bool)=
        .ok (.cons (.val (.word value)) .nil) ∧
      (boolBoundMachine base label (rawArgumentWord input) machine).mem
        (cellOf base (.here : Idx BoolBoundCtx (.val .bool)))=.val ⟨value.val,value.lt⟩ ∧
      run whole.code machine=run back.code (boolBoundMachine base label (rawArgumentWord input) machine) := by
  rcases BoolBinding.decoded_and_bound C base label (BoolBinding.compiled C base label)
    (BoolBinding.selected C base label) input fuel machine size initialWord initialSize represented full valid with
    ⟨value,semantic,_,cell⟩
  refine ⟨value,semantic,cell,?_⟩
  rw [executed base label body outFrag bodyCore whole back wholeFound bodyFound machine _ size initialWord initialSize]
  simp only [represented,if_neg full,rawArgumentWord,if_pos valid]

/-- A short head prevents both the word read and all body execution. -/
theorem short_before_body (base : Nat) (label : Fin W) (body : Prog C BoolBoundCtx Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP (Frag.init BoolBoundCtx) body=some outFrag)
    (machine : Machine) (size : Fin W) (initialSize : machine.mem (base+1)=.val size)
    (short : size.val<36) :
    run (selectedWhole base label body outFrag bodyCore).code machine=.revert := by
  rw [code,BoolBinding.code]
  rw [List.append_assoc]
  exact run_append_revert (SingleWordGate.short_before_word C base .bool label machine size initialSize short)

def certificate : Interface.BoolBindingBodyCertificate program where
  selected := fun base label body outFrag bodyCore =>
    ⟨selectedWhole base label body outFrag bodyCore,selectedBody base body outFrag bodyCore,
      whole_selected base label body outFrag bodyCore,body_selected base body outFrag bodyCore,
      code base label body outFrag bodyCore⟩
  executed := executed

/-- info: 'Solidity.Backend.AbiEntry.BoolBindingBody.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingBody.whole_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whole_selected
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingBody.body_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_selected
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingBody.code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms code
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingBody.composed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composed
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingBody.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingBody.decoded_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_body
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingBody.short_before_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_before_body
/-- info: 'Solidity.Backend.AbiEntry.BoolBindingBody.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.BoolBindingBody
