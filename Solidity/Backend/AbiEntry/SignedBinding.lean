import Solidity.Backend.AbiEntry.SignedBindingInterface

/-! Existing compiler validation and declaration of the actual signed parameter.
The fresh local holds the raw word, not a separately supplied decoded payload. -/
namespace Solidity.Backend.AbiEntry.SignedBinding
open Solidity.Evm
open Interface (RouteCtx SignedBoundCtx singleWordParams rawArgumentWord signedBoundMachine signedBindingOutcome)

def parameter (C : Contract) : Val C RouteCtx .int :=
  .unop .toInt rfl rfl (.simple (.local (.there .here)))

def program (C : Contract) (bits : Nat) (label : Fin W) : Prog C RouteCtx SignedBoundCtx :=
  .cons (.block (SingleWordGate.program C (.int bits) label))
    (.cons (.declLocal .int (.user "argument") (some (parameter C))) .nil)

theorem admitted (C : Contract) (bits : Nat) (label : Fin W) :
    inFragP (Frag.init RouteCtx) (program C bits label)=some (Frag.init SignedBoundCtx) := by
  simp only [program,inFragP,inFrag,SingleWordGate.admitted,Option.map_some]
  rfl

def compiled (C : Contract) (base bits : Nat) (label : Fin W) :
    Compiler.Compilation base (Frag.init RouteCtx) (program C bits label) :=
  .core (Frag.init SignedBoundCtx) (admitted C bits label)

theorem selected (C : Contract) (base bits : Nat) (label : Fin W) :
    Compiler.compile base (Frag.init RouteCtx) (program C bits label)=some (compiled C base bits label) :=
  ValueGateBody.body_selected base _ _ _ (admitted C bits label)

theorem code (C : Contract) (base bits : Nat) (label : Fin W) :
    compileProg base (program C bits label)=
      compileProg base (SingleWordGate.program C (.int bits) label)++[.mload base,.mstore (base+2)] := by
  simp only [program,compileProg,compileStmt,parameter,compileVal,compileSimple,List.append_nil]
  rfl

theorem run_program (C : Contract) (base bits : Nat) (label : Fin W)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run (compileProg base (program C bits label)) machine=signedBindingOutcome base bits label word size machine := by
  rw [code]
  have gate : run (compileProg base (SingleWordGate.program C (.int bits) label)) machine=
      Interface.singleWordOutcome base (.int bits) label word size machine :=
    SingleWordGate.run_program C base (.int bits) label machine word size initialWord initialSize
  simp only [Interface.singleWordOutcome,Interface.wordGateOutcome] at gate
  by_cases short : size.val<36
  · rw [ite_eq_left short] at gate
    rw [run_append_revert gate]
    exact (ite_eq_left short).symm
  · rw [ite_eq_right short] at gate
    by_cases valid : (Solidity.AbiEntry.Kind.int bits).valid word.val=true
    · rw [ite_eq_left valid] at gate
      rw [run_append_ok gate]
      have preserved : upd machine.mem (base+1) (.val label) base=.val word :=
        (upd_other machine.mem (.val label) (Nat.ne_of_lt (Nat.lt_succ_self base))).trans initialWord
      simp only [signedBindingOutcome,ite_eq_right short,ite_eq_left valid,run,exec_cons_zero,Instr.step,Machine.next,
        Out.bind,preserved]
      rfl
    · rw [ite_eq_right valid] at gate
      rw [run_append_revert gate]
      simp only [signedBindingOutcome,ite_eq_right short,ite_eq_right valid]

theorem executed (C : Contract) (base bits : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C bits label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C bits label)=some result)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run result.code machine=signedBindingOutcome base bits label word size machine := by
  have same : result=compiled C base bits label := Option.some.inj (found.symm.trans (selected C base bits label))
  rw [same]
  exact run_program C base bits label machine word size initialWord initialSize

set_option backward.isDefEq.respectTransparency false in
theorem entry_rejection (C : Contract) (base bits : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C bits label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C bits label)=some result)
    (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Machine) (size : Fin W)
    (initialWord : machine.mem base=.val (rawArgumentWord input))
    (initialSize : machine.mem (base+1)=.val size) (represented : size.val=input.size) :
    (run result.code machine=.revert ↔
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams (.int bits))=.error .revert) := by
  rw [executed C base bits label result found machine _ size initialWord initialSize,SingleWordGate.entry_form]
  simp only [signedBindingOutcome,represented,rawArgumentWord]
  by_cases short : input.size<36
  · simp only [ite_eq_left short]
  · simp only [ite_eq_right short]
    by_cases valid : (Solidity.AbiEntry.Kind.int bits).valid (Solidity.AbiEntry.load input.data 4)=true
    · simp only [ite_eq_left valid,dite_eq_left valid]
      constructor <;> intro impossible <;> cases impossible
    · simp only [ite_eq_right valid,dite_eq_right valid]

set_option backward.isDefEq.respectTransparency false in
/-- The newly declared local is the typed semantic word decoded from bytes. -/
theorem decoded_and_bound (C : Contract) (base bits : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C bits label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C bits label)=some result)
    (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Machine) (size : Fin W)
    (initialWord : machine.mem base=.val (rawArgumentWord input))
    (initialSize : machine.mem (base+1)=.val size) (represented : size.val=input.size)
    (full : ¬input.size<36)
    (valid : (Solidity.AbiEntry.Kind.int bits).valid (Solidity.AbiEntry.load input.data 4)=true) :
    ∃ value : Solidity.AbiEntry.Word (.int bits),
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams (.int bits))=
        .ok (.cons (.val (.word value)) .nil) ∧
      run result.code machine=.ok (signedBoundMachine base label (rawArgumentWord input) machine) 0 ∧
      (signedBoundMachine base label (rawArgumentWord input) machine).mem
        (cellOf base (.here : Idx SignedBoundCtx (.val .int)))=.val ⟨value.val,value.lt⟩ ∧
      sgn value.val=Solidity.AbiEntry.toInt (Solidity.AbiEntry.load input.data 4) := by
  refine ⟨⟨Solidity.AbiEntry.load input.data 4,Solidity.AbiEntry.load_lt _ _,valid⟩,
    SingleWordGate.entry_success input fuel (.int bits) full valid,?_,?_,?_⟩
  · rw [executed C base bits label result found machine _ size initialWord initialSize]
    simp only [signedBindingOutcome,represented,ite_eq_right full,rawArgumentWord,ite_eq_left valid]
  · exact upd_same _ _ _
  · rfl

/-- A short head is rejected before the input word or typed cast is read. -/
theorem short_before_word (C : Contract) (base bits : Nat) (label : Fin W)
    (machine : Machine) (size : Fin W) (initialSize : machine.mem (base+1)=.val size)
    (short : size.val<36) : run (compiled C base bits label).code machine=.revert := by
  change run (compileProg base (program C bits label)) machine=.revert
  rw [code]
  exact run_append_revert (SingleWordGate.short_before_word C base (.int bits) label machine size initialSize short)

def certificate : Interface.SignedBindingCertificate program where
  selected := fun C base bits label => ⟨compiled C base bits label,selected C base bits label⟩
  executed := executed
  entry_rejection := entry_rejection

/-- info: 'Solidity.Backend.AbiEntry.SignedBinding.admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.SignedBinding.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.SignedBinding.code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms code
/-- info: 'Solidity.Backend.AbiEntry.SignedBinding.run_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_program
/-- info: 'Solidity.Backend.AbiEntry.SignedBinding.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.SignedBinding.entry_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entry_rejection
/-- info: 'Solidity.Backend.AbiEntry.SignedBinding.decoded_and_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_and_bound
/-- info: 'Solidity.Backend.AbiEntry.SignedBinding.short_before_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_before_word
/-- info: 'Solidity.Backend.AbiEntry.SignedBinding.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.SignedBinding
