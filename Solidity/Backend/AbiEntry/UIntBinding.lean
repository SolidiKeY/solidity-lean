import Solidity.Backend.AbiEntry.UIntBindingInterface

/-! Existing compiler validation and declaration of the actual uint parameter.
The fresh local holds the raw word, not a separately supplied decoded payload. -/
namespace Solidity.Backend.AbiEntry.UIntBinding
open Solidity.Evm
open Interface (RouteCtx UIntBoundCtx singleWordParams rawArgumentWord uintBoundMachine uintBindingOutcome)

def parameter (C : Contract) : Val C RouteCtx .uint := .simple (.local (.there .here))

def program (C : Contract) (bits : Nat) (label : Fin W) : Prog C RouteCtx UIntBoundCtx :=
  .cons (.block (SingleWordGate.program C (.uint bits) label))
    (.cons (.declLocal .uint (.user "argument") (some (parameter C))) .nil)

theorem admitted (C : Contract) (bits : Nat) (label : Fin W) :
    inFragP (Frag.init RouteCtx) (program C bits label)=some (Frag.init UIntBoundCtx) := by
  simp only [program,inFragP,inFrag,SingleWordGate.admitted,Option.map_some]
  rfl

def compiled (C : Contract) (base bits : Nat) (label : Fin W) :
    Compiler.Compilation base (Frag.init RouteCtx) (program C bits label) :=
  .core (Frag.init UIntBoundCtx) (admitted C bits label)

theorem selected (C : Contract) (base bits : Nat) (label : Fin W) :
    Compiler.compile base (Frag.init RouteCtx) (program C bits label)=some (compiled C base bits label) :=
  ValueGateBody.body_selected base _ _ _ (admitted C bits label)

theorem code (C : Contract) (base bits : Nat) (label : Fin W) :
    compileProg base (program C bits label)=
      compileProg base (SingleWordGate.program C (.uint bits) label)++[.mload base,.mstore (base+2)] := by
  simp only [program,compileProg,compileStmt,parameter,compileVal,compileSimple,List.append_nil]
  rfl

theorem run_program (C : Contract) (base bits : Nat) (label : Fin W)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run (compileProg base (program C bits label)) machine=uintBindingOutcome base bits label word size machine := by
  rw [code]
  have gate := SingleWordGate.run_program C base (.uint bits) label machine word size initialWord initialSize
  simp only [Interface.singleWordOutcome,Interface.wordGateOutcome] at gate
  by_cases short : size.val<36
  · rw [if_pos short] at gate
    rw [run_append_revert gate]
    exact (if_pos short).symm
  · rw [if_neg short] at gate
    by_cases valid : (Solidity.AbiEntry.Kind.uint bits).valid word.val=true
    · rw [if_pos valid] at gate
      rw [run_append_ok gate]
      have preserved : upd machine.mem (base+1) (.val label) base=.val word :=
        (upd_other machine.mem (.val label) (Nat.ne_of_lt (Nat.lt_succ_self base))).trans initialWord
      simp only [uintBindingOutcome,if_neg short,if_pos valid,run,exec_cons_zero,Instr.step,Machine.next,
        Out.bind,preserved]
      rfl
    · rw [if_neg valid] at gate
      rw [run_append_revert gate]
      simp only [uintBindingOutcome,if_neg short,if_neg valid]

theorem executed (C : Contract) (base bits : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C bits label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C bits label)=some result)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run result.code machine=uintBindingOutcome base bits label word size machine := by
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
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams (.uint bits))=.error .revert) := by
  rw [executed C base bits label result found machine _ size initialWord initialSize,SingleWordGate.entry_form]
  simp only [uintBindingOutcome,represented,rawArgumentWord]
  by_cases short : input.size<36
  · simp only [if_pos short]
  · simp only [if_neg short]
    by_cases valid : (Solidity.AbiEntry.Kind.uint bits).valid (Solidity.AbiEntry.load input.data 4)=true
    · simp only [if_pos valid,dif_pos valid]
      constructor <;> intro impossible <;> cases impossible
    · simp only [if_neg valid,dif_neg valid]

set_option backward.isDefEq.respectTransparency false in
/-- The newly declared local is the typed semantic word decoded from bytes. -/
theorem decoded_and_bound (C : Contract) (base bits : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C bits label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C bits label)=some result)
    (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Machine) (size : Fin W)
    (initialWord : machine.mem base=.val (rawArgumentWord input))
    (initialSize : machine.mem (base+1)=.val size) (represented : size.val=input.size)
    (full : ¬input.size<36)
    (valid : (Solidity.AbiEntry.Kind.uint bits).valid (Solidity.AbiEntry.load input.data 4)=true) :
    ∃ value : Solidity.AbiEntry.Word (.uint bits),
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams (.uint bits))=
        .ok (.cons (.val (.word value)) .nil) ∧
      run result.code machine=.ok (uintBoundMachine base label (rawArgumentWord input) machine) 0 ∧
      (uintBoundMachine base label (rawArgumentWord input) machine).mem
        (cellOf base (.here : Idx UIntBoundCtx (.val .uint)))=.val ⟨value.val,value.lt⟩ := by
  refine ⟨⟨Solidity.AbiEntry.load input.data 4,Solidity.AbiEntry.load_lt _ _,valid⟩,
    SingleWordGate.entry_success input fuel (.uint bits) full valid,?_,?_⟩
  · rw [executed C base bits label result found machine _ size initialWord initialSize]
    simp only [uintBindingOutcome,represented,if_neg full,rawArgumentWord,if_pos valid]
  · exact upd_same _ _ _

def certificate : Interface.UIntBindingCertificate program where
  selected := fun C base bits label => ⟨compiled C base bits label,selected C base bits label⟩
  executed := executed
  entry_rejection := entry_rejection

/-- info: 'Solidity.Backend.AbiEntry.UIntBinding.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.UIntBinding.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.UIntBinding.code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms code
/-- info: 'Solidity.Backend.AbiEntry.UIntBinding.run_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_program
/-- info: 'Solidity.Backend.AbiEntry.UIntBinding.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.UIntBinding.entry_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entry_rejection
/-- info: 'Solidity.Backend.AbiEntry.UIntBinding.decoded_and_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_and_bound
/-- info: 'Solidity.Backend.AbiEntry.UIntBinding.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.UIntBinding
