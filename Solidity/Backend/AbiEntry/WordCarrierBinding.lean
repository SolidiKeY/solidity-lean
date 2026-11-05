import Solidity.Backend.AbiEntry.WordCarrierBindingInterface

/-! Actual primitive validation and bit-preserving raw word binding.
This uses the existing typed compiler and uint carrier declaration. Boolean
and signed source locals retain their separate typed bindings. -/
namespace Solidity.Backend.AbiEntry.WordCarrierBinding
open Solidity.Evm
open Interface (RouteCtx UIntBoundCtx singleWordParams rawArgumentWord uintBoundMachine wordCarrierOutcome)

def program (C : Contract) (kind : Solidity.AbiEntry.Kind) (label : Fin W) : Prog C RouteCtx UIntBoundCtx :=
  .cons (.block (SingleWordGate.program C kind label))
    (.cons (.declLocal .uint (.user "argument") (some (UIntBinding.parameter C))) .nil)

theorem admitted (C : Contract) (kind : Solidity.AbiEntry.Kind) (label : Fin W) :
    inFragP (Frag.init RouteCtx) (program C kind label)=some (Frag.init UIntBoundCtx) := by
  simp only [program,inFragP,inFrag,SingleWordGate.admitted,Option.map_some]
  rfl

def compiled (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W) :
    Compiler.Compilation base (Frag.init RouteCtx) (program C kind label) :=
  .core (Frag.init UIntBoundCtx) (admitted C kind label)

theorem selected (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W) :
    Compiler.compile base (Frag.init RouteCtx) (program C kind label)=some (compiled C base kind label) :=
  ValueGateBody.body_selected base _ _ _ (admitted C kind label)

theorem code (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W) :
    compileProg base (program C kind label)=
      compileProg base (SingleWordGate.program C kind label)++[.mload base,.mstore (base+2)] := by
  simp only [program,compileProg,compileStmt,UIntBinding.parameter,compileVal,compileSimple,List.append_nil]
  rfl

theorem run_program (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run (compileProg base (program C kind label)) machine=wordCarrierOutcome base kind label word size machine := by
  rw [code]
  have gate : run (compileProg base (SingleWordGate.program C kind label)) machine=
      Interface.singleWordOutcome base kind label word size machine :=
    SingleWordGate.run_program C base kind label machine word size initialWord initialSize
  simp only [Interface.singleWordOutcome,Interface.wordGateOutcome] at gate
  by_cases short : size.val<36
  · rw [if_pos short] at gate
    rw [run_append_revert gate]
    exact (if_pos short).symm
  · rw [if_neg short] at gate
    by_cases valid : kind.valid word.val=true
    · rw [if_pos valid] at gate
      rw [run_append_ok gate]
      have preserved : upd machine.mem (base+1) (.val label) base=.val word :=
        (upd_other machine.mem (.val label) (Nat.ne_of_lt (Nat.lt_succ_self base))).trans initialWord
      simp only [wordCarrierOutcome,if_neg short,if_pos valid,run,exec_cons_zero,Instr.step,Machine.next,
        Out.bind,preserved]
      rfl
    · rw [if_neg valid] at gate
      rw [run_append_revert gate]
      simp only [wordCarrierOutcome,if_neg short,if_neg valid]

theorem executed (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C kind label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C kind label)=some result)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run result.code machine=wordCarrierOutcome base kind label word size machine := by
  have same : result=compiled C base kind label := Option.some.inj (found.symm.trans (selected C base kind label))
  rw [same]
  exact run_program C base kind label machine word size initialWord initialSize

theorem entry_rejection (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C kind label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C kind label)=some result)
    (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Machine) (size : Fin W)
    (initialWord : machine.mem base=.val (rawArgumentWord input))
    (initialSize : machine.mem (base+1)=.val size) (represented : size.val=input.size) :
    (run result.code machine=.revert ↔
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams kind)=.error .revert) := by
  rw [executed C base kind label result found machine _ size initialWord initialSize,SingleWordGate.entry_form]
  simp only [wordCarrierOutcome,represented,rawArgumentWord]
  by_cases short : input.size<36
  · simp only [if_pos short]
  · simp only [if_neg short]
    by_cases valid : kind.valid (Solidity.AbiEntry.load input.data 4)=true
    · simp only [if_pos valid,dif_pos valid]
      constructor <;> intro impossible <;> cases impossible
    · simp only [if_neg valid,dif_neg valid]

/-- The newly declared local is the typed semantic word decoded from bytes. -/
theorem decoded_and_bound (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C kind label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C kind label)=some result)
    (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Machine) (size : Fin W)
    (initialWord : machine.mem base=.val (rawArgumentWord input))
    (initialSize : machine.mem (base+1)=.val size) (represented : size.val=input.size)
    (full : ¬input.size<36)
    (valid : kind.valid (Solidity.AbiEntry.load input.data 4)=true) :
    ∃ value : Solidity.AbiEntry.Word kind,
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams kind)=
        .ok (.cons (.val (.word value)) .nil) ∧
      run result.code machine=.ok (uintBoundMachine base label (rawArgumentWord input) machine) 0 ∧
      (uintBoundMachine base label (rawArgumentWord input) machine).mem
        (cellOf base (.here : Idx UIntBoundCtx (.val .uint)))=.val ⟨value.val,value.lt⟩ := by
  refine ⟨⟨Solidity.AbiEntry.load input.data 4,Solidity.AbiEntry.load_lt _ _,valid⟩,
    SingleWordGate.entry_success input fuel kind full valid,?_,?_⟩
  · rw [executed C base kind label result found machine _ size initialWord initialSize]
    simp only [wordCarrierOutcome,represented,if_neg full,rawArgumentWord,if_pos valid]
  · exact upd_same _ _ _

def certificate : Interface.WordCarrierBindingCertificate program where
  selected := fun C base kind label => ⟨compiled C base kind label,selected C base kind label⟩
  executed := executed
  entry_rejection := entry_rejection

/-- Head rejection precedes reading the raw carrier or declaring a local. -/
theorem short_before_word (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W)
    (machine : Machine) (size : Fin W) (initialSize : machine.mem (base+1)=.val size)
    (short : size.val<36) : run (compiled C base kind label).code machine=.revert := by
  rw [show (compiled C base kind label).code=compileProg base (program C kind label) from rfl,code]
  exact run_append_revert (SingleWordGate.short_before_word C base kind label machine size initialSize short)

/-- The uint case is the existing binder, with no alternative representation. -/
theorem uint_specialization (C : Contract) (bits : Nat) (label : Fin W) :
    program C (.uint bits) label=UIntBinding.program C bits label := rfl

/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBinding.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBinding.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBinding.code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms code
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBinding.run_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_program
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBinding.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBinding.entry_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entry_rejection
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBinding.decoded_and_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_and_bound
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBinding.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBinding.short_before_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_before_word
/-- info: 'Solidity.Backend.AbiEntry.WordCarrierBinding.uint_specialization' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms uint_specialization
end Solidity.Backend.AbiEntry.WordCarrierBinding
