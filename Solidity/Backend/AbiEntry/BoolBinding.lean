import Solidity.Backend.AbiEntry.BoolBindingInterface

/-! Existing compiler validation and declaration of the actual bool parameter.
The fresh local holds the raw word, not a separately supplied decoded payload. -/
namespace Solidity.Backend.AbiEntry.BoolBinding
open Solidity.Evm
open Interface (RouteCtx BoolBoundCtx singleWordParams rawArgumentWord boolValueWord boolBoundMachine boolBindingOutcome)

def parameter (C : Contract) : Val C RouteCtx .bool :=
  .binop .eqB rfl rfl (.simple (.local (.there .here))) (.simple (.lit 1 (by decide)))

def program (C : Contract) (label : Fin W) : Prog C RouteCtx BoolBoundCtx :=
  .cons (.block (SingleWordGate.program C .bool label))
    (.cons (.declLocal .bool (.user "argument") (some (parameter C))) .nil)

theorem admitted (C : Contract) (label : Fin W) :
    inFragP (Frag.init RouteCtx) (program C label)=some (Frag.init BoolBoundCtx) := by
  simp only [program,inFragP,inFrag,SingleWordGate.admitted,Option.map_some]
  rfl

def compiled (C : Contract) (base : Nat) (label : Fin W) :
    Compiler.Compilation base (Frag.init RouteCtx) (program C label) :=
  .core (Frag.init BoolBoundCtx) (admitted C label)

theorem selected (C : Contract) (base : Nat) (label : Fin W) :
    Compiler.compile base (Frag.init RouteCtx) (program C label)=some (compiled C base label) :=
  ValueGateBody.body_selected base _ _ _ (admitted C label)

theorem code (C : Contract) (base : Nat) (label : Fin W) :
    compileProg base (program C label)=
      compileProg base (SingleWordGate.program C .bool label)++[.mload base,.push (.val (wmod 1)),.eq,.mstore (base+2)] := by
  simp only [program,compileProg,compileStmt,parameter,compileVal,compileSimple,List.append_nil]
  rfl

theorem run_program (C : Contract) (base : Nat) (label : Fin W)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run (compileProg base (program C label)) machine=boolBindingOutcome base label word size machine := by
  rw [code]
  have gate := SingleWordGate.run_program C base .bool label machine word size initialWord initialSize
  simp only [Interface.singleWordOutcome,Interface.wordGateOutcome] at gate
  by_cases short : size.val<36
  · rw [if_pos short] at gate
    rw [run_append_revert gate]
    exact (if_pos short).symm
  · rw [if_neg short] at gate
    by_cases valid : Solidity.AbiEntry.Kind.bool.valid word.val=true
    · rw [if_pos valid] at gate
      rw [run_append_ok gate]
      have preserved : upd machine.mem (base+1) (.val label) base=.val word :=
        (upd_other machine.mem (.val label) (Nat.ne_of_lt (Nat.lt_succ_self base))).trans initialWord
      simp only [boolBindingOutcome,if_neg short,if_pos valid,run,exec_cons_zero,Instr.step,Machine.next,
        Out.bind,preserved]
      have literal : (wmod 1).val=1 := by decide
      have symmetric : decide (1=word.val)=decide (word.val=1) := by simp only [eq_comm]
      simp only [literal,symmetric]
      rfl
    · rw [if_neg valid] at gate
      rw [run_append_revert gate]
      simp only [boolBindingOutcome,if_neg short,if_neg valid]

theorem executed (C : Contract) (base : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C label)=some result)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run result.code machine=boolBindingOutcome base label word size machine := by
  have same : result=compiled C base label := Option.some.inj (found.symm.trans (selected C base label))
  rw [same]
  exact run_program C base label machine word size initialWord initialSize

set_option backward.isDefEq.respectTransparency false in
theorem entry_rejection (C : Contract) (base : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C label)=some result)
    (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Machine) (size : Fin W)
    (initialWord : machine.mem base=.val (rawArgumentWord input))
    (initialSize : machine.mem (base+1)=.val size) (represented : size.val=input.size) :
    (run result.code machine=.revert ↔
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams .bool)=.error .revert) := by
  rw [executed C base label result found machine _ size initialWord initialSize,SingleWordGate.entry_form]
  simp only [boolBindingOutcome,represented,rawArgumentWord]
  by_cases short : input.size<36
  · simp only [if_pos short]
  · simp only [if_neg short]
    by_cases valid : Solidity.AbiEntry.Kind.bool.valid (Solidity.AbiEntry.load input.data 4)=true
    · simp only [if_pos valid,dif_pos valid]
      constructor <;> intro impossible <;> cases impossible
    · simp only [if_neg valid,dif_neg valid]

/-- Successful Boolean validation preserves the raw bit in the typed local. -/
theorem validated_word (word : Fin W) (valid : Solidity.AbiEntry.Kind.bool.valid word.val=true) :
    boolValueWord word=word := by
  have small : word.val<2 := of_decide_eq_true valid
  have casesWord : word.val=0 ∨ word.val=1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ small)
  apply Fin.ext
  rcases casesWord with zero | one
  · have notOne : ¬word.val=1 := by rw [zero]; decide
    simp only [boolValueWord,bword,decide_eq_false notOne,Bool.false_eq_true,if_false]
    exact zero.symm
  · simp only [boolValueWord,bword,decide_eq_true one,if_true]
    exact one.symm

set_option backward.isDefEq.respectTransparency false in
/-- The newly declared Boolean local is the semantic validated bit from bytes. -/
theorem decoded_and_bound (C : Contract) (base : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C label)=some result)
    (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Machine) (size : Fin W)
    (initialWord : machine.mem base=.val (rawArgumentWord input))
    (initialSize : machine.mem (base+1)=.val size) (represented : size.val=input.size)
    (full : ¬input.size<36)
    (valid : Solidity.AbiEntry.Kind.bool.valid (Solidity.AbiEntry.load input.data 4)=true) :
    ∃ value : Solidity.AbiEntry.Word .bool,
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams .bool)=
        .ok (.cons (.val (.word value)) .nil) ∧
      run result.code machine=.ok (boolBoundMachine base label (rawArgumentWord input) machine) 0 ∧
      (boolBoundMachine base label (rawArgumentWord input) machine).mem
        (cellOf base (.here : Idx BoolBoundCtx (.val .bool)))=.val ⟨value.val,value.lt⟩ := by
  refine ⟨⟨Solidity.AbiEntry.load input.data 4,Solidity.AbiEntry.load_lt _ _,valid⟩,
    SingleWordGate.entry_success input fuel .bool full valid,?_,?_⟩
  · rw [executed C base label result found machine _ size initialWord initialSize]
    simp only [boolBindingOutcome,represented,if_neg full,rawArgumentWord,if_pos valid]
  · change upd (upd machine.mem (base+1) (Word.val label)) (base+2) (Word.val (boolValueWord (rawArgumentWord input))) (base+2)=Word.val (rawArgumentWord input)
    rw [upd_same,validated_word (rawArgumentWord input) valid]

/-- Rejection of a short head does not inspect the word to be bound. -/
theorem short_before_word (C : Contract) (base : Nat) (label : Fin W)
    (machine : Machine) (size : Fin W) (initialSize : machine.mem (base+1)=.val size)
    (short : size.val<36) : run (compiled C base label).code machine=.revert := by
  change run (compileProg base (program C label)) machine=.revert
  rw [code]
  exact run_append_revert (SingleWordGate.short_before_word C base .bool label machine size initialSize short)

def certificate : Interface.BoolBindingCertificate program where
  selected := fun C base label => ⟨compiled C base label,selected C base label⟩
  executed := executed
  entry_rejection := entry_rejection

/-- info: 'Solidity.Backend.AbiEntry.BoolBinding.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.BoolBinding.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.BoolBinding.code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms code
/-- info: 'Solidity.Backend.AbiEntry.BoolBinding.run_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_program
/-- info: 'Solidity.Backend.AbiEntry.BoolBinding.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.BoolBinding.entry_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entry_rejection
/-- info: 'Solidity.Backend.AbiEntry.BoolBinding.validated_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms validated_word
/-- info: 'Solidity.Backend.AbiEntry.BoolBinding.decoded_and_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_and_bound
/-- info: 'Solidity.Backend.AbiEntry.BoolBinding.short_before_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_before_word
/-- info: 'Solidity.Backend.AbiEntry.BoolBinding.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.BoolBinding
