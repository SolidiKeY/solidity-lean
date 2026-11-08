import Solidity.Backend.AbiEntry.SingleWordGateInterface

/-! Actual public compiler composition of head and primitive validation.
The raw word and represented size remain input-loading obligations. -/
namespace Solidity.Backend.AbiEntry.SingleWordGate
open Solidity.Evm
open Interface (RouteCtx singleWordParams rawArgumentWord singleWordOutcome wordGateOutcome)

def program (C : Contract) (kind : Solidity.AbiEntry.Kind) (label : Fin W) : Prog C RouteCtx RouteCtx :=
  .cons (.block (HeadGate.program C (singleWordParams kind) label)) (WordGate.program C kind label)

theorem admitted (C : Contract) (kind : Solidity.AbiEntry.Kind) (label : Fin W) :
    inFragP (Frag.init RouteCtx) (program C kind label)=some (Frag.init RouteCtx) := by
  simp only [program,inFragP,inFrag,HeadGate.admitted,Option.map_some]
  exact WordGate.admitted C kind label

def compiled (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W) :
    Compiler.Compilation base (Frag.init RouteCtx) (program C kind label) :=
  .core (Frag.init RouteCtx) (admitted C kind label)

theorem selected (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W) :
    Compiler.compile base (Frag.init RouteCtx) (program C kind label)=some (compiled C base kind label) :=
  ValueGateBody.body_selected base _ _ _ (admitted C kind label)

private theorem overwrite (memory : Nat → Word) (address : Nat) (value : Word) :
    upd (upd memory address value) address value=upd memory address value := by
  funext queried
  by_cases same : queried=address
  · simp only [upd,if_pos same]
  · simp only [upd,if_neg same]

theorem run_program (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run (compileProg base (program C kind label)) machine=singleWordOutcome base kind label word size machine := by
  have head := HeadGate.run_program C base (singleWordParams kind) label machine size initialSize
  change run (compileProg base (HeadGate.program C (singleWordParams kind) label) ++
    compileProg base (WordGate.program C kind label)) machine=_
  change run (compileProg base (HeadGate.program C (singleWordParams kind) label)) machine=
    (if size.val<36 then .revert else .ok {machine with mem := upd machine.mem (base+1) (.val label)} 0) at head
  by_cases short : size.val<36
  · rw [if_pos short] at head
    rw [run_append_revert head]
    exact (if_pos short).symm
  · rw [if_neg short] at head
    rw [run_append_ok head]
    have preserved : (upd machine.mem (base+1) (.val label)) base=.val word :=
      (upd_other machine.mem (.val label) (Nat.ne_of_lt (Nat.lt_succ_self base))).trans initialWord
    rw [WordGate.run_program C base kind label _ word preserved]
    simp only [singleWordOutcome,if_neg short,wordGateOutcome,overwrite]

theorem executed (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C kind label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C kind label)=some result)
    (machine : Machine) (word size : Fin W) (initialWord : machine.mem base=.val word)
    (initialSize : machine.mem (base+1)=.val size) :
    run result.code machine=singleWordOutcome base kind label word size machine := by
  have same : result=compiled C base kind label := Option.some.inj (found.symm.trans (selected C base kind label))
  rw [same]
  exact run_program C base kind label machine word size initialWord initialSize

/-- The existing decoder produces a typed value directly from raw bytes. -/
theorem entry_form (input : Solidity.AbiEntry.Input) (fuel : Nat) (kind : Solidity.AbiEntry.Kind) :
    Solidity.AbiEntry.entry input (fuel+2) (singleWordParams kind)=
      if input.size<36 then .error .revert else
      if valid : kind.valid (Solidity.AbiEntry.load input.data 4)=true then
        .ok (.cons (.val (.word ⟨Solidity.AbiEntry.load input.data 4,Solidity.AbiEntry.load_lt _ _,valid⟩)) .nil)
      else .error .revert := by
  simp only [Solidity.AbiEntry.entry,singleWordParams,Solidity.AbiEntry.headsOf,List.map_cons,List.map_nil,
    Solidity.AbiEntry.Shape.headsSize,Solidity.AbiEntry.Shape.headSize,Nat.add_zero]
  split
  · rfl
  · simp only [Solidity.AbiEntry.enter,Solidity.AbiEntry.melem,Solidity.AbiEntry.Shape.dynamic,
      Bool.false_eq_true,if_false,Nat.add_zero,Solidity.AbiEntry.mdec]
    by_cases valid : kind.valid (Solidity.AbiEntry.load input.data 4)=true
    · simp only [dif_pos valid]; rfl
    · simp only [dif_neg valid]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem entry_rejection (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C kind label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C kind label)=some result)
    (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Machine) (size : Fin W)
    (initialWord : machine.mem base=.val (rawArgumentWord input))
    (initialSize : machine.mem (base+1)=.val size) (represented : size.val=input.size) :
    (run result.code machine=.revert ↔
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams kind)=.error .revert) := by
  rw [executed C base kind label result found machine _ size initialWord initialSize,entry_form]
  simp only [singleWordOutcome,represented,wordGateOutcome,rawArgumentWord]
  by_cases short : input.size<36
  · simp only [if_pos short]
  · simp only [if_neg short]
    by_cases valid : kind.valid (Solidity.AbiEntry.load input.data 4)=true
    · simp only [if_pos valid,dif_pos valid]
      constructor <;> intro impossible <;> cases impossible
    · simp only [if_neg valid,dif_neg valid]

/-- No decoded payload is a premise: the typed word is constructed from the raw load. -/
theorem entry_success (input : Solidity.AbiEntry.Input) (fuel : Nat) (kind : Solidity.AbiEntry.Kind)
    (full : ¬input.size<36) (valid : kind.valid (Solidity.AbiEntry.load input.data 4)=true) :
    Solidity.AbiEntry.entry input (fuel+2) (singleWordParams kind)=
      .ok (.cons (.val (.word ⟨Solidity.AbiEntry.load input.data 4,Solidity.AbiEntry.load_lt _ _,valid⟩)) .nil) := by
  rw [entry_form,if_neg full,dif_pos valid]

/-- A failed head check does not inspect the word cell. -/
theorem short_before_word (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin W)
    (machine : Machine) (size : Fin W) (initialSize : machine.mem (base+1)=.val size)
    (short : size.val<36) : run (compiled C base kind label).code machine=.revert := by
  have head := HeadGate.run_program C base (singleWordParams kind) label machine size initialSize
  change run (compileProg base (HeadGate.program C (singleWordParams kind) label)) machine=
    (if size.val<36 then .revert else .ok {machine with mem := upd machine.mem (base+1) (.val label)} 0) at head
  rw [if_pos short] at head
  exact run_append_revert head

/-- The comparison does not hide the decoder's two levels of fuel. -/
theorem insufficient_fuel (input : Solidity.AbiEntry.Input) (kind : Solidity.AbiEntry.Kind)
    (full : ¬input.size<36) :
    Solidity.AbiEntry.entry input 0 (singleWordParams kind)=.error .fuel ∧
    Solidity.AbiEntry.entry input 1 (singleWordParams kind)=.error .fuel := by
  constructor <;>
    simp only [Solidity.AbiEntry.entry,singleWordParams,Solidity.AbiEntry.headsOf,List.map_cons,List.map_nil,
      Solidity.AbiEntry.Shape.headsSize,Solidity.AbiEntry.Shape.headSize,Nat.add_zero,if_neg full,
      Solidity.AbiEntry.enter,Solidity.AbiEntry.melem,Solidity.AbiEntry.Shape.dynamic,
      Bool.false_eq_true,if_false,Solidity.AbiEntry.mdec] <;> rfl

def certificate : Interface.SingleWordGateCertificate program where
  selected := fun C base kind label => ⟨compiled C base kind label,selected C base kind label⟩
  executed := executed
  entry_rejection := entry_rejection
/-- info: 'Solidity.Backend.AbiEntry.SingleWordGate.admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.SingleWordGate.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.SingleWordGate.run_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_program
/-- info: 'Solidity.Backend.AbiEntry.SingleWordGate.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.SingleWordGate.entry_form' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms entry_form
/-- info: 'Solidity.Backend.AbiEntry.SingleWordGate.entry_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entry_rejection
/-- info: 'Solidity.Backend.AbiEntry.SingleWordGate.entry_success' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms entry_success
/-- info: 'Solidity.Backend.AbiEntry.SingleWordGate.short_before_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_before_word
/-- info: 'Solidity.Backend.AbiEntry.SingleWordGate.insufficient_fuel' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms insufficient_fuel
/-- info: 'Solidity.Backend.AbiEntry.SingleWordGate.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.SingleWordGate
