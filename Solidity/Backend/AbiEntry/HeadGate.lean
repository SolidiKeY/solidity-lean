import Solidity.Backend.AbiEntry.HeadGateInterface

/-! Actual typed head guard with exact execution. Unrepresentable semantic
extents reject rather than wrap a PUSH immediate. Subsequent decoding is open. -/
namespace Solidity.Backend.AbiEntry.HeadGate
open Solidity.Evm
open Interface (RouteCtx headGateOutcome)

def condition (C : Contract) (bound : Fin W) : Val C RouteCtx .bool :=
  .unop .not rfl rfl (.binop .lt rfl rfl (.simple (.local .here))
    (.simple (.lit (bound.val : Int) (PrimTy.inRange_uint_of_lt bound.isLt))))

def program (C : Contract) (parameters : List Solidity.AbiEntry.Param) (label : Fin W) : Prog C RouteCtx RouteCtx :=
  if fits : HeadCheck.need parameters<W then
    .cons (.require (condition C ⟨HeadCheck.need parameters,fits⟩)) (SelectorRoutes.writeLabel C label)
  else .cons .revert .nil

theorem admitted (C : Contract) (parameters : List Solidity.AbiEntry.Param) (label : Fin W) :
    inFragP (Frag.init RouteCtx) (program C parameters label)=some (Frag.init RouteCtx) := by
  unfold program
  split
  · exact SelectorRoutes.write_core C label _
  · rfl

def compiled (C : Contract) (base : Nat) (parameters : List Solidity.AbiEntry.Param) (label : Fin W) :
    Compiler.Compilation base (Frag.init RouteCtx) (program C parameters label) :=
  .core (Frag.init RouteCtx) (admitted C parameters label)

theorem selected (C : Contract) (base : Nat) (parameters : List Solidity.AbiEntry.Param) (label : Fin W) :
    Compiler.compile base (Frag.init RouteCtx) (program C parameters label)=some (compiled C base parameters label) :=
  ValueGateBody.body_selected base _ _ _ (admitted C parameters label)

private theorem bounded_code (C : Contract) (base : Nat) (bound label : Fin W) :
    compileProg base (.cons (.require (condition C bound)) (SelectorRoutes.writeLabel C label))=
      [.mload (base+1),.push (.val bound),.gt,.iszero,.jumpi 1,.revert,.push (.val label),.mstore (base+1)] := by
  simp only [compileProg,compileStmt,condition,compileVal,compileSimple]
  rw [SelectorRoutes.write_code]
  have literal : wmod (toWord (bound.val : Int))=bound := by
    simp only [toWord,Int.natCast_nonneg,if_true,Int.toNat_natCast]
    exact Fin.ext (Nat.mod_eq_of_lt bound.isLt)
  rw [literal]
  rfl

private theorem bounded_run (base : Nat) (bound label size : Fin W) (machine : Machine)
    (initial : machine.mem (base+1)=.val size) :
    run [.mload (base+1),.push (.val bound),.gt,.iszero,.jumpi 1,.revert,.push (.val label),.mstore (base+1)] machine=
      if size.val<bound.val then .revert else .ok {machine with mem := upd machine.mem (base+1) (.val label)} 0 := by
  by_cases short : size.val<bound.val
  · simp only [run,exec_cons_zero,Instr.step,Machine.next,Out.bind,initial,short,decide_true,
      bword,if_true,if_false,Nat.one_ne_zero,decide_false,Bool.false_eq_true]
  · simp only [run,exec_cons_zero,exec_cons_succ,Instr.step,Machine.next,Out.bind,initial,short,
      decide_false,decide_true,bword,if_true,if_false,Nat.one_ne_zero,Bool.false_eq_true]
    rfl

theorem run_program (C : Contract) (base : Nat) (parameters : List Solidity.AbiEntry.Param) (label : Fin W)
    (machine : Machine) (size : Fin W) (initial : machine.mem (base+1)=.val size) :
    run (compileProg base (program C parameters label)) machine=headGateOutcome base parameters label size machine := by
  by_cases fits : HeadCheck.need parameters<W
  · simp only [program,dif_pos fits]
    rw [bounded_code,bounded_run base _ label size machine initial]
    rfl
  · have short : size.val<HeadCheck.need parameters :=
      Nat.lt_of_lt_of_le size.isLt (Nat.le_of_not_gt fits)
    simp only [program,dif_neg fits,headGateOutcome,if_pos short]
    rfl

theorem executed (C : Contract) (base : Nat) (parameters : List Solidity.AbiEntry.Param) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C parameters label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C parameters label)=some result)
    (machine : Machine) (size : Fin W) (initial : machine.mem (base+1)=.val size) :
    run result.code machine=headGateOutcome base parameters label size machine := by
  have same : result=compiled C base parameters label := Option.some.inj (found.symm.trans (selected C base parameters label))
  rw [same]
  exact run_program C base parameters label machine size initial

theorem rejected_iff (C : Contract) (base : Nat) (parameters : List Solidity.AbiEntry.Param) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C parameters label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C parameters label)=some result)
    (machine : Machine) (size : Fin W) (initial : machine.mem (base+1)=.val size) :
    (run result.code machine=.revert ↔ size.val<HeadCheck.need parameters) := by
  rw [executed C base parameters label result found machine size initial]
  by_cases short : size.val<HeadCheck.need parameters
  · simp only [headGateOutcome,if_pos short]
    exact ⟨fun _ => short,fun _ => True.intro⟩
  · simp only [headGateOutcome,if_neg short]
    constructor
    · intro impossible; cases impossible
    · intro impossible; exact False.elim (short impossible)

theorem semantic_rejection (C : Contract) (base : Nat) (parameters : List Solidity.AbiEntry.Param) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C parameters label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C parameters label)=some result)
    (machine : Machine) (size : Fin W) (initial : machine.mem (base+1)=.val size)
    (input : Solidity.AbiEntry.Input) (represented : size.val=input.size) (fuel : Nat)
    (rejected : run result.code machine=.revert) :
    Solidity.AbiEntry.entry input fuel parameters=.error .revert := by
  have short := (rejected_iff C base parameters label result found machine size initial).mp rejected
  rw [represented] at short
  exact HeadCheck.early_revert input fuel parameters short

def certificate : Interface.HeadGateCertificate program where
  selected := fun C base parameters label => ⟨compiled C base parameters label,selected C base parameters label⟩
  executed := executed
/-- info: 'Solidity.Backend.AbiEntry.HeadGate.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.HeadGate.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.HeadGate.run_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_program
/-- info: 'Solidity.Backend.AbiEntry.HeadGate.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.HeadGate.rejected_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejected_iff
/-- info: 'Solidity.Backend.AbiEntry.HeadGate.semantic_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms semantic_rejection
/-- info: 'Solidity.Backend.AbiEntry.HeadGate.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.HeadGate
