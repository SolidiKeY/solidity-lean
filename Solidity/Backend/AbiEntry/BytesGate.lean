import Solidity.Backend.AbiEntry.BytesGateInterface

/-! Validate low padding bits with the existing intrinsic bitwise compiler.
No input cleanup or restriction of the existing semantic size is introduced. -/
namespace Solidity.Backend.AbiEntry.BytesGate
open Solidity.Evm
open Interface (RouteCtx bytesGateOutcome)

def mask (size : Nat) : Nat := 2^(256-8*size)-1
private theorem mask_lt (size : Nat) : mask size<W := by
  have power : 2^(256-8*size)≤W := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have positive : 0<2^(256-8*size) := Nat.two_pow_pos _
  exact Nat.lt_of_lt_of_le (Nat.sub_lt positive (by decide : 0<1)) power
def maskWord (size : Nat) : Fin W := ⟨mask size,mask_lt size⟩
def condition (C : Contract) (size : Nat) : Val C RouteCtx .bool :=
  .binop .eqB (by decide) rfl
    (.binop .band rfl rfl (.simple (.local (.there .here)))
      (.simple (.lit ((maskWord size).val : Int) (PrimTy.inRange_uint_of_lt (maskWord size).isLt))))
    (.simple (.lit 0 rfl))
def program (C : Contract) (size : Nat) (label : Fin W) : Prog C RouteCtx RouteCtx :=
  .cons (.require (condition C size)) (SelectorRoutes.writeLabel C label)

theorem admitted (C : Contract) (size : Nat) (label : Fin W) :
    inFragP (Frag.init RouteCtx) (program C size label)=some (Frag.init RouteCtx) := rfl

def compiled (C : Contract) (base size : Nat) (label : Fin W) :
    Compiler.Compilation base (Frag.init RouteCtx) (program C size label) :=
  .core (Frag.init RouteCtx) (admitted C size label)
theorem selected (C : Contract) (base size : Nat) (label : Fin W) :
    Compiler.compile base (Frag.init RouteCtx) (program C size label)=some (compiled C base size label) :=
  ValueGateBody.body_selected base _ _ _ (admitted C size label)

private theorem code (C : Contract) (base size : Nat) (label : Fin W) :
    compileProg base (program C size label)=
      [.mload base,.push (.val (maskWord size)),.and,.push (.val (wmod 0)),.eq,.jumpi 1,.revert,
        .push (.val label),.mstore (base+1)] := by
  simp only [program,compileProg,compileStmt,condition,compileVal,compileSimple]
  rw [SelectorRoutes.write_code]
  have literal : wmod (toWord ((maskWord size).val : Int))=maskWord size := by
    simp only [toWord,Int.natCast_nonneg,if_true,Int.toNat_natCast]
    exact Fin.ext (Nat.mod_eq_of_lt (maskWord size).isLt)
  rw [literal]
  rfl

private theorem run_code (base size : Nat) (label word : Fin W) (machine : Machine)
    (initial : machine.mem base=.val word) :
    run [.mload base,.push (.val (maskWord size)),.and,.push (.val (wmod 0)),.eq,.jumpi 1,.revert,
      .push (.val label),.mstore (base+1)] machine=bytesGateOutcome base size label word machine := by
  have masked : (maskWord size).val &&& word.val=word.val%2^(256-8*size) := by
    change mask size &&& word.val=_
    rw [Nat.and_comm]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have semantic : (Solidity.AbiEntry.Kind.fixedBytes size).valid word.val=
      decide ((maskWord size).val &&& word.val=0) := by
    rw [masked]
    apply Bool.eq_iff_iff.mpr
    simp only [Solidity.AbiEntry.Kind.valid,beq_iff_eq,decide_eq_true_eq]
  rw [bytesGateOutcome,semantic]
  by_cases clean : (maskWord size).val &&& word.val=0
  · simp only [run,exec_cons_zero,Instr.step,Machine.next,Out.bind,initial,wmod,Nat.zero_mod,
      clean,decide_true,bword,if_true,Nat.one_ne_zero]
    rfl
  · simp only [run,exec_cons_zero,Instr.step,Machine.next,Out.bind,initial,wmod,Nat.zero_mod,
      clean,decide_eq_false (Ne.symm clean),decide_false,bword,Bool.false_eq_true,if_false,if_true]

theorem run_program (C : Contract) (base size : Nat) (label : Fin W) (machine : Machine)
    (word : Fin W) (initial : machine.mem base=.val word) :
    run (compileProg base (program C size label)) machine=bytesGateOutcome base size label word machine := by
  rw [code]
  exact run_code base size label word machine initial

theorem executed (C : Contract) (base size : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C size label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C size label)=some result)
    (machine : Machine) (word : Fin W) (initial : machine.mem base=.val word) :
    run result.code machine=bytesGateOutcome base size label word machine := by
  have same : result=compiled C base size label := Option.some.inj (found.symm.trans (selected C base size label))
  rw [same]
  exact run_program C base size label machine word initial

def certificate : Interface.BytesGateCertificate program where
  selected := fun C base size label => ⟨compiled C base size label,selected C base size label⟩
  executed := executed
/-- info: 'Solidity.Backend.AbiEntry.BytesGate.admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.BytesGate.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.BytesGate.run_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_program
/-- info: 'Solidity.Backend.AbiEntry.BytesGate.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.BytesGate.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.BytesGate
