import Solidity.Backend.AbiEntry.ValueGateInterface

/-! A typed value-gate family selected by the existing public compiler.
This intrinsic target observation does not supply Source entry or byte-level
revert adequacy. No replacement compiler or interpreter is introduced. -/
namespace Solidity.Backend.AbiEntry.ValueGate
open Solidity.Evm

variable {C : Contract} {Γ : Ctx}

def condition : Val C Γ .bool :=
  .binop .eqB (by decide) rfl (.simple (.env .msgValue rfl)) (.simple (.lit 0 (by decide)))

def program : Bool → Prog C Γ Γ
  | true => .nil
  | false => .cons (.require condition) .nil

def compiled (base : Nat) (frag : Frag Γ) (payable : Bool) :
    Compiler.Compilation base frag (program (C := C) payable) :=
  .core frag (by cases payable <;> rfl)

theorem selected (base : Nat) (frag : Frag Γ) (payable : Bool) :
    Compiler.compile base frag (program (C := C) payable)=some (compiled base frag payable) := by
  cases payable <;> rfl

theorem code (base : Nat) (frag : Frag Γ) (payable : Bool) :
    (compiled (C := C) base frag payable).code=if payable then [] else
      [.callvalue,.push (.val (wmod 0)),.eq,.jumpi 1,.revert] := by
  cases payable <;> rfl

theorem run_code (payable : Bool) (machine : Machine) :
    run (if payable then [] else [.callvalue,.push (.val (wmod 0)),.eq,.jumpi 1,.revert]) machine=
      if payable || decide (machine.callvalue.val=0) then .ok machine 0 else .revert := by
  cases payable with
  | true => rfl
  | false =>
    by_cases zero : machine.callvalue.val=0
    · simp only [run,exec,Instr.step,Machine.next,Out.bind,wmod,bword,zero,
        Bool.false_eq_true,if_false,if_true,Bool.false_or,decide_true,Nat.zero_mod,eq_comm]
      rfl
    · simp only [run,exec,Instr.step,Machine.next,Out.bind,wmod,bword,zero,
        Bool.false_eq_true,if_false,if_true,Bool.false_or,decide_false,Nat.zero_mod,eq_comm]

theorem executed (base : Nat) (frag : Frag Γ) (payable : Bool)
    (result : Compiler.Compilation base frag (program (C := C) payable))
    (found : Compiler.compile base frag (program payable)=some result) (machine : Machine) :
    run result.code machine=
      if payable || decide (machine.callvalue.val=0) then .ok machine 0 else .revert := by
  have same : result=compiled base frag payable :=
    Option.some.inj (found.symm.trans (selected base frag payable))
  rw [same,code]
  exact run_code payable machine

def certificate : Interface.ValueGateCertificate program where
  selected := fun base frag payable => ⟨compiled base frag payable,selected base frag payable,code base frag payable⟩
  executed := executed

/-- info: 'Solidity.Backend.AbiEntry.ValueGate.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.ValueGate.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.ValueGate.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate

end Solidity.Backend.AbiEntry.ValueGate
