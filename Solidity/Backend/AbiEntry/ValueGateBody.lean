import Solidity.Backend.AbiEntry.ValueGateBodyInterface
import Solidity.Backend.AbiEntry.ValueGate

/-! Typed prefix construction through the existing public compiler. The actual
core classifier defines this supported family; global Source/profile admission
is not inferred. Body execution is not supplied as a premise. -/
namespace Solidity.Backend.AbiEntry.ValueGateBody
open Solidity.Evm
variable {C : Contract} {Γ Δ : Ctx}

def guard (payable : Bool) (body : Prog C Γ Δ) : Prog C Γ Δ :=
  if payable then body else .cons (.require ValueGate.condition) body

theorem admitted (frag : Frag Γ) (body : Prog C Γ Δ) (payable : Bool)
    (outFrag : Frag Δ) (bodyCore : inFragP frag body=some outFrag) :
    inFragP frag (guard payable body)=some outFrag := by
  cases payable <;> exact bodyCore

def selectedBody (base : Nat) (frag : Frag Γ) (body : Prog C Γ Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP frag body=some outFrag) :
    Compiler.Compilation base frag body := .core outFrag bodyCore

def selectedWhole (base : Nat) (frag : Frag Γ) (body : Prog C Γ Δ) (payable : Bool)
    (outFrag : Frag Δ) (bodyCore : inFragP frag body=some outFrag) :
    Compiler.Compilation base frag (guard payable body) :=
  .core outFrag (admitted frag body payable outFrag bodyCore)

theorem body_selected (base : Nat) (frag : Frag Γ) (body : Prog C Γ Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP frag body=some outFrag) :
    Compiler.compile base frag body=some (selectedBody base frag body outFrag bodyCore) := by
  unfold Compiler.compile
  split
  · rename_i actual found
    have same : actual=outFrag := Option.some.inj (found.symm.trans bodyCore)
    subst actual
    rfl
  · rename_i found
    rw [bodyCore] at found
    cases found

theorem whole_selected (base : Nat) (frag : Frag Γ) (body : Prog C Γ Δ) (payable : Bool)
    (outFrag : Frag Δ) (bodyCore : inFragP frag body=some outFrag) :
    Compiler.compile base frag (guard payable body)=
      some (selectedWhole base frag body payable outFrag bodyCore) := by
  exact body_selected base frag (guard payable body) outFrag (admitted frag body payable outFrag bodyCore)

theorem code (base : Nat) (frag : Frag Γ) (body : Prog C Γ Δ) (payable : Bool)
    (outFrag : Frag Δ) (bodyCore : inFragP frag body=some outFrag) :
    (selectedWhole base frag body payable outFrag bodyCore).code=
      (if payable then [] else [.callvalue,.push (.val (wmod 0)),.eq,.jumpi 1,.revert])++
        (selectedBody base frag body outFrag bodyCore).code := by
  cases payable <;> rfl

theorem composed (payable : Bool) (bodyCode : List Evm.Instr) (machine : Machine) :
    run ((if payable then [] else [.callvalue,.push (.val (wmod 0)),.eq,.jumpi 1,.revert])++bodyCode) machine=
      if payable || decide (machine.callvalue.val=0) then run bodyCode machine else .revert := by
  have gate := ValueGate.run_code payable machine
  by_cases allowed : (payable || decide (machine.callvalue.val=0))=true
  · rw [if_pos allowed] at gate ⊢
    exact run_append_ok gate
  · rw [if_neg allowed] at gate ⊢
    exact run_append_revert gate

theorem executed (base : Nat) (frag : Frag Γ) (body : Prog C Γ Δ) (payable : Bool)
    (outFrag : Frag Δ) (bodyCore : inFragP frag body=some outFrag)
    (whole : Compiler.Compilation base frag (guard payable body))
    (back : Compiler.Compilation base frag body)
    (frontFound : Compiler.compile base frag (guard payable body)=some whole)
    (backFound : Compiler.compile base frag body=some back) (machine : Machine) :
    run whole.code machine=if payable || decide (machine.callvalue.val=0)
      then run back.code machine else .revert := by
  have frontSame : whole=selectedWhole base frag body payable outFrag bodyCore :=
    Option.some.inj (frontFound.symm.trans (whole_selected base frag body payable outFrag bodyCore))
  have backSame : back=selectedBody base frag body outFrag bodyCore :=
    Option.some.inj (backFound.symm.trans (body_selected base frag body outFrag bodyCore))
  rw [frontSame,backSame,code]
  exact composed payable _ machine

def certificate : Interface.ValueGateBodyCertificate guard where
  selected := fun base frag body payable outFrag bodyCore =>
    ⟨selectedWhole base frag body payable outFrag bodyCore,selectedBody base frag body outFrag bodyCore,
      whole_selected base frag body payable outFrag bodyCore,body_selected base frag body outFrag bodyCore,
      code base frag body payable outFrag bodyCore⟩
  executed := executed

/-- info: 'Solidity.Backend.AbiEntry.ValueGateBody.body_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_selected
/-- info: 'Solidity.Backend.AbiEntry.ValueGateBody.whole_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whole_selected
/-- info: 'Solidity.Backend.AbiEntry.ValueGateBody.composed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composed
/-- info: 'Solidity.Backend.AbiEntry.ValueGateBody.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.ValueGateBody.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate

end Solidity.Backend.AbiEntry.ValueGateBody
