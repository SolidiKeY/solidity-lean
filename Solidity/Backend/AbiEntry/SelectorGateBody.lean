import Solidity.Backend.AbiEntry.SelectorGateBodyInterface
import Solidity.Backend.AbiEntry.SourceRoutes

/-! A selector-local prefix in the existing typed compiler. Passing it leaves
all machine state and the saved stack unchanged before the actual body. No
short-routing, Source table authenticity or native loading is inferred. -/
namespace Solidity.Backend.AbiEntry.SelectorGateBody
open Solidity.Evm
variable {C : Contract} {Γ Δ : Ctx}

def condition (index : Idx Γ (.val .uint)) (tag : Fin W) : Val C Γ .bool :=
  .binop .eqB rfl rfl (.simple (.local index))
    (.simple (.lit (tag.val : Int) (PrimTy.inRange_uint_of_lt tag.isLt)))

def program (index : Idx Γ (.val .uint)) (tag : Fin W) (body : Prog C Γ Δ) : Prog C Γ Δ :=
  .cons (.require (condition index tag)) body

theorem admitted (frag : Frag Γ) (index : Idx Γ (.val .uint)) (tag : Fin W)
    (body : Prog C Γ Δ) (outFrag : Frag Δ) (bodyCore : inFragP frag body=some outFrag) :
    inFragP frag (program index tag body)=some outFrag := bodyCore

def selectedWhole (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint)) (tag : Fin W)
    (body : Prog C Γ Δ) (outFrag : Frag Δ) (bodyCore : inFragP frag body=some outFrag) :
    Compiler.Compilation base frag (program index tag body) :=
  .core outFrag (admitted frag index tag body outFrag bodyCore)

def selectedBody (base : Nat) (frag : Frag Γ) (body : Prog C Γ Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP frag body=some outFrag) :
    Compiler.Compilation base frag body := ValueGateBody.selectedBody base frag body outFrag bodyCore

theorem whole_selected (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint)) (tag : Fin W)
    (body : Prog C Γ Δ) (outFrag : Frag Δ) (bodyCore : inFragP frag body=some outFrag) :
    Compiler.compile base frag (program index tag body)=
      some (selectedWhole base frag index tag body outFrag bodyCore) :=
  ValueGateBody.body_selected base frag _ outFrag (admitted frag index tag body outFrag bodyCore)

theorem body_selected (base : Nat) (frag : Frag Γ) (body : Prog C Γ Δ)
    (outFrag : Frag Δ) (bodyCore : inFragP frag body=some outFrag) :
    Compiler.compile base frag body=some (selectedBody base frag body outFrag bodyCore) :=
  ValueGateBody.body_selected base frag body outFrag bodyCore

/-- Reuse the existing selector comparison compilation at the chosen cell. -/
theorem condition_code (base : Nat) (index : Idx Γ (.val .uint)) (tag : Fin W) :
    compileVal base (condition (C := C) index tag)=[.mload (cellOf base index),.push (.val tag),.eq] :=
  SelectorRoutes.condition_code C (cellOf base index) tag

theorem code (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint)) (tag : Fin W)
    (body : Prog C Γ Δ) (outFrag : Frag Δ) (bodyCore : inFragP frag body=some outFrag) :
    (selectedWhole base frag index tag body outFrag bodyCore).code=
      [.mload (cellOf base index),.push (.val tag),.eq,.jumpi 1,.revert]++
        (selectedBody base frag body outFrag bodyCore).code := by
  change (compileVal base (condition index tag)++[.jumpi 1,.revert])++compileProg base body=_
  rw [condition_code]
  rfl

theorem run_code (address : Nat) (tag selector : Fin W) (machine : Machine)
    (initial : machine.mem address=.val selector) :
    run [.mload address,.push (.val tag),.eq,.jumpi 1,.revert] machine=
      if tag.val=selector.val then .ok machine 0 else .revert := by
  by_cases same : tag.val=selector.val
  · simp only [run,exec,Instr.step,Machine.next,Out.bind,initial,same,decide_true,bword,
      ite_true,ite_false,Nat.one_ne_zero]
  · simp only [run,exec,Instr.step,Machine.next,Out.bind,initial,same,decide_false,bword,
      Bool.false_eq_true,ite_false,ite_true]

theorem executed (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint)) (tag : Fin W)
    (body : Prog C Γ Δ) (outFrag : Frag Δ) (bodyCore : inFragP frag body=some outFrag)
    (whole : Compiler.Compilation base frag (program index tag body))
    (back : Compiler.Compilation base frag body)
    (wholeFound : Compiler.compile base frag (program index tag body)=some whole)
    (bodyFound : Compiler.compile base frag body=some back)
    (machine : Machine) (selector : Fin W) (initial : machine.mem (cellOf base index)=.val selector) :
    run whole.code machine=if tag.val=selector.val then run back.code machine else .revert := by
  have sameWhole : whole=selectedWhole base frag index tag body outFrag bodyCore :=
    Option.some.inj (wholeFound.symm.trans (whole_selected base frag index tag body outFrag bodyCore))
  have sameBody : back=selectedBody base frag body outFrag bodyCore :=
    Option.some.inj (bodyFound.symm.trans (body_selected base frag body outFrag bodyCore))
  rw [sameWhole,sameBody,code]
  have guardRun : run [.mload (cellOf base index),.push (.val tag),.eq,.jumpi 1,.revert] machine=
      if tag.val=selector.val then .ok machine 0 else .revert := run_code _ tag selector machine initial
  by_cases same : tag.val=selector.val
  · rw [ite_eq_left same] at guardRun ⊢
    exact run_append_ok guardRun
  · rw [ite_eq_right same] at guardRun ⊢
    exact run_append_revert guardRun

theorem miss_before_body (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint)) (tag : Fin W)
    (body : Prog C Γ Δ) (outFrag : Frag Δ) (bodyCore : inFragP frag body=some outFrag)
    (machine : Machine) (selector : Fin W) (initial : machine.mem (cellOf base index)=.val selector)
    (miss : tag.val≠selector.val) :
    run (selectedWhole base frag index tag body outFrag bodyCore).code machine=.revert := by
  rw [executed base frag index tag body outFrag bodyCore _ _
    (whole_selected base frag index tag body outFrag bodyCore) (body_selected base frag body outFrag bodyCore)
    machine selector initial,ite_eq_right miss]

/-- Reuse the published Source selector predicate; body/signature association remains separate. -/
theorem source_executed {E : Source.Env} (global : Source.Glob E) (signature : List Char)
    (frame : Source.Fr) (full : 4≤frame.cd.length)
    (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint))
    (body : Prog C Γ Δ) (outFrag : Frag Δ) (bodyCore : inFragP frag body=some outFrag)
    (whole : Compiler.Compilation base frag (program index (SourceRoutes.selectorWord global signature) body))
    (back : Compiler.Compilation base frag body)
    (wholeFound : Compiler.compile base frag (program index (SourceRoutes.selectorWord global signature) body)=some whole)
    (bodyFound : Compiler.compile base frag body=some back) (machine : Machine)
    (initial : machine.mem (cellOf base index)=.val (Interface.rawSelectorWord frame)) :
    run whole.code machine=if global.selector signature==frame.cd.take 4 then run back.code machine else .revert := by
  have predicate : decide ((SourceRoutes.selectorWord global signature).val=(Interface.rawSelectorWord frame).val)=
      (global.selector signature==frame.cd.take 4) := SourceRoutes.predicate global signature frame full
  simpa only [←predicate,decide_eq_true_eq] using executed base frag index (SourceRoutes.selectorWord global signature)
    body outFrag bodyCore whole back wholeFound bodyFound machine (Interface.rawSelectorWord frame) initial

def certificate : Interface.SelectorGateBodyCertificate program where
  selected := fun base frag index tag body outFrag bodyCore =>
    ⟨selectedWhole base frag index tag body outFrag bodyCore,selectedBody base frag body outFrag bodyCore,
      whole_selected base frag index tag body outFrag bodyCore,body_selected base frag body outFrag bodyCore⟩
  executed := executed

/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBody.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBody.whole_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whole_selected
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBody.body_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_selected
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBody.condition_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms condition_code
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBody.code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms code
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBody.run_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_code
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBody.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBody.miss_before_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms miss_before_body
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBody.source_executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_executed
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBody.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.SelectorGateBody
