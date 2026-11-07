import Solidity.Backend.AbiEntry.ValueGateBody

/-! Actual checked context-growing body selection and a nontrivial word-memory
write, with two saved stack words. Raw fault/skip controls exercise only the
arbitrary-suffix helper, not the typed-body classifier. -/
namespace Solidity.Backend.AbiEntry.ValueGateBodyControls
open Solidity.Evm
private def C : Contract := {vars := []}
private def Γ : Ctx := [.val .uint]
private def Δ : Ctx := .val .uint::Γ
private def F : Frag Γ := Frag.init Γ
private def G : Frag Δ := Frag.init Δ
private def body : Prog C Γ Δ :=
  .cons (.declLocal .uint (.user "fresh") (some (.simple (.lit 9 (by decide))))) .nil
private theorem bodyCore : inFragP F body=some G := by rfl
private def back : Compiler.Compilation 7 F body :=
  ValueGateBody.selectedBody 7 F body G bodyCore
private def whole (payable : Bool) : Compiler.Compilation 7 F (ValueGateBody.guard payable body) :=
  ValueGateBody.selectedWhole 7 F body payable G bodyCore
private def machine (value : Fin W) : Machine :=
  {Machine.init with
    callvalue := value
    stack := [.val (wmod 258),.val (wmod 513)]
    mem := fun _ => .val (wmod 71)}
private def written (initial : Machine) : Machine :=
  {initial with mem := upd initial.mem 8 (.val (wmod 9))}

theorem selected (payable : Bool) :
    Compiler.compile 7 F (ValueGateBody.guard payable body)=some (whole payable) ∧
    Compiler.compile 7 F body=some back :=
  ⟨ValueGateBody.whole_selected _ _ _ _ _ _,ValueGateBody.body_selected _ _ _ _ _⟩

theorem body_changes (value : Fin W) :
    run back.code (machine value)=.ok (written (machine value)) 0 := by rfl

theorem zero_body : run (whole false).code (machine (wmod 0))=
    .ok (written (machine (wmod 0))) 0 := by
  have actual := ValueGateBody.executed 7 F body false G bodyCore
    (whole false) back (selected false).1 (selected false).2 (machine (wmod 0))
  exact actual.trans (body_changes _)

theorem payable_body (value : Fin W) :
    run (whole true).code (machine value)=.ok (written (machine value)) 0 := by
  have actual := ValueGateBody.executed 7 F body true G bodyCore
    (whole true) back (selected true).1 (selected true).2 (machine value)
  exact actual.trans (body_changes _)

theorem nonzero_blocks (value : Fin W) (nonzero : value.val≠0) :
    run (whole false).code (machine value)=.revert := by
  have actual := ValueGateBody.executed 7 F body false G bodyCore
    (whole false) back (selected false).1 (selected false).2 (machine value)
  change run (whole false).code (machine value)=
    (if false || decide (value.val=0) then run back.code (machine value) else .revert) at actual
  simpa only [Bool.false_or,decide_eq_false nonzero,Bool.false_eq_true,if_false] using actual

theorem mutation_not_noop (value : Fin W) : written (machine value)≠machine value := by
  intro same
  have wrong : Word.val (wmod 9)=Word.val (wmod 71) :=
    congrArg (fun m => m.mem 8) same
  exact (by decide : Word.val (wmod 9)≠Word.val (wmod 71)) wrong

theorem protected_and_saved (value : Fin W) :
    (written (machine value)).mem 7=(machine value).mem 7 ∧
    (written (machine value)).stack=(machine value).stack := by exact ⟨rfl,rfl⟩

theorem raw_fault_preserved :
    run ((if true then [] else [.callvalue,.push (.val (wmod 0)),.eq,.jumpi 1,.revert])++
      [.pop,.pop,.pop]) (machine (wmod 1))=.fault :=
  ValueGateBody.composed true _ _

theorem raw_skip_preserved :
    run ((if false then [] else [.callvalue,.push (.val (wmod 0)),.eq,.jumpi 1,.revert])++
      [.jump 3]) (machine (wmod 0))=.ok (machine (wmod 0)) 3 :=
  ValueGateBody.composed false _ _

/-- info: 'Solidity.Backend.AbiEntry.ValueGateBodyControls.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.ValueGateBodyControls.body_changes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_changes
/-- info: 'Solidity.Backend.AbiEntry.ValueGateBodyControls.zero_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_body
/-- info: 'Solidity.Backend.AbiEntry.ValueGateBodyControls.payable_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms payable_body
/-- info: 'Solidity.Backend.AbiEntry.ValueGateBodyControls.nonzero_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonzero_blocks
/-- info: 'Solidity.Backend.AbiEntry.ValueGateBodyControls.mutation_not_noop' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms mutation_not_noop
/-- info: 'Solidity.Backend.AbiEntry.ValueGateBodyControls.protected_and_saved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
/-- info: 'Solidity.Backend.AbiEntry.ValueGateBodyControls.raw_fault_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_fault_preserved
/-- info: 'Solidity.Backend.AbiEntry.ValueGateBodyControls.raw_skip_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_skip_preserved
end Solidity.Backend.AbiEntry.ValueGateBodyControls
